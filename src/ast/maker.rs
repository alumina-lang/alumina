use std::collections::HashMap;

use crate::{
    ast::{AstCtx, AstId, BuiltinType, Field, Function, Item, ItemP, Parameter, Struct, Ty},
    common::{AluminaError, ArenaAllocatable, CodeErrorKind, WithSpanDuringParsing},
    diagnostics::DiagnosticContext,
    intrinsics::intrinsic_kind,
    name_resolution::scope::{NamedItem, Scope},
    parser::{AluminaVisitor, ParseCtx},
};

use super::{
    expressions::ExpressionVisitor,
    lang::{lang_item_kind, LangItemKind, LangItemMap},
    macros::MacroMaker,
    types::TypeVisitor,
    AssociatedFn, Attribute, Enum, EnumMember, Intrinsic, Span, Static,
};

pub struct AstItemMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    diag_ctx: DiagnosticContext,
    symbols: Vec<ItemP<'ast>>,

    lang_items: HashMap<LangItemKind, ItemP<'ast>>,
}

impl<'ast> AstItemMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, diag_ctx: DiagnosticContext) -> Self {
        Self {
            ast,
            diag_ctx,
            symbols: Vec::new(),
            lang_items: HashMap::new(),
        }
    }

    pub fn into_inner(self) -> (Vec<ItemP<'ast>>, LangItemMap<'ast>) {
        (self.symbols, LangItemMap::new(self.lang_items))
    }

    fn get_attributes<'src>(
        &mut self,
        item: ItemP<'ast>,
        code: &'src ParseCtx<'src>,
        node: tree_sitter::Node<'src>,
    ) -> Result<&'ast [Attribute], AluminaError> {
        let attribute_node = match node.child_by_field_name("attributes") {
            Some(node) => node,
            None => return Ok([].alloc_on(self.ast)),
        };

        let mut cursor = attribute_node.walk();
        let result = attribute_node
            .children(&mut cursor)
            .map(|n| code.node_text(n.child_by_field_name("name").unwrap()))
            .filter_map(|s| match lang_item_kind(s) {
                Some(kind) => {
                    // We allow lang items to be overriden.
                    self.lang_items.insert(kind, item);
                    None
                }
                None => Some(s),
            })
            .filter_map(|name| match name {
                "export" => Some(Attribute::Export),
                "force_inline" => Some(Attribute::ForceInline),
                _ => None,
            })
            .collect::<Vec<_>>()
            .alloc_on(self.ast);

        Ok(result)
    }

    fn resolve_associated_fns<'src>(
        &self,
        scope: Scope<'ast, 'src>,
    ) -> Result<&'ast [AssociatedFn<'ast>], AluminaError> {
        let mut associated_fns = Vec::new();

        for (name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Function(symbol, _, _) => associated_fns.push(AssociatedFn {
                    name: name,
                    item: *symbol,
                }),
                _ => {}
            }
        }

        let result = associated_fns.alloc_on(self.ast);
        Ok(result)
    }

    fn make_struct<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), AluminaError> {
        let mut placeholders: Vec<AstId> = Vec::new();
        let mut fields: Vec<Field<'ast>> = Vec::new();

        for (name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Placeholder(placeholder) => {
                    placeholders.push(*placeholder);
                }
                NamedItem::Field(node) => {
                    let mut visitor = TypeVisitor::new(self.ast, scope.clone());
                    let field_type = visitor.visit(node.child_by_field_name("type").unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: scope.code().unwrap().file_id(),
                    };

                    fields.push(Field {
                        id: self.ast.make_id(),
                        name: name,
                        typ: field_type,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let associated_fns = match impl_scope {
            Some(impl_scope) => self.resolve_associated_fns(impl_scope)?,
            None => (&[]).alloc_on(self.ast),
        };

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::Struct(Struct {
            name: Some(name),
            placeholders: placeholders.alloc_on(self.ast),
            fields: fields.alloc_on(self.ast),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            associated_fns,
            span: Some(span),
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_enum<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), AluminaError> {
        let mut members = Vec::new();

        for (name, item) in scope.inner().all_items() {
            match item {
                NamedItem::EnumMember(_, id, node) => {
                    let expr = node
                        .child_by_field_name("value")
                        .map(|node| {
                            ExpressionVisitor::new(self.ast, self.diag_ctx.clone(), scope.clone())
                                .generate(node)
                        })
                        .transpose()?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: scope.code().unwrap().file_id(),
                    };

                    members.push(EnumMember {
                        name: Some(name),
                        id: *id,
                        value: expr,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let associated_fns = match impl_scope {
            Some(impl_scope) => self.resolve_associated_fns(impl_scope)?,
            None => (&[]).alloc_on(self.ast),
        };

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::Enum(Enum {
            name: Some(name),
            members: members.alloc_on(self.ast),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            associated_fns,
            span: Some(span),
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_function_regular<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        body: Option<tree_sitter::Node<'src>>,
    ) -> Result<(), AluminaError> {
        let mut placeholders: Vec<AstId> = Vec::new();
        let mut parameters: Vec<Parameter<'ast>> = Vec::new();

        for (_name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Placeholder(placeholder) => {
                    placeholders.push(*placeholder);
                }
                NamedItem::Parameter(id, node) => {
                    let field_type = TypeVisitor::new(self.ast, scope.clone())
                        .visit(node.child_by_field_name("type").unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: scope.code().unwrap().file_id(),
                    };

                    parameters.push(Parameter {
                        id: *id,
                        typ: field_type,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let return_type = node
            .child_by_field_name("return_type")
            .map(|n| TypeVisitor::new(self.ast, scope.clone()).visit(n))
            .transpose()?
            .unwrap_or(self.ast.intern_type(Ty::Builtin(BuiltinType::Void)));

        let function_body = body
            .map(|body| {
                ExpressionVisitor::new(self.ast, self.diag_ctx.clone(), scope.clone())
                    .generate(body)
            })
            .transpose()?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::Function(Function {
            name: Some(name),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            placeholders: placeholders.alloc_on(self.ast),
            args: parameters.alloc_on(self.ast),
            return_type,
            body: function_body,
            span: Some(span),
            closure: false,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_static<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
    ) -> Result<(), AluminaError> {
        let typ = node
            .child_by_field_name("type")
            .map(|n| TypeVisitor::new(self.ast, scope.clone()).visit(n))
            .transpose()?;

        let init = node
            .child_by_field_name("init")
            .map(|body| {
                ExpressionVisitor::new(self.ast, self.diag_ctx.clone(), scope.clone())
                    .generate(body)
            })
            .transpose()?;

        if typ.is_none() && init.is_none() {
            return Err(CodeErrorKind::TypeHintRequired).with_span(&scope, node);
        }

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::Static(Static {
            name: Some(name),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            typ,
            init,
            span: Some(span),
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_function_extern<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
    ) -> Result<(), AluminaError> {
        let code = scope.code().unwrap();

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: code.file_id(),
        };

        let abi = code.node_text(node.child_by_field_name("abi").unwrap());

        match abi {
            "\"C\"" => {
                let mut parameters = Vec::new();
                for (_name, item) in scope.inner().all_items() {
                    match item {
                        NamedItem::Placeholder(_) => {
                            return Err(CodeErrorKind::ExternCGenericParams)
                                .with_span(&scope, node);
                        }
                        NamedItem::Parameter(id, node) => {
                            let field_type = TypeVisitor::new(self.ast, scope.clone())
                                .visit(node.child_by_field_name("type").unwrap())?;

                            let span = Span {
                                start: node.start_byte(),
                                end: node.end_byte(),
                                file: scope.code().unwrap().file_id(),
                            };

                            parameters.push(Parameter {
                                id: *id,
                                typ: field_type,
                                span: Some(span),
                            });
                        }
                        _ => {}
                    }
                }
                let return_type = node
                    .child_by_field_name("return_type")
                    .map(|n| TypeVisitor::new(self.ast, scope.clone()).visit(n))
                    .transpose()?
                    .unwrap_or(self.ast.intern_type(Ty::Builtin(BuiltinType::Void)));
                let result = Item::Function(Function {
                    name: Some(name),
                    attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
                    placeholders: [].alloc_on(self.ast),
                    args: parameters.alloc_on(self.ast),
                    return_type,
                    body: None,
                    span: Some(span),
                    closure: false,
                });

                symbol.assign(result);
                self.symbols.push(symbol);
            }
            "\"intrinsic\"" => {
                let (generic_count, arg_count) =
                    scope
                        .inner()
                        .all_items()
                        .fold((0, 0), |(generic, args), item| match item.1 {
                            NamedItem::Placeholder(_) => (generic + 1, args),
                            NamedItem::Parameter(_, _) => (generic, args + 1),
                            _ => (generic, args),
                        });

                let result = Item::Intrinsic(Intrinsic {
                    kind: intrinsic_kind(name)
                        .ok_or(CodeErrorKind::UnknownIntrinsic(name.to_string()))
                        .with_span(&scope, node)?,
                    generic_count,
                    arg_count,
                    span: Some(span),
                });

                symbol.assign(result);
            }
            _ => {
                return Err(CodeErrorKind::UnsupportedABI(abi.to_string())).with_span(&scope, node)
            }
        }

        Ok(())
    }

    fn make_type<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), AluminaError> {
        match node.kind() {
            "struct_definition" => self.make_struct(name, symbol, node, scope, impl_scope)?,
            "enum_definition" => self.make_enum(name, symbol, node, scope, impl_scope)?,
            _ => unimplemented!(),
        };

        Ok(())
    }

    pub fn make<'src>(&mut self, scope: Scope<'ast, 'src>) -> Result<(), AluminaError> {
        for (name, item) in scope.inner().grouped_items() {
            match item {
                [NamedItem::Module(module)] => {
                    self.make(module.clone())?;
                }
                [NamedItem::Type(symbol, node, scope), NamedItem::Impl(impl_scope)] => {
                    self.make_type(
                        name,
                        *symbol,
                        *node,
                        scope.clone(),
                        Some(impl_scope.clone()),
                    )?;
                    self.make(impl_scope.clone())?;
                }
                [NamedItem::Type(symbol, node, scope)] => {
                    self.make_type(name, *symbol, *node, scope.clone(), None)?;
                }
                [NamedItem::Static(symbol, node)] => {
                    self.make_static(name, *symbol, *node, scope.clone())?;
                }
                [NamedItem::Macro(symbol, node, scope)] => {
                    let mut macro_maker = MacroMaker::new(self.ast, self.diag_ctx.clone());
                    macro_maker.make(name, *symbol, *node, scope.clone())?;
                    self.symbols.push(symbol);
                }
                [NamedItem::Function(symbol, node, scope)] => {
                    match node.kind() {
                        "function_definition" => self.make_function_regular(
                            name,
                            symbol,
                            *node,
                            scope.clone(),
                            Some(node.child_by_field_name("body").unwrap()),
                        )?,
                        "extern_function" => {
                            self.make_function_extern(name, symbol, *node, scope.clone())?
                        }
                        _ => unimplemented!(),
                    };
                }
                _ => {}
            }
        }

        Ok(())
    }
}
