use std::collections::HashMap;

use once_cell::unsync::OnceCell;

use crate::{
    ast::{AstCtx, BuiltinType, Field, Function, Item, ItemP, Parameter, StructLike, Ty},
    common::{AluminaError, ArenaAllocatable, CodeErrorKind, WithSpanDuringParsing},
    diagnostics::DiagnosticContext,
    intrinsics::intrinsic_kind,
    name_resolution::scope::{NamedItem, Scope, ScopeType},
    parser::{AluminaVisitor, ParseCtx},
};

use super::{
    expressions::ExpressionVisitor,
    lang::{lang_item_kind, LangItemKind, LangItemMap},
    macros::MacroMaker,
    types::TypeVisitor,
    AssociatedFn, Attribute, Enum, EnumMember, Intrinsic, Mixin, MixinCell, Placeholder, Protocol,
    Span, StaticOrConst,
};

pub struct AstItemMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    diag_ctx: DiagnosticContext,
    symbols: Vec<ItemP<'ast>>,

    lang_items: HashMap<LangItemKind, ItemP<'ast>>,
    ambient_placeholders: Vec<Placeholder<'ast>>,
}

impl<'ast> AstItemMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, diag_ctx: DiagnosticContext) -> Self {
        Self {
            ast,
            diag_ctx,
            symbols: Vec::new(),
            lang_items: HashMap::new(),
            ambient_placeholders: Vec::new(),
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
            .filter(|s| match lang_item_kind(s) {
                Some(kind) => {
                    // We allow lang items to be overriden.
                    self.lang_items.insert(kind, item);
                    false
                }
                None => true,
            })
            .filter_map(|name| match name {
                "export" => Some(Attribute::Export),
                "inline" => Some(Attribute::Inline),
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
                    name: name.unwrap(),
                    item: *symbol,
                }),
                _ => {}
            }
        }

        let result = associated_fns.alloc_on(self.ast);
        Ok(result)
    }

    fn resolve_mixins<'src>(
        &self,
        scope: Scope<'ast, 'src>,
    ) -> Result<&'ast [Mixin<'ast>], AluminaError> {
        let mut mixins = Vec::new();

        for (_name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Mixin(node, scope) => {
                    let mut placeholders = Vec::new();
                    for (_name, item) in scope.inner().all_items() {
                        match item {
                            NamedItem::Placeholder(id, node) => {
                                placeholders.push(Placeholder {
                                    id: *id,
                                    bounds: TypeVisitor::new(self.ast, scope.clone())
                                        .parse_protocol_bounds(*node)?,
                                });
                            }
                            _ => {}
                        }
                    }

                    let mut visitor = TypeVisitor::new(self.ast, scope.clone()).with_protocol();
                    let protocol_type =
                        visitor.visit(node.child_by_field_name("protocol").unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: scope.code().unwrap().file_id(),
                    };

                    mixins.push(Mixin {
                        placeholders: placeholders.alloc_on(self.ast),
                        protocol: protocol_type,
                        contents: self.ast.arena.alloc(MixinCell {
                            contents: OnceCell::new(),
                        }),
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let result = mixins.alloc_on(self.ast);
        Ok(result)
    }

    fn make_struct_like<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), AluminaError> {
        let mut placeholders = Vec::new();
        let mut fields: Vec<Field<'ast>> = Vec::new();

        let code = scope.code().unwrap();

        for (name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Placeholder(id, node) => {
                    placeholders.push(Placeholder {
                        id: *id,
                        bounds: TypeVisitor::new(self.ast, scope.clone())
                            .parse_protocol_bounds(*node)?,
                    });
                }
                NamedItem::Field(node) => {
                    let mut visitor = TypeVisitor::new(self.ast, scope.clone());
                    let field_type = visitor.visit(node.child_by_field_name("type").unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: code.file_id(),
                    };

                    fields.push(Field {
                        id: self.ast.make_id(),
                        name: name.unwrap(),
                        typ: field_type,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let is_union = match code.node_text(node.child_by_field_name("kind").unwrap()) {
            "struct" => false,
            "union" => true,
            _ => unimplemented!(),
        };

        let (associated_fns, mixins) = match impl_scope {
            Some(impl_scope) => (
                self.resolve_associated_fns(impl_scope.clone())?,
                self.resolve_mixins(impl_scope)?,
            ),
            None => ((&[]).alloc_on(self.ast), (&[]).alloc_on(self.ast)),
        };

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: code.file_id(),
        };

        let result = Item::StructLike(StructLike {
            name,
            placeholders: placeholders.alloc_on(self.ast),
            fields: fields.alloc_on(self.ast),
            attributes: self.get_attributes(symbol, code, node)?,
            associated_fns,
            mixins,
            span: Some(span),
            is_union,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_protocol<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
    ) -> Result<(), AluminaError> {
        let mut placeholders = Vec::new();
        let code = scope.code().unwrap();

        for (_name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Placeholder(id, node) => {
                    placeholders.push(Placeholder {
                        id: *id,
                        bounds: TypeVisitor::new(self.ast, scope.clone())
                            .parse_protocol_bounds(*node)?,
                    });
                }
                _ => {}
            }
        }

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: code.file_id(),
        };

        let associated_fns = self.resolve_associated_fns(scope)?;

        let result = Item::Protocol(Protocol {
            name,
            placeholders: placeholders.alloc_on(self.ast),
            associated_fns,
            attributes: self.get_attributes(symbol, code, node)?,
            span: Some(span),
        });

        symbol.assign(result);

        Ok(())
    }

    fn make_impl<'src>(&mut self, scope: Scope<'ast, 'src>) -> Result<(), AluminaError> {
        // Ambient placeholders on impl blocks
        for (_, item) in scope.inner().all_items() {
            match item {
                NamedItem::Placeholder(id, node) => {
                    self.ambient_placeholders.push(Placeholder {
                        id: *id,
                        bounds: TypeVisitor::new(self.ast, scope.clone())
                            .parse_protocol_bounds(*node)?,
                    });
                }
                _ => {}
            }
        }

        let res = self.make(scope);
        self.ambient_placeholders.clear();
        res
    }

    fn make_enum<'src>(
        &mut self,
        name: Option<&'ast str>,
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
                        name: name.unwrap(),
                        id: *id,
                        value: expr,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let (associated_fns, mixins) = match impl_scope {
            Some(impl_scope) => (
                self.resolve_associated_fns(impl_scope.clone())?,
                self.resolve_mixins(impl_scope)?,
            ),
            None => ((&[]).alloc_on(self.ast), (&[]).alloc_on(self.ast)),
        };

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::Enum(Enum {
            name,
            members: members.alloc_on(self.ast),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            associated_fns,
            mixins,
            span: Some(span),
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_function<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        body: Option<tree_sitter::Node<'src>>,
    ) -> Result<(), AluminaError> {
        let mut placeholders = self.ambient_placeholders.clone();
        let mut parameters: Vec<Parameter<'ast>> = Vec::new();
        let code = scope.code().unwrap();

        let is_extern = node.child_by_field_name("extern").is_some();
        let is_protocol_fn = matches!(scope.parent().map(|s| s.typ()), Some(ScopeType::Protocol));

        let abi = node.child_by_field_name("abi").map(|n| code.node_text(n));
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            file: scope.code().unwrap().file_id(),
        };

        for (_name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Placeholder(id, node) => {
                    placeholders.push(Placeholder {
                        id: *id,
                        bounds: TypeVisitor::new(self.ast, scope.clone())
                            .parse_protocol_bounds(*node)?,
                    });
                }
                NamedItem::Parameter(id, node) => {
                    let field_type = TypeVisitor::new(self.ast, scope.clone())
                        .visit(node.child_by_field_name("type").unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        file: code.file_id(),
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

        if is_protocol_fn {
            if is_extern {
                return Err(CodeErrorKind::ProtocolFnsCannotBeExtern).with_span(&scope, node);
            }

            if !placeholders.is_empty() {
                return Err(CodeErrorKind::ProtocolFnsCannotBeGeneric).with_span(&scope, node);
            }
        }

        match abi {
            None | Some("\"C\"") => {
                if is_extern && !placeholders.is_empty() {
                    return Err(CodeErrorKind::ExternCGenericParams).with_span(&scope, node);
                }
            }
            Some("\"intrinsic\"") => {
                let result = Item::Intrinsic(Intrinsic {
                    kind: intrinsic_kind(name.unwrap())
                        .ok_or_else(|| CodeErrorKind::UnknownIntrinsic(name.unwrap().to_string()))
                        .with_span(&scope, node)?,
                    generic_count: placeholders.len(),
                    arg_count: parameters.len(),
                    span: Some(span),
                });
                symbol.assign(result);
                return Ok(());
            }
            Some(abi) => {
                return Err(CodeErrorKind::UnsupportedABI(abi.to_string())).with_span(&scope, node)
            }
        }

        let return_type = node
            .child_by_field_name("return_type")
            .map(|n| TypeVisitor::new(self.ast, scope.clone()).visit(n))
            .transpose()?
            .unwrap_or_else(|| self.ast.intern_type(Ty::Builtin(BuiltinType::Void)));

        let function_body = body
            .map(|body| {
                ExpressionVisitor::new(self.ast, self.diag_ctx.clone(), scope.clone())
                    .generate(body)
            })
            .transpose()?;

        if function_body.is_none() && !is_extern && !is_protocol_fn {
            return Err(CodeErrorKind::FunctionMustHaveBody).with_span(&scope, node);
        }

        let result = Item::Function(Function {
            name,
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

    fn make_static_or_const<'src>(
        &mut self,
        is_const: bool,
        name: Option<&'ast str>,
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

        let result = Item::StaticOrConst(StaticOrConst {
            name,
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            typ,
            init,
            span: Some(span),
            is_const,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_type<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), AluminaError> {
        match node.kind() {
            "struct_definition" => self.make_struct_like(name, symbol, node, scope, impl_scope)?,
            "enum_definition" => self.make_enum(name, symbol, node, scope, impl_scope)?,
            _ => unimplemented!(),
        };

        Ok(())
    }

    pub fn make_item<'src>(
        &mut self,
        scope: Scope<'ast, 'src>,
        name: Option<&'ast str>,
        item: NamedItem<'ast, 'src>,
    ) -> Result<(), AluminaError> {
        self.make_item_group(scope, name, &[item])
    }

    fn make_item_group<'src>(
        &mut self,
        scope: Scope<'ast, 'src>,
        name: Option<&'ast str>,
        item_group: &[NamedItem<'ast, 'src>],
    ) -> Result<(), AluminaError> {
        match item_group {
            [NamedItem::Module(module)] => {
                self.make(module.clone())?;
            }
            [NamedItem::Impl(node, scope)] => {
                return Err(CodeErrorKind::NoFreeStandingImpl).with_span(scope, *node)
            }
            [NamedItem::Type(symbol, node, scope), NamedItem::Impl(_, impl_scope)] => {
                self.make_type(
                    name,
                    *symbol,
                    *node,
                    scope.clone(),
                    Some(impl_scope.clone()),
                )?;
                self.make_impl(impl_scope.clone())?;
            }
            [NamedItem::Type(symbol, node, scope)] => {
                self.make_type(name, *symbol, *node, scope.clone(), None)?;
            }
            [NamedItem::Protocol(symbol, node, scope)] => {
                self.make_protocol(name, *symbol, *node, scope.clone())?;
                self.make(scope.clone())?;
            }
            [NamedItem::Static(symbol, node)] => {
                self.make_static_or_const(false, name, *symbol, *node, scope)?;
            }
            [NamedItem::Const(symbol, node)] => {
                self.make_static_or_const(true, name, *symbol, *node, scope)?;
            }
            [NamedItem::Macro(symbol, node, scope)] => {
                let mut macro_maker = MacroMaker::new(self.ast, self.diag_ctx.clone());
                macro_maker.make(name, *symbol, *node, scope.clone())?;
                self.symbols.push(symbol);
            }
            [NamedItem::Function(symbol, node, scope)] => self.make_function(
                name,
                symbol,
                *node,
                scope.clone(),
                node.child_by_field_name("body"),
            )?,
            _ => {}
        }

        Ok(())
    }

    pub fn make<'src>(&mut self, scope: Scope<'ast, 'src>) -> Result<(), AluminaError> {
        for (name, items) in scope.inner().grouped_items() {
            self.make_item_group(scope.clone(), name, items)?;
        }

        Ok(())
    }
}
