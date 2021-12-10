use std::collections::HashMap;

use crate::{
    ast::{AstCtx, AstId, BuiltinType, Field, Function, Item, ItemP, Parameter, Struct, Ty},
    common::{ArenaAllocatable, SyntaxError},
    name_resolution::scope::{NamedItem, Scope},
    parser::{AluminaVisitor, ParseCtx},
};

use super::{
    expressions::ExpressionVisitor,
    lang::{lang_item_kind, LangItemKind, LangItemMap},
    types::TypeVisitor,
    AssociatedFn, Attribute, Enum, EnumMember,
};

pub struct AstItemMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    symbols: Vec<ItemP<'ast>>,

    lang_items: HashMap<LangItemKind, ItemP<'ast>>,
}

impl<'ast> AstItemMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>) -> Self {
        Self {
            ast,
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
    ) -> Result<&'ast [Attribute], SyntaxError<'src>> {
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
    ) -> Result<&'ast [AssociatedFn<'ast>], SyntaxError<'src>> {
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
    ) -> Result<(), SyntaxError<'src>> {
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

                    fields.push(Field {
                        id: self.ast.make_id(),
                        name: name,
                        typ: field_type,
                    });
                }
                _ => {}
            }
        }

        let associated_fns = match impl_scope {
            Some(impl_scope) => self.resolve_associated_fns(impl_scope)?,
            None => (&[]).alloc_on(self.ast),
        };

        let result = Item::Struct(Struct {
            name: Some(name),
            placeholders: placeholders.alloc_on(self.ast),
            fields: fields.alloc_on(self.ast),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            associated_fns,
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
    ) -> Result<(), SyntaxError<'src>> {
        let mut members = Vec::new();

        for (name, item) in scope.inner().all_items() {
            match item {
                NamedItem::EnumMember(_, id, node) => {
                    let expr = node
                        .child_by_field_name("value")
                        .map(|node| {
                            ExpressionVisitor::new(self.ast, scope.clone())
                                .generate(node)
                                .and_then(|(expr, additional_items)| {
                                    self.symbols.extend(additional_items);
                                    Ok(expr)
                                })
                        })
                        .transpose()?;

                    members.push(EnumMember {
                        name: Some(name),
                        id: *id,
                        value: expr,
                    });
                }
                _ => {}
            }
        }

        let associated_fns = match impl_scope {
            Some(impl_scope) => self.resolve_associated_fns(impl_scope)?,
            None => (&[]).alloc_on(self.ast),
        };

        let result = Item::Enum(Enum {
            name: Some(name),
            members: members.alloc_on(self.ast),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            associated_fns,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_function_impl<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        body: Option<tree_sitter::Node<'src>>,
    ) -> Result<(), SyntaxError<'src>> {
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

                    parameters.push(Parameter {
                        id: *id,
                        typ: field_type,
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
                ExpressionVisitor::new(self.ast, scope.clone())
                    .generate(body)
                    .and_then(|(expr, additional_items)| {
                        self.symbols.extend(additional_items);
                        Ok(expr)
                    })
            })
            .transpose()?;

        let result = Item::Function(Function {
            name: Some(name),
            attributes: self.get_attributes(symbol, scope.code().unwrap(), node)?,
            placeholders: placeholders.alloc_on(self.ast),
            args: parameters.alloc_on(self.ast),
            return_type,
            body: function_body,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_type<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), SyntaxError<'src>> {
        match node.kind() {
            "struct_definition" => self.make_struct(name, symbol, node, scope, impl_scope)?,
            "enum_definition" => self.make_enum(name, symbol, node, scope, impl_scope)?,
            _ => unimplemented!(),
        };

        Ok(())
    }

    fn make_function<'src>(
        &mut self,
        name: &'ast str,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
    ) -> Result<(), SyntaxError<'src>> {
        match node.kind() {
            "function_definition" => self.make_function_impl(
                name,
                symbol,
                node,
                scope,
                Some(node.child_by_field_name("body").unwrap()),
            )?,
            "extern_function_declaration" => {
                self.make_function_impl(name, symbol, node, scope, None)?
            }
            _ => unimplemented!(),
        };

        Ok(())
    }

    pub fn make<'src>(&mut self, scope: Scope<'ast, 'src>) -> Result<(), SyntaxError<'src>> {
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
                [NamedItem::Function(symbol, node, scope)] => {
                    self.make_function(name, *symbol, *node, scope.clone())?;
                }
                _ => {}
            }
        }

        Ok(())
    }
}
