use crate::{
    ast::{AstCtx, AstId, BuiltinType, Field, Function, Item, ItemP, Parameter, Struct, Ty},
    common::{ArenaAllocatable, SyntaxError, ToSyntaxError},
    name_resolution::scope::{NamedItem, Scope},
    parser::{AluminaVisitor, ParseCtx},
};

use super::{expressions::ExpressionVisitor, types::TypeVisitor, AssociatedFn, Enum, EnumMember, Attribute, AttributeKind};

pub struct AstItemMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    symbols: Vec<ItemP<'ast>>,
}

impl<'ast> AstItemMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>) -> Self {
        Self {
            ast,
            symbols: Vec::new(),
        }
    }

    pub fn into_inner(self) -> Vec<ItemP<'ast>> {
        self.symbols
    }

    fn resolve_associated_fns<'src>(
        &self,
        scope: Scope<'ast, 'src>,
    ) -> Result<&'ast [AssociatedFn<'ast>], SyntaxError<'src>> {
        let mut associated_fns = Vec::new();

        for (name, item) in scope.inner().all_items() {
            match item {
                NamedItem::Function(symbol, _, _) => associated_fns.push(AssociatedFn {
                    name: name.alloc_on(self.ast),
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
        symbol: ItemP<'ast>,
        _node: tree_sitter::Node<'src>,
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
                        name: name.alloc_on(self.ast),
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
            placeholders: placeholders.alloc_on(self.ast),
            fields: fields.alloc_on(self.ast),
            associated_fns,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_enum<'src>(
        &mut self,
        symbol: ItemP<'ast>,
        _node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), SyntaxError<'src>> {
        let mut members = Vec::new();

        for (_name, item) in scope.inner().all_items() {
            match item {
                NamedItem::EnumMember(_, id, node) => {
                    let field_value = node
                        .child_by_field_name("value")
                        .map(|node| ExpressionVisitor::new(self.ast, scope.clone()).visit(node))
                        .transpose()?;

                    members.push(EnumMember {
                        id: *id,
                        value: field_value,
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
            members: members.alloc_on(self.ast),
            associated_fns,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_attribute<'src>(
        &mut self,
        code: &'src ParseCtx<'src>,
        node: tree_sitter::Node<'src>,
    ) -> Result<&'ast [Attribute], SyntaxError<'src>> {
        let attribute = node.child_by_field_name("attribute").iter().flat_map(|n| {
            let mut cursor = node.walk();
            n.children_by_field_name("name", &mut cursor)
                .map(|n| code.node_text(n))
                .collect::<Vec<_>>()
        }).filter_map(|name| match name {
            "export" => Some(Attribute { kind: AttributeKind::Export }),
            _ => None,
        }).collect::<Vec<_>>().alloc_on(self.ast);

        Ok(attribute)
    }

    fn make_function_impl<'src>(
        &mut self,
        name: &'src str,
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
            .map(|body| ExpressionVisitor::new(self.ast, scope.clone()).visit(body))
            .transpose()?;

        let result = Item::Function(Function {
            name: Some(name.alloc_on(self.ast)),
            attributes: self.make_attribute(scope.code().unwrap(), node)?,
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
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scope: Option<Scope<'ast, 'src>>,
    ) -> Result<(), SyntaxError<'src>> {
        match node.kind() {
            "struct_definition" => self.make_struct(symbol, node, scope, impl_scope)?,
            "enum_definition" => self.make_enum(symbol, node, scope, impl_scope)?,
            _ => unimplemented!(),
        };

        Ok(())
    }

    fn make_function<'src>(
        &mut self,
        name: &'src str,
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
            "extern_function_declaration" => self.make_function_impl(name, symbol, node, scope, None)?,
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
                    self.make_type(*symbol, *node, scope.clone(), Some(impl_scope.clone()))?;
                    self.make(impl_scope.clone())?;
                }
                [NamedItem::Type(symbol, node, scope)] => {
                    self.make_type(*symbol, *node, scope.clone(), None)?;
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
