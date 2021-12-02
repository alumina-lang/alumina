use crate::{
    ast::{BuiltinType, Field, Function, NodeId, Parameter, Struct, Symbol, SymbolP, Ty},
    common::SyntaxError,
    name_resolution::scope::{Item, Scope},
    parser::AluminaVisitor,
};

use super::{expressions::ExpressionVisitor, types::TypeVisitor};

pub struct Maker<'gcx> {
    pub symbols: Vec<SymbolP<'gcx>>,
}

impl<'gcx> Maker<'gcx> {
    pub fn new() -> Self {
        Self {
            symbols: Vec::new(),
        }
    }

    fn resolve_associated_fns<'src>(
        &self,
        scope: Scope<'gcx, 'src>,
    ) -> Result<&'gcx [SymbolP<'gcx>], SyntaxError<'src>> {
        let mut associated_fns: Vec<SymbolP<'gcx>> = Vec::new();
        let parse_ctx = scope.parse_ctx().unwrap();

        for (_name, item) in scope.inner().all_items() {
            match item {
                Item::Function(symbol, _, _) => associated_fns.push(*symbol),
                _ => {}
            }
        }

        Ok(parse_ctx.alloc_slice(associated_fns.as_slice()))
    }

    fn make_struct<'src>(
        &mut self,
        symbol: SymbolP<'gcx>,
        _node: tree_sitter::Node<'src>,
        scope: Scope<'gcx, 'src>,
        impl_scope: Option<Scope<'gcx, 'src>>,
    ) -> Result<(), SyntaxError<'src>> {
        let mut placeholders: Vec<NodeId> = Vec::new();
        let mut fields: Vec<Field<'gcx>> = Vec::new();

        let parse_ctx = scope.parse_ctx().unwrap();

        for (name, item) in scope.inner().all_items() {
            match item {
                Item::Placeholder(placeholder) => {
                    placeholders.push(*placeholder);
                }
                Item::Field(node) => {
                    let mut visitor = TypeVisitor::new(scope.clone());
                    let field_type = visitor.visit(node.child_by_field_name("type").unwrap())?;

                    fields.push(Field {
                        name: parse_ctx.alloc_str(name),
                        ty: field_type,
                    });
                }
                _ => {}
            }
        }

        let associated_fns = match impl_scope {
            Some(impl_scope) => self.resolve_associated_fns(impl_scope)?,
            None => parse_ctx.alloc_slice(&[]),
        };

        let result = Symbol::Struct(Struct {
            placeholders: parse_ctx.alloc_slice(placeholders.as_slice()),
            fields: parse_ctx.alloc_slice(fields.as_slice()),
            associated_fns,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_function_impl<'src>(
        &mut self,
        symbol: SymbolP<'gcx>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'gcx, 'src>,
        body: Option<tree_sitter::Node<'src>>,
    ) -> Result<(), SyntaxError<'src>> {
        let mut placeholders: Vec<NodeId> = Vec::new();
        let mut parameters: Vec<Parameter<'gcx>> = Vec::new();

        let parse_ctx = scope.parse_ctx().unwrap();

        for (_name, item) in scope.inner().all_items() {
            match item {
                Item::Placeholder(placeholder) => {
                    placeholders.push(*placeholder);
                }
                Item::Parameter(id, node) => {
                    let field_type = TypeVisitor::new(scope.clone())
                        .visit(node.child_by_field_name("type").unwrap())?;

                    parameters.push(Parameter {
                        id: *id,
                        ty: field_type,
                    });
                }
                _ => {}
            }
        }

        let return_type = node
            .child_by_field_name("return_type")
            .map(|n| TypeVisitor::new(scope.clone()).visit(n))
            .transpose()?
            .unwrap_or(parse_ctx.intern_type(Ty::Builtin(BuiltinType::Void)));

        let function_body = body
            .map(|body| ExpressionVisitor::new(scope.clone()).visit(body))
            .transpose()?;

        let result = Symbol::Function(Function {
            placeholders: parse_ctx.alloc_slice(placeholders.as_slice()),
            parameters: parse_ctx.alloc_slice(parameters.as_slice()),
            return_type,
            body: function_body,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_type<'src>(
        &mut self,
        symbol: SymbolP<'gcx>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'gcx, 'src>,
        impl_scope: Option<Scope<'gcx, 'src>>,
    ) -> Result<(), SyntaxError<'src>> {
        match node.kind() {
            "struct_definition" => self.make_struct(symbol, node, scope, impl_scope)?,
            _ => unimplemented!(),
        };

        Ok(())
    }

    fn make_function<'src>(
        &mut self,
        symbol: SymbolP<'gcx>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'gcx, 'src>,
    ) -> Result<(), SyntaxError<'src>> {
        match node.kind() {
            "function_definition" => self.make_function_impl(
                symbol,
                node,
                scope,
                Some(node.child_by_field_name("body").unwrap()),
            )?,
            "extern_function_declaration" => self.make_function_impl(symbol, node, scope, None)?,
            _ => unimplemented!(),
        };

        Ok(())
    }

    pub fn make<'src>(&mut self, scope: Scope<'gcx, 'src>) -> Result<(), SyntaxError<'src>> {
        for (_, item) in scope.inner().grouped_items() {
            match item {
                [Item::Module(module)] => {
                    self.make(module.clone())?;
                }
                [Item::Type(symbol, node, scope), Item::Impl(impl_scope)] => {
                    self.make_type(*symbol, *node, scope.clone(), Some(impl_scope.clone()))?;
                    self.make(impl_scope.clone())?;
                }
                [Item::Type(symbol, node, scope)] => {
                    self.make_type(*symbol, *node, scope.clone(), None)?;
                }
                [Item::Function(symbol, node, scope)] => {
                    self.make_function(*symbol, *node, scope.clone())?;
                }
                _ => {}
            }
        }

        Ok(())
    }
}
