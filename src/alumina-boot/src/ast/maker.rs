use crate::common::HashSet;

use once_cell::unsync::OnceCell;

use crate::{
    ast::{AstCtx, BuiltinType, Field, Function, Item, ItemP, Parameter, StructLike, Ty},
    common::{
        AluminaError, ArenaAllocatable, CodeError, CodeErrorKind, Marker, WithSpanDuringParsing,
    },
    global_ctx::GlobalCtx,
    intrinsics::intrinsic_kind,
    name_resolution::{
        resolver::NameResolver,
        scope::{NamedItem, NamedItemKind, Scope, ScopeType},
    },
    parser::AluminaVisitor,
};

use crate::parser::FieldKind;
use crate::parser::NodeExt;
use crate::parser::NodeKind;

use super::{
    expressions::ExpressionVisitor, lang::LangItemKind, macros::MacroMaker, types::TypeVisitor,
    AssociatedFn, Attribute, Enum, EnumMember, Intrinsic, Mixin, MixinCell, Placeholder, Protocol,
    Span, StaticOrConst, TyP, TypeDef,
};

pub struct AstItemMaker<'ast> {
    ast: &'ast AstCtx<'ast>,
    global_ctx: GlobalCtx,
    symbols: Vec<ItemP<'ast>>,
    ambient_placeholders: Vec<Placeholder<'ast>>,
    in_a_macro: bool,
    local: bool,
}

impl<'ast> AstItemMaker<'ast> {
    pub fn new(ast: &'ast AstCtx<'ast>, global_ctx: GlobalCtx, in_a_macro: bool) -> Self {
        Self {
            ast,
            global_ctx,
            symbols: Vec::new(),
            ambient_placeholders: Vec::new(),
            in_a_macro,
            local: false,
        }
    }

    pub fn new_local(ast: &'ast AstCtx<'ast>, global_ctx: GlobalCtx, in_a_macro: bool) -> Self {
        Self {
            ast,
            global_ctx,
            symbols: Vec::new(),
            ambient_placeholders: Vec::new(),
            in_a_macro,
            local: true,
        }
    }

    pub fn into_inner(self) -> Vec<ItemP<'ast>> {
        self.symbols
    }

    pub fn get_placeholders<'src>(
        &self,
        scope: &Scope<'ast, 'src>,
    ) -> Result<&'ast [Placeholder<'ast>], AluminaError> {
        let mut placeholders = self.ambient_placeholders.clone();
        for (_name, item) in scope.inner().all_items() {
            match item.kind {
                NamedItemKind::Placeholder(id, node) => {
                    placeholders.push(Placeholder {
                        id,
                        default: node
                            .child_by_field(FieldKind::Default)
                            .map(|node| {
                                // Default values for generic parameters are name-resolved in parent
                                // scope to avoid cyclic references, like `struct Foo<T2 = T2>`. This
                                // also disallows references to other generic parameters, which could
                                // technically be allowed, but it complicates mono, so it's not allowed for
                                // now. The complication is that default args need to be resolved quite
                                // early in the monomorphization process to ensure that fully-specified
                                // items and ones instantiated with default values result in the same item.
                                TypeVisitor::new(
                                    self.global_ctx.clone(),
                                    self.ast,
                                    scope.parent().unwrap(),
                                    self.in_a_macro,
                                )
                                .visit(node)
                            })
                            .transpose()?,
                        // Unlike defaults, bounds can refer to self and this is in fact quite central
                        // to how Alumina protocols work.
                        bounds: TypeVisitor::new(
                            self.global_ctx.clone(),
                            self.ast,
                            scope.clone(),
                            self.in_a_macro,
                        )
                        .parse_protocol_bounds(node)?,
                    });
                }
                _ => {}
            }
        }

        Ok(placeholders.alloc_on(self.ast))
    }

    fn resolve_associated_items<'src>(
        &self,
        impl_scopes: &[Scope<'ast, 'src>],
    ) -> Result<(&'ast [AssociatedFn<'ast>], &'ast [Mixin<'ast>]), AluminaError> {
        let mut associated_fns = Vec::new();
        let mut mixins = Vec::new();
        let mut names = HashSet::default();

        for impl_scope in impl_scopes {
            for (name, item) in impl_scope.inner().all_items() {
                match &item.kind {
                    NamedItemKind::Function(symbol, node, _)
                    | NamedItemKind::Method(symbol, node, _) => {
                        if let Some(name) = name {
                            if !names.insert(name) {
                                self.global_ctx.diag().add_warning(CodeError::from_kind(
                                    CodeErrorKind::DuplicateNameShadow(name.to_string()),
                                    Some(Span {
                                        start: node.start_byte(),
                                        end: node.end_byte(),
                                        line: node.start_position().row,
                                        column: node.start_position().column,
                                        file: impl_scope.code().unwrap().file_id(),
                                    }),
                                ));
                            }
                        }
                        associated_fns.push(AssociatedFn {
                            name: name.unwrap(),
                            item: symbol,
                        })
                    }
                    NamedItemKind::Mixin(node, scope) => {
                        // FIXME: Unify this between functions and mixin
                        let mut placeholders = self.get_placeholders(impl_scope)?.to_vec();
                        placeholders.extend_from_slice(self.get_placeholders(scope)?);
                        let placeholders = placeholders.alloc_on(self.ast);

                        let mut visitor = TypeVisitor::new(
                            self.global_ctx.clone(),
                            self.ast,
                            scope.clone(),
                            self.in_a_macro,
                        );
                        let protocol_type =
                            visitor.visit(node.child_by_field(FieldKind::Protocol).unwrap())?;

                        let span = Span {
                            start: node.start_byte(),
                            end: node.end_byte(),
                            line: node.start_position().row,
                            column: node.start_position().column,
                            file: scope.code().unwrap().file_id(),
                        };

                        mixins.push(Mixin {
                            placeholders,
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
        }

        let associated_fns = associated_fns.alloc_on(self.ast);
        let mixins = mixins.alloc_on(self.ast);

        Ok((associated_fns, mixins))
    }

    fn make_struct_like<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        impl_scopes: &[Scope<'ast, 'src>],
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        let mut fields: Vec<Field<'ast>> = Vec::new();

        let code = scope.code().unwrap();

        for (name, item) in scope.inner().all_items() {
            match item.kind {
                NamedItemKind::Field(node) => {
                    let mut visitor = TypeVisitor::new(
                        self.global_ctx.clone(),
                        self.ast,
                        scope.clone(),
                        self.in_a_macro,
                    );
                    let field_type =
                        visitor.visit(node.child_by_field(FieldKind::Type).unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        line: node.start_position().row,
                        column: node.start_position().column,
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

        let placeholders = self.get_placeholders(&scope)?;
        let is_union = match code.node_text(node.child_by_field(FieldKind::Kind).unwrap()) {
            "struct" => false,
            "union" => true,
            _ => unimplemented!(),
        };

        if attributes.contains(&Attribute::Transparent) && fields.len() != 1 {
            return Err(CodeErrorKind::InvalidTransparent).with_span_from(&scope, node);
        }

        let (associated_fns, mixins) = self.resolve_associated_items(impl_scopes)?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: node.start_position().column,
            file: code.file_id(),
        };

        let result = Item::StructLike(StructLike {
            name,
            placeholders,
            fields: fields.alloc_on(self.ast),
            attributes,
            associated_fns,
            mixins,
            span: Some(span),
            is_local: self.local,
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
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        let code = scope.code().unwrap();
        let placeholders = self.get_placeholders(&scope)?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: node.start_position().column,
            file: code.file_id(),
        };

        let (associated_fns, _) = self.resolve_associated_items(&[scope])?;

        let result = Item::Protocol(Protocol {
            name,
            placeholders,
            associated_fns,
            attributes,
            is_local: self.local,
            span: Some(span),
        });

        symbol.assign(result);

        Ok(())
    }

    fn make_impl<'src>(&mut self, scope: Scope<'ast, 'src>) -> Result<(), AluminaError> {
        // Ambient placeholders on impl blocks
        self.ambient_placeholders = self.get_placeholders(&scope)?.to_vec();
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
        impl_scopes: &[Scope<'ast, 'src>],
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        let mut members = Vec::new();

        for (name, item) in scope.inner().all_items() {
            match item.kind {
                NamedItemKind::EnumMember(_, id, node) => {
                    let value = node
                        .child_by_field(FieldKind::Value)
                        .map(|node| {
                            ExpressionVisitor::new(
                                self.ast,
                                self.global_ctx.clone(),
                                scope.clone(),
                                self.in_a_macro,
                            )
                            .generate(node)
                        })
                        .transpose()?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        line: node.start_position().row,
                        column: node.start_position().column,
                        file: scope.code().unwrap().file_id(),
                    };

                    members.push(EnumMember {
                        name: name.unwrap(),
                        id,
                        value,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        let (associated_fns, mixins) = self.resolve_associated_items(impl_scopes)?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: node.start_position().column,
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::Enum(Enum {
            name,
            members: members.alloc_on(self.ast),
            attributes,
            associated_fns,
            mixins,
            is_local: self.local,
            span: Some(span),
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn make_typedef<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        let placeholders = self.get_placeholders(&scope)?;

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: node.start_position().column,
            file: scope.code().unwrap().file_id(),
        };

        let target = node
            .child_by_field(FieldKind::Inner)
            .map(|n| {
                TypeVisitor::new(
                    self.global_ctx.clone(),
                    self.ast,
                    scope.clone(),
                    self.in_a_macro,
                )
                .visit(n)
            })
            .transpose()?;

        let result = Item::TypeDef(TypeDef {
            name,
            placeholders,
            target,
            span: Some(span),
            is_local: self.local,
            attributes,
        });

        symbol.assign(result);

        self.symbols.push(symbol);

        Ok(())
    }

    fn check_self_confusion(&self, typ: TyP<'ast>, span: Option<Span>) {
        match typ {
            Ty::NamedType(item) | Ty::Pointer(Ty::NamedType(item), _) => {
                if let Some(LangItemKind::DynSelf) = self.ast.lang_item_kind(item) {
                    self.global_ctx.diag().add_warning(CodeError {
                        kind: CodeErrorKind::SelfConfusion,
                        backtrace: span.map(Marker::Span).into_iter().collect(),
                    })
                }
            }
            _ => {}
        }
    }

    fn make_function<'src>(
        &mut self,
        name: Option<&'ast str>,
        symbol: ItemP<'ast>,
        node: tree_sitter::Node<'src>,
        scope: Scope<'ast, 'src>,
        body: Option<tree_sitter::Node<'src>>,
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        let mut parameters: Vec<Parameter<'ast>> = Vec::new();
        let code = scope.code().unwrap();

        let is_extern = node.child_by_field(FieldKind::Extern).is_some();
        let has_varargs = node
            .child_by_field(FieldKind::Parameters)
            .and_then(|n| n.child_by_field(FieldKind::EtCetera))
            .is_some();

        if has_varargs && !is_extern {
            return Err(CodeErrorKind::VarArgsCanOnlyBeExtern).with_span_from(&scope, node);
        }

        let is_protocol_fn = matches!(scope.parent().map(|s| s.typ()), Some(ScopeType::Protocol));

        let abi = node
            .child_by_field(FieldKind::Abi)
            .map(|n| code.node_text(n));
        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: node.start_position().column,
            file: scope.code().unwrap().file_id(),
        };

        let placeholders = self.get_placeholders(&scope)?;

        for (_name, item) in scope.inner().all_items() {
            match item.kind {
                NamedItemKind::Parameter(id, node) => {
                    let typ = TypeVisitor::new(
                        self.global_ctx.clone(),
                        self.ast,
                        scope.clone(),
                        self.in_a_macro,
                    )
                    .visit(node.child_by_field(FieldKind::Type).unwrap())?;

                    let span = Span {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        line: node.start_position().row,
                        column: node.start_position().column,
                        file: code.file_id(),
                    };

                    self.check_self_confusion(typ, Some(span));

                    parameters.push(Parameter {
                        id,
                        typ,
                        span: Some(span),
                    });
                }
                _ => {}
            }
        }

        if is_protocol_fn && is_extern {
            return Err(CodeErrorKind::ProtocolFnsCannotBeExtern).with_span_from(&scope, node);
        }

        match abi {
            None | Some("\"C\"") => {
                if is_extern && !placeholders.is_empty() {
                    return Err(CodeErrorKind::ExternCGenericParams).with_span_from(&scope, node);
                }
            }
            Some("\"intrinsic\"") => {
                let result = Item::Intrinsic(Intrinsic {
                    kind: intrinsic_kind(name.unwrap())
                        .ok_or_else(|| CodeErrorKind::UnknownIntrinsic(name.unwrap().to_string()))
                        .with_span_from(&scope, node)?,
                    generic_count: placeholders.len(),
                    arg_count: parameters.len(),
                    varargs: has_varargs,
                    span: Some(span),
                });
                symbol.assign(result);
                return Ok(());
            }
            Some(abi) => {
                return Err(CodeErrorKind::UnsupportedABI(abi.to_string()))
                    .with_span_from(&scope, node)
            }
        }

        let return_type = node
            .child_by_field(FieldKind::ReturnType)
            .map(|n| {
                TypeVisitor::new(
                    self.global_ctx.clone(),
                    self.ast,
                    scope.clone(),
                    self.in_a_macro,
                )
                .visit(n)
            })
            .transpose()?
            .unwrap_or_else(|| self.ast.intern_type(Ty::Builtin(BuiltinType::Void)));

        self.check_self_confusion(return_type, Some(span));

        let function_body = body
            .map(|body| {
                ExpressionVisitor::new(
                    self.ast,
                    self.global_ctx.clone(),
                    scope.clone(),
                    self.in_a_macro,
                )
                .generate(body)
            })
            .transpose()?;

        if function_body.is_none() && !is_extern && !is_protocol_fn {
            return Err(CodeErrorKind::FunctionMustHaveBody).with_span_from(&scope, node);
        }

        let result = Item::Function(Function {
            name,
            attributes,
            placeholders,
            args: parameters.alloc_on(self.ast),
            return_type,
            body: function_body,
            varargs: has_varargs,
            span: Some(span),
            is_local: self.local,
            is_protocol_fn,
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
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        let typ = node
            .child_by_field(FieldKind::Type)
            .map(|n| {
                TypeVisitor::new(
                    self.global_ctx.clone(),
                    self.ast,
                    scope.clone(),
                    self.in_a_macro,
                )
                .visit(n)
            })
            .transpose()?;

        let is_extern = node.child_by_field(FieldKind::Extern).is_some();
        assert!(!is_extern || !is_const);

        let init = node
            .child_by_field(FieldKind::Init)
            .map(|body| {
                ExpressionVisitor::new(
                    self.ast,
                    self.global_ctx.clone(),
                    scope.clone(),
                    self.in_a_macro,
                )
                .generate(body)
            })
            .transpose()?;

        let placeholders = self.get_placeholders(&scope)?;
        if !placeholders.is_empty() && is_extern {
            return Err(CodeErrorKind::ExternStaticCannotBeGeneric).with_span_from(&scope, node);
        }

        if typ.is_none() && init.is_none() {
            return Err(CodeErrorKind::TypeHintRequired).with_span_from(&scope, node);
        }

        if is_extern && (typ.is_none() || init.is_some()) {
            return Err(CodeErrorKind::ExternStaticMustHaveType).with_span_from(&scope, node);
        }

        let span = Span {
            start: node.start_byte(),
            end: node.end_byte(),
            line: node.start_position().row,
            column: node.start_position().column,
            file: scope.code().unwrap().file_id(),
        };

        let result = Item::StaticOrConst(StaticOrConst {
            name,
            attributes,
            typ,
            init,
            span: Some(span),
            is_const,
            placeholders,
            is_local: self.local,
            r#extern: is_extern,
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
        impl_scopes: &[Scope<'ast, 'src>],
        attributes: &'ast [Attribute],
    ) -> Result<(), AluminaError> {
        match node.kind_typed() {
            NodeKind::StructDefinition => {
                self.make_struct_like(name, symbol, node, scope, impl_scopes, attributes)?
            }
            NodeKind::EnumDefinition => {
                self.make_enum(name, symbol, node, scope, impl_scopes, attributes)?
            }
            _ => unimplemented!(),
        };

        Ok(())
    }

    pub fn make_item_group<'src>(
        &mut self,
        scope: Scope<'ast, 'src>,
        name: Option<&'ast str>,
        item_group: &[NamedItem<'ast, 'src>],
    ) -> Result<(), AluminaError> {
        use NamedItem as NI;
        use NamedItemKind::*;
        match item_group {
            [NI {
                kind: Alias(path, node),
                ..
            }] => {
                let mut resolver = NameResolver::new();

                // Resolve all aliases to avoid having non-existent uses
                resolver
                    .resolve_item(scope.clone(), path.clone())
                    .with_span_from(&scope, *node)?;
            }
            [NI {
                kind: Module(module),
                ..
            }] => {
                self.make(module.clone())?;
            }
            [NI {
                kind: Impl(node, scope),
                ..
            }] => return Err(CodeErrorKind::NoFreeStandingImpl).with_span_from(scope, *node),
            [NI {
                kind: Type(symbol, node, scope),
                attributes,
            }, rest @ ..] => {
                let mut impl_scopes = Vec::with_capacity(rest.len());
                for impl_item in rest {
                    match &impl_item.kind {
                        NamedItemKind::Impl(_, scope) => {
                            self.make_impl(scope.clone())?;
                            impl_scopes.push(scope.clone());
                        }
                        _ => unreachable!(),
                    }
                }
                self.make_type(
                    name,
                    *symbol,
                    *node,
                    scope.clone(),
                    &impl_scopes[..],
                    attributes,
                )?;
            }
            [NI {
                kind: TypeDef(symbol, node, scope),
                attributes,
            }] => {
                self.make_typedef(name, *symbol, *node, scope.clone(), attributes)?;
            }
            [NI {
                kind: Protocol(symbol, node, scope),
                attributes,
            }] => {
                self.make_protocol(name, *symbol, *node, scope.clone(), attributes)?;
                self.make(scope.clone())?;
            }
            [NI {
                kind: Static(symbol, node, scope),
                attributes,
            }] => {
                self.make_static_or_const(false, name, *symbol, *node, scope.clone(), attributes)?;
            }
            [NI {
                kind: Const(symbol, node, scope),
                attributes,
            }] => {
                self.make_static_or_const(true, name, *symbol, *node, scope.clone(), attributes)?;
            }
            [NI {
                kind: Macro(symbol, node, scope),
                attributes,
            }] => {
                let mut macro_maker = MacroMaker::new(self.ast, self.global_ctx.clone());
                macro_maker.make(name, *symbol, *node, scope.clone(), attributes)?;
                self.symbols.push(symbol);
            }
            [NI {
                kind: Function(symbol, node, scope),
                attributes,
            }] => self.make_function(
                name,
                symbol,
                *node,
                scope.clone(),
                node.child_by_field(FieldKind::Body),
                attributes,
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
