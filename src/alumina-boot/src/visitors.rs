use crate::ast::expressions::parse_string_literal;
use crate::ast::{AstCtx, Attribute, ItemP, Span, TestMetadata};
use crate::common::{
    AluminaError, ArenaAllocatable, CodeError, CodeErrorKind, Marker, WithSpanDuringParsing,
};
use crate::global_ctx::GlobalCtx;
use crate::name_resolution::path::{Path, PathSegment};
use crate::name_resolution::scope::{NamedItem, NamedItemKind, Scope};
use crate::parser::{AluminaVisitor, FieldKind, NodeExt, ParseCtx};

use tree_sitter::Node;

pub struct ScopedPathVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>, // ast: &'ast AstCtx<'ast>
    in_a_macro: bool,
}

impl<'ast, 'src> ScopedPathVisitor<'ast, 'src> {
    pub fn new(ast: &'ast AstCtx<'ast>, scope: Scope<'ast, 'src>, in_a_macro: bool) -> Self {
        Self {
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            in_a_macro,
        }
    }
}

pub trait VisitorExt<'src> {
    type ReturnType;

    fn visit_children(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType;

    fn visit_children_by_field(
        &mut self,
        node: tree_sitter::Node<'src>,
        field: &'static str,
    ) -> Self::ReturnType;
}

impl<'src, T, E> VisitorExt<'src> for T
where
    T: AluminaVisitor<'src, ReturnType = Result<(), E>>,
{
    type ReturnType = Result<(), E>;

    fn visit_children(&mut self, node: tree_sitter::Node<'src>) -> Result<(), E> {
        let mut cursor = node.walk();
        for node in node.children(&mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }

    fn visit_children_by_field(
        &mut self,
        node: tree_sitter::Node<'src>,
        field: &'static str,
    ) -> Result<(), E> {
        let mut cursor = node.walk();
        for node in node.children_by_field_name(field, &mut cursor) {
            self.visit(node)?;
        }

        Ok(())
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for ScopedPathVisitor<'ast, 'src> {
    type ReturnType = Result<Path<'ast>, AluminaError>;

    fn visit_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.code.node_text(node).alloc_on(self.ast);

        Ok(PathSegment(name).into())
    }

    fn visit_macro_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        if !self.in_a_macro {
            return Err(CodeErrorKind::DollaredOutsideOfMacro).with_span_from(&self.scope, node);
        }

        let name = self.code.node_text(node).alloc_on(self.ast);

        Ok(PathSegment(name).into())
    }

    fn visit_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let name = self.code.node_text(node).alloc_on(self.ast);

        Ok(PathSegment(name).into())
    }

    fn visit_scoped_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let subpath = match node.child_by_field(FieldKind::Path) {
            Some(subnode) => self.visit(subnode)?,
            None => Path::root(),
        };

        let name = self
            .code
            .node_text(node.child_by_field(FieldKind::Name).unwrap())
            .alloc_on(self.ast);

        Ok(subpath.extend(PathSegment(name)))
    }

    fn visit_generic_type(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        Err(CodeErrorKind::GenericArgsInPath).with_span_from(&self.scope, node)
    }

    fn visit_scoped_type_identifier(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let subpath = match node.child_by_field(FieldKind::Path) {
            Some(subnode) => self.visit(subnode)?,
            None => Path::root(),
        };

        let name = self
            .code
            .node_text(node.child_by_field(FieldKind::Name).unwrap())
            .alloc_on(self.ast);

        Ok(subpath.extend(PathSegment(name)))
    }
}

pub struct UseClauseVisitor<'ast, 'src> {
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    prefix: Path<'ast>,
    scope: Scope<'ast, 'src>,
    attributes: &'ast [Attribute],
    in_a_macro: bool,
}

impl<'ast, 'src> UseClauseVisitor<'ast, 'src> {
    pub fn new(
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        attributes: &'ast [Attribute],
        in_a_macro: bool,
    ) -> Self {
        Self {
            ast,
            prefix: Path::default(),
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            attributes,
            in_a_macro,
        }
    }

    fn parse_use_path(&mut self, node: Node<'src>) -> Result<Path<'ast>, AluminaError> {
        let mut visitor = ScopedPathVisitor::new(self.ast, self.scope.clone(), self.in_a_macro);
        visitor.visit(node)
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for UseClauseVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_use_as_clause(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let path = self.parse_use_path(node.child_by_field(FieldKind::Path).unwrap())?;
        let alias = self
            .code
            .node_text(node.child_by_field(FieldKind::Alias).unwrap())
            .alloc_on(self.ast);

        self.scope
            .add_item(
                Some(alias),
                NamedItem::new(
                    NamedItemKind::Alias(self.prefix.join_with(path), node),
                    self.attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_use_list(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        self.visit_children_by_field(node, "item")
    }

    fn visit_scoped_use_list(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let suffix = self.parse_use_path(node.child_by_field(FieldKind::Path).unwrap())?;
        let new_prefix = self.prefix.join_with(suffix);
        let old_prefix = std::mem::replace(&mut self.prefix, new_prefix);

        self.visit(node.child_by_field(FieldKind::List).unwrap())?;
        self.prefix = old_prefix;

        Ok(())
    }

    fn visit_identifier(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let alias = self.code.node_text(node).alloc_on(self.ast);
        self.scope
            .add_item(
                Some(alias),
                NamedItem::new(
                    NamedItemKind::Alias(self.prefix.extend(PathSegment(alias)), node),
                    self.attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }

    fn visit_use_wildcard(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let path = self.parse_use_path(node.child_by_field(FieldKind::Path).unwrap())?;
        self.scope.add_star_import(self.prefix.join_with(path));

        Ok(())
    }

    fn visit_scoped_identifier(&mut self, node: Node<'src>) -> Result<(), AluminaError> {
        let path = match node.child_by_field(FieldKind::Path) {
            Some(path) => self.parse_use_path(path)?,
            None => Path::root(),
        };
        let name = self
            .code
            .node_text(node.child_by_field(FieldKind::Name).unwrap())
            .alloc_on(self.ast);

        self.scope
            .add_item(
                Some(name),
                NamedItem::new(
                    NamedItemKind::Alias(
                        self.prefix.join_with(path.extend(PathSegment(name))),
                        node,
                    ),
                    self.attributes,
                ),
            )
            .with_span_from(&self.scope, node)?;

        Ok(())
    }
}

pub struct AttributeVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    ast: &'ast AstCtx<'ast>,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    item: Option<ItemP<'ast>>,
    attributes: Vec<Attribute>,
    should_skip: bool,
    test_attributes: Vec<String>,
}

impl<'ast, 'src> AttributeVisitor<'ast, 'src> {
    pub fn parse_attributes(
        global_ctx: GlobalCtx,
        ast: &'ast AstCtx<'ast>,
        scope: Scope<'ast, 'src>,
        node: Node<'src>,
        item: Option<ItemP<'ast>>,
    ) -> Result<Option<&'ast [Attribute]>, AluminaError> {
        let mut visitor = AttributeVisitor {
            global_ctx,
            ast,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            item,
            attributes: Vec::new(),
            should_skip: false,
            test_attributes: Vec::new(),
        };

        if let Some(node) = node.child_by_field(FieldKind::Attributes) {
            visitor.visit(node)?;
        }

        visitor.finalize(node)?;

        if visitor.should_skip {
            Ok(None)
        } else {
            Ok(Some(visitor.attributes.alloc_on(ast)))
        }
    }

    fn finalize(&mut self, node: tree_sitter::Node<'src>) -> Result<(), AluminaError> {
        if !self.test_attributes.is_empty() {
            self.ast.add_test_metadata(
                self.item
                    .ok_or(CodeErrorKind::CannotBeATest)
                    .with_span_from(&self.scope, node)?,
                TestMetadata {
                    attributes: std::mem::take(&mut self.test_attributes),
                    path: self.scope.path(),
                    name: Path::from(PathSegment(
                        self.code
                            .node_text(
                                node.child_by_field(FieldKind::Name)
                                    .ok_or(CodeErrorKind::CannotBeATest)
                                    .with_span_from(&self.scope, node)?,
                            )
                            .alloc_on(self.ast),
                    )),
                },
            );
            self.attributes.push(Attribute::Test);
        }

        Ok(())
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for AttributeVisitor<'ast, 'src> {
    type ReturnType = Result<(), AluminaError>;

    fn visit_attributes(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_children(node)?;
        Ok(())
    }

    fn visit_top_level_attributes(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        self.visit_attributes(node)
    }

    fn visit_top_level_attribute_item(
        &mut self,
        node: tree_sitter::Node<'src>,
    ) -> Self::ReturnType {
        self.visit_attribute_item(node)
    }

    fn visit_meta_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self
            .code
            .node_text(node.child_by_field(FieldKind::Name).unwrap());

        let span = Span::from_node(self.scope.file_id(), node);

        macro_rules! check_duplicate {
            ($attr:pat) => {
                if self.attributes.iter().any(|a| matches!(a, $attr)) {
                    return Err(CodeErrorKind::DuplicateAttribute(name.to_string()))
                        .with_span_from(&self.scope, node)?;
                }
            };
        }

        match name {
            "align" => {
                check_duplicate!(Attribute::Align(_));

                let align: usize = node
                    .child_by_field(FieldKind::Arguments)
                    .and_then(|n| n.child_by_field(FieldKind::Argument))
                    .map(|n| self.code.node_text(n))
                    .and_then(|f| f.parse().ok())
                    .ok_or(CodeErrorKind::InvalidAttribute)
                    .with_span_from(&self.scope, node)?;

                if align == 1 {
                    self.global_ctx.diag().add_warning(CodeError {
                        kind: CodeErrorKind::Align1,
                        backtrace: vec![Marker::Span(span)],
                    });
                } else if !align.is_power_of_two() {
                    return Err(CodeErrorKind::InvalidAttributeDetail(
                        "alignment must be a power of two".to_string(),
                    ))
                    .with_span_from(&self.scope, node);
                } else {
                    if self
                        .attributes
                        .iter()
                        .any(|a| matches!(a, Attribute::Packed))
                    {
                        return Err(CodeErrorKind::AlignAndPacked)
                            .with_span_from(&self.scope, node);
                    }

                    self.attributes.push(Attribute::Align(align))
                }
            }
            "cold" => {
                check_duplicate!(Attribute::Cold);
                self.attributes.push(Attribute::Cold);
            }
            "transparent" => {
                check_duplicate!(Attribute::Transparent);
                self.attributes.push(Attribute::Transparent);
            }
            "packed" => {
                check_duplicate!(Attribute::Packed);

                if self
                    .attributes
                    .iter()
                    .any(|a| matches!(a, Attribute::Align(_)))
                {
                    return Err(CodeErrorKind::AlignAndPacked).with_span_from(&self.scope, node);
                }

                self.attributes.push(Attribute::Packed);
            }
            "inline" => {
                check_duplicate!(
                    Attribute::Inline | Attribute::AlwaysInline | Attribute::InlineDuringMono
                );
                match node
                    .child_by_field(FieldKind::Arguments)
                    .and_then(|n| n.child_by_field(FieldKind::Argument))
                    .map(|n| self.code.node_text(n))
                {
                    Some("always") => self.attributes.push(Attribute::AlwaysInline),
                    Some("never") => self.attributes.push(Attribute::NoInline),
                    Some("ir") => self.attributes.push(Attribute::InlineDuringMono),
                    None => self.attributes.push(Attribute::Inline),
                    _ => {
                        return Err(CodeErrorKind::InvalidAttribute)
                            .with_span_from(&self.scope, node)
                    }
                }
            }
            "builtin" => {
                check_duplicate!(Attribute::Builtin);
                self.attributes.push(Attribute::Builtin);
            }
            "export" => {
                check_duplicate!(Attribute::Export);
                self.attributes.push(Attribute::Export);
            }
            "thread_local" => {
                check_duplicate!(Attribute::ThreadLocal);
                // We can skip thread-local on programs that are compiled with threads
                // disabled.
                if self.global_ctx.has_flag("threading") {
                    self.attributes.push(Attribute::ThreadLocal)
                }
            }
            "test_main" => self.attributes.push(Attribute::TestMain),
            "link_name" => {
                check_duplicate!(Attribute::LinkName(..));

                let link_name = node
                    .child_by_field(FieldKind::Arguments)
                    .and_then(|n| n.child_by_field(FieldKind::Argument))
                    .ok_or(CodeErrorKind::InvalidAttribute)
                    .with_span_from(&self.scope, node)?;

                let bytes = self.code.node_text(link_name).as_bytes();

                let mut val = [0; 255];
                val.as_mut_slice()[0..bytes.len()].copy_from_slice(bytes);

                self.attributes.push(Attribute::LinkName(bytes.len(), val));
            }
            "test" => {
                self.test_attributes.push(
                    node.child_by_field(FieldKind::Arguments)
                        .map(|s| self.code.node_text(s))
                        .unwrap_or("")
                        .to_string(),
                );
            }
            "cfg" => {
                let mut cfg_visitor = CfgVisitor::new(self.global_ctx.clone(), self.scope.clone());
                if !cfg_visitor.visit(node)? {
                    self.should_skip = true;
                }
            }
            "cfg_attr" => {
                let mut cursor = node.walk();
                let args: Vec<_> = node
                    .child_by_field(FieldKind::Arguments)
                    .map(|a| {
                        a.children_by_field(FieldKind::Argument, &mut cursor)
                            .collect()
                    })
                    .unwrap_or_default();

                if args.len() < 2 {
                    return Err(CodeErrorKind::InvalidAttributeDetail(
                        "cfg_attr requires two arguments".to_string(),
                    ))
                    .with_span_from(&self.scope, node);
                }

                let mut cfg_visitor = CfgVisitor::new(self.global_ctx.clone(), self.scope.clone());
                if cfg_visitor.visit(args[0])? {
                    for arg in args.into_iter().skip(1) {
                        self.visit(arg)?;
                    }
                }
            }
            "must_use" => {
                check_duplicate!(Attribute::MustUse);
                self.attributes.push(Attribute::MustUse);
            }
            "lang" => {
                let lang_type = node
                    .child_by_field(FieldKind::Arguments)
                    .and_then(|n| n.child_by_field(FieldKind::Argument))
                    .ok_or(CodeErrorKind::UnknownLangItem(None))
                    .with_span_from(&self.scope, node)?;

                self.ast.add_lang_item(
                    self.code
                        .node_text(lang_type)
                        .try_into()
                        .with_span_from(&self.scope, node)?,
                    self.item
                        .ok_or(CodeErrorKind::CannotBeALangItem)
                        .with_span_from(&self.scope, node)?,
                );
            }
            _ => {}
        }

        Ok(())
    }

    fn visit_attribute_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        self.visit(node.child_by_field(FieldKind::Inner).unwrap())
    }
}

#[derive(Debug, Clone, Copy)]
enum State {
    Single,
    All,
    Any,
    Not,
}

pub struct CfgVisitor<'ast, 'src> {
    global_ctx: GlobalCtx,
    code: &'src ParseCtx<'src>,
    scope: Scope<'ast, 'src>,
    state: Vec<State>,
}

impl<'ast, 'src> CfgVisitor<'ast, 'src> {
    pub fn new(global_ctx: GlobalCtx, scope: Scope<'ast, 'src>) -> Self {
        CfgVisitor {
            global_ctx,
            code: scope
                .code()
                .expect("cannot run on scope without parse context"),
            scope,
            state: vec![],
        }
    }
}

impl<'ast, 'src> AluminaVisitor<'src> for CfgVisitor<'ast, 'src> {
    type ReturnType = Result<bool, AluminaError>;

    fn visit_meta_item(&mut self, node: Node<'src>) -> Self::ReturnType {
        let name = self
            .code
            .node_text(node.child_by_field(FieldKind::Name).unwrap());

        if let Some(arguments) = node.child_by_field(FieldKind::Arguments) {
            let ret = match name {
                "cfg" => {
                    self.state.push(State::Single);
                    self.visit(arguments)?
                }
                "all" => {
                    self.state.push(State::All);
                    self.visit(arguments)?
                }
                "any" => {
                    self.state.push(State::Any);
                    self.visit(arguments)?
                }
                "not" => {
                    self.state.push(State::Not);
                    self.visit(arguments)?
                }
                _ => return Err(CodeErrorKind::InvalidAttribute).with_span_from(&self.scope, node),
            };
            self.state.pop();
            Ok(ret)
        } else {
            let expected = node
                .child_by_field(FieldKind::Value)
                .map(|n| self.code.node_text(n))
                .map(parse_string_literal)
                .transpose()
                .with_span_from(&self.scope, node)?;

            let actual = self.global_ctx.cfg(name);

            let matches = match (expected, actual) {
                (Some(value), Some(Some(cfg))) => cfg == std::str::from_utf8(&value).unwrap(),
                (Some(_), Some(None)) => false,
                (None, Some(_)) => true,
                (_, None) => false,
            };

            Ok(matches)
        }
    }

    fn visit_meta_arguments(&mut self, node: tree_sitter::Node<'src>) -> Self::ReturnType {
        let mut cursor = node.walk();
        let state = *self.state.last().unwrap();
        let mut iter = node.children_by_field(FieldKind::Argument, &mut cursor);

        while let Some(child) = iter.next() {
            let matches = self.visit(child)?;
            match state {
                State::Single | State::Not => {
                    if iter.next().is_some() {
                        return Err(CodeErrorKind::InvalidAttribute)
                            .with_span_from(&self.scope, node);
                    }
                    return Ok(matches == matches!(state, State::Single));
                }
                State::All => {
                    if !matches {
                        return Ok(false);
                    }
                }
                State::Any => {
                    if matches {
                        return Ok(true);
                    }
                }
            }
        }

        match state {
            State::Single | State::Not => {
                Err(CodeErrorKind::InvalidAttribute).with_span_from(&self.scope, node)
            }
            State::All => Ok(true),
            State::Any => Ok(false),
        }
    }
}
