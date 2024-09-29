const PREC = {
  universal_macro: 16,
  call: 15,
  field: 14,
  try: 13,
  unary: 12,
  cast: 11,
  multiplicative: 10,
  additive: 9,
  shift: 8,
  bitand: 7,
  bitxor: 6,
  bitor: 5,
  comparative: 4,
  and: 3,
  or: 2,
  range: 1,
  assign: 0,
  closure: -1,
  et_cetera: -2,
};

const integer_types = [
  "u8",
  "i8",
  "u16",
  "i16",
  "u32",
  "i32",
  "u64",
  "i64",
  "u128",
  "i128",
  "isize",
  "usize",
];

const float_types = ["f32", "f64"];

const primitive_types = integer_types
  .concat(float_types)
  .concat(["bool", "void"]);

function sepBy1(sep, rule) {
  return seq(rule, repeat(seq(sep, rule)));
}

function sepBy(sep, rule) {
  return optional(sepBy1(sep, rule));
}

module.exports = grammar({
  name: "alumina",
  extras: ($) => [
    $.file_doc_comment,
    $.doc_comment,
    $.block_comment,
    $.line_comment,
    /[\s]+/,
  ],

  word: ($) => $.identifier,
  inline: ($) => [
    $._path,
    $._type_identifier,
    $._field_identifier,
    $._expression_ending_with_block,
  ],

  rules: {
    source_file: ($) =>
      seq(
        optional(field("attributes", $.top_level_attributes)),
        repeat(field("body", $._top_level_item))
      ),

    doc_comment: ($) => token(seq("///", /[^\n\r]*/)),
    file_doc_comment: ($) => token(seq("//!", /[^\n\r]*/)),
    line_comment: ($) => token(seq("//", /.*/)),
    block_comment: ($) => token(seq("/*", /[^*]*\*+([^/*][^*]*\*+)*/, "/")),

    top_level_attributes: ($) => repeat1($.top_level_attribute_item),
    top_level_attribute_item: ($) =>
      seq("#!", "[", field("inner", $.meta_item), "]"),

    attributes: ($) => repeat1($.attribute_item),
    attribute_item: ($) => seq("#", "[", field("inner", $.meta_item), "]"),
    meta_item: ($) =>
      seq(
        field("name", $._path),
        optional(
          choice(
            seq(
              "=",
              field("value", choice($.string_literal, $.integer_literal))
            ),
            field("arguments", $.meta_arguments)
          )
        )
      ),
    meta_arguments: ($) =>
      seq(
        "(",
        sepBy(
          ",",
          field(
            "argument",
            choice($.meta_item, $.string_literal, $.integer_literal)
          )
        ),
        optional(","),
        ")"
      ),

    _top_level_item: ($) =>
      choice(
        $.doc_comment,
        $.file_doc_comment,
        $.use_declaration,
        $.function_definition,
        $.struct_definition,
        $.static_declaration,
        $.enum_definition,
        $.protocol_definition,
        $.type_definition,
        $.impl_block,
        $.mod_definition,
        $.macro_definition,
        $.const_declaration,
        $.top_level_block
      ),

    top_level_block: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "{",
        repeat(field("items", $._top_level_item)),
        "}"
      ),

    _impl_item: ($) =>
      choice($.doc_comment, $.use_declaration, $.function_definition, $.mixin),

    _protocol_item: ($) =>
      choice($.doc_comment, $.use_declaration, $.function_definition),

    mod_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "mod",
        field("name", $.identifier),
        "{",
        field("body", repeat($._top_level_item)),
        "}"
      ),

    function_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        optional(
          seq(field("extern", "extern"), field("abi", $.string_literal))
        ),
        "fn",
        field("coroutine", optional("*")),
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        field("parameters", $.parameter_list),
        optional(seq("->", field("return_type", $._type))),
        choice(field("body", $.block), ";")
      ),

    macro_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "macro",
        field("name", $.identifier),
        field("parameters", $.macro_parameter_list),
        field("body", $.block)
      ),

    macro_parameter_list: ($) =>
      seq(
        "(",
        sepBy(",", field("parameter", $.macro_parameter)),
        optional(","),
        ")"
      ),

    macro_parameter: ($) =>
      seq(
        field("name", $.macro_identifier),
        optional(field("et_cetera", "..."))
      ),

    struct_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        field("kind", choice("struct", "union")),
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        "{",
        sepBy(",", field("body", $.struct_field)),
        optional(","),
        "}"
      ),

    protocol_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        field("kind", "protocol"),
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        "{",
        field("body", repeat($._protocol_item)),
        "}"
      ),

    mixin: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "mixin",
        optional(field("type_arguments", $.generic_argument_list)),
        field("protocol", $._type),
        ";"
      ),

    type_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "type",
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        optional(seq("=", field("inner", $._type))),
        ";"
      ),

    enum_definition: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "enum",
        field("name", $.identifier),
        seq("{", sepBy(",", field("body", $.enum_item)), optional(","), "}")
      ),

    enum_item: ($) =>
      seq(
        repeat(field("docstring", $.doc_comment)),
        optional(field("attributes", $.attributes)),
        field("name", $.identifier),
        optional(seq("=", field("value", $._expression)))
      ),

    struct_field: ($) =>
      seq(
        repeat(field("docstring", $.doc_comment)),
        optional(field("attributes", $.attributes)),
        field("name", $.identifier),
        ":",
        field("type", $._type)
      ),

    impl_block: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "impl",
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        "{",
        field("body", repeat($._impl_item)),
        "}"
      ),

    use_declaration: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "use",
        field("argument", $._use_clause),
        ";"
      ),

    use_wildcard: ($) => seq(field("path", $._path), "::", "*"),

    _use_clause: ($) =>
      choice(
        $._path,
        $.use_as_clause,
        $.use_list,
        $.scoped_use_list,
        $.use_wildcard
      ),

    use_as_clause: ($) =>
      seq(field("path", $._path), "as", field("alias", $.identifier)),

    use_list: ($) =>
      seq(
        "{",
        sepBy(",", field("item", choice($._use_clause))),
        optional(","),
        "}"
      ),

    scoped_use_list: ($) =>
      seq(field("path", optional($._path)), "::", field("list", $.use_list)),

    parameter: ($) =>
      seq(field("name", $.identifier), ":", field("type", $._type)),

    protocol_bound: ($) =>
      seq(optional(field("negated", "!")), field("type", $._type)),

    generic_argument: ($) =>
      seq(
        field("placeholder", $.identifier),
        optional(
          seq(
            ":",
            choice(
              field("all_bounds", sepBy("+", field("bound", $.protocol_bound))),
              field("any_bounds", sepBy("|", field("bound", $.protocol_bound)))
            )
          )
        ),
        optional(seq("=", field("default", $._type)))
      ),

    generic_argument_list: ($) =>
      seq(
        "<",
        sepBy(",", field("argument", $.generic_argument)),
        optional(","),
        alias(token(prec(1, ">")), ">")
      ),

    parameter_list: ($) =>
      seq(
        "(",
        sepBy(
          ",",
          choice(field("et_cetera", "..."), field("parameter", $.parameter))
        ),
        optional(","),
        ")"
      ),

    parameter_type_list: ($) =>
      seq("(", sepBy(",", field("parameter", $._type)), optional(","), ")"),

    pointer_of: ($) =>
      prec.left(
        PREC.unary,
        seq("&", optional(field("mut", "mut")), field("inner", $._type))
      ),

    tuple_index_of: ($) =>
      prec.left(
        PREC.field,
        seq(
          field("inner", $._type),
          ".",
          field("index", $.tuple_index_expression)
        )
      ),

    et_cetera_of: ($) =>
      prec.right(PREC.et_cetera, seq(field("inner", $._type), "...")),

    deref_of: ($) => prec.left(PREC.unary, seq("*", field("inner", $._type))),

    slice_of: ($) =>
      seq(
        "&",
        optional(field("mut", "mut")),
        "[",
        field("inner", $._type),
        "]"
      ),

    dyn_of: ($) =>
      seq(
        "&",
        optional(field("mut", "mut")),
        "dyn",
        choice(
          field("inner", $._type),
          seq(
            "(",
            field("inner", $._type),
            "+",
            sepBy1("+", field("inner", $._type)),
            ")"
          )
        )
      ),

    array_of: ($) =>
      seq("[", field("inner", $._type), ";", field("size", $._expression), "]"),

    array_expression: ($) =>
      seq(
        "[",
        choice(seq(sepBy(",", field("element", $._expression)), optional(","))),
        "]"
      ),

    function_pointer: ($) =>
      seq(
        "fn",
        field("parameters", $.parameter_type_list),
        optional(seq("->", field("return_type", $._type)))
      ),

    function_protocol: ($) =>
      seq(
        "Fn",
        field("parameters", $.parameter_type_list),
        optional(seq("->", field("return_type", $._type)))
      ),

    type_arguments: ($) =>
      seq(
        token(prec(1, "<")),
        sepBy1(",", field("type", $._type)),
        optional(","),
        ">"
      ),

    _type: ($) =>
      choice(
        $.scoped_type_identifier,
        $._type_identifier,
        alias(choice(...primitive_types), $.primitive_type),
        $.never_type,
        $.pointer_of,
        $.generic_type,
        $.slice_of,
        $.dyn_of,
        $.array_of,
        $.tuple_type,
        $.function_pointer,
        $.function_protocol,
        $.et_cetera_of,
        $.tuple_index_of,
        $.deref_of,
        $.type_of,
        $.when_type
      ),

    type_of: ($) => seq("typeof", "(", field("inner", $._expression), ")"),

    never_type: ($) => "!",

    tuple_type: ($) =>
      seq("(", sepBy(",", field("element", $._type)), optional(","), ")"),

    block: ($) =>
      seq(
        "{",
        repeat(field("statements", $.statement)),
        optional(field("result", $._expression)),
        "}"
      ),

    let_declaration: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        "let",
        choice(
          field("name", $.identifier),
          seq(
            "(",
            sepBy(",", field("element", $.identifier)),
            optional(","),
            ")"
          )
        ),
        optional(seq(":", field("type", $._type))),
        optional(seq("=", field("value", $._expression))),
        ";"
      ),

    static_declaration: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        optional(
          seq(field("extern", "extern"), field("abi", $.string_literal))
        ),
        "static",
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        optional(seq(":", field("type", $._type))),
        optional(seq("=", field("init", $._expression))),
        ";"
      ),

    const_declaration: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        optional(
          seq(field("extern", "extern"), field("abi", $.string_literal))
        ),
        "const",
        field("name", $.identifier),
        optional(field("type_arguments", $.generic_argument_list)),
        optional(seq(":", field("type", $._type))),
        seq("=", field("init", $._expression)),
        ";"
      ),

    statement: ($) =>
      seq(
        field("inner", choice($._declaration_statement, $.expression_statement))
      ),

    empty_statement: ($) => ";",

    _declaration_statement: ($) =>
      choice(
        $.let_declaration,
        $.use_declaration,
        $.const_declaration,
        $.function_definition,
        $.static_declaration,
        $.struct_definition,
        $.enum_definition,
        $.protocol_definition,
        $.type_definition,
        $.impl_block,
        $.macro_definition,
        $.empty_statement
      ),

    expression_statement: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        choice(
          seq(field("inner", $._expression), ";"),
          prec(1, field("inner", $._expression_ending_with_block))
        )
      ),

    return_expression: ($) =>
      choice(
        prec.left(seq("return", field("inner", $._expression))),
        prec(-1, "return")
      ),

    yield_expression: ($) =>
      choice(
        prec.left(seq("yield", field("inner", $._expression))),
        prec(-1, "yield")
      ),

    defer_expression: ($) =>
      prec.left(seq("defer", field("inner", $._expression))),

    arguments: ($) =>
      seq("(", sepBy(",", field("inner", $._expression)), optional(","), ")"),

    macro_arguments: ($) =>
      choice(
        seq("(", sepBy(",", field("inner", $._expression)), optional(","), ")"),
        seq("[", sepBy(",", field("inner", $._expression)), optional(","), "]"),
        seq("{", sepBy(",", field("inner", $._expression)), optional(","), "}")
      ),

    tuple_expression: ($) =>
      choice(
        seq(
          "(",
          seq(field("element", $._expression), ","),
          repeat(seq(field("element", $._expression), ",")),
          optional(field("element", $._expression)),
          ")"
        ),
        seq("(", ")")
      ),

    turbofish: ($) =>
      prec(
        1,
        seq(
          field(
            "function",
            choice($.identifier, $.scoped_identifier, $.field_expression)
          ),
          "::",
          field("type_arguments", $.type_arguments)
        )
      ),

    _expression_except_range: ($) =>
      choice(
        $.return_expression,
        $.yield_expression,
        $.defer_expression,
        $.break_expression,
        $.continue_expression,
        $.unary_expression,
        $.binary_expression,
        $.reference_expression,
        $.dereference_expression,
        $.try_expression,
        $.assignment_expression,
        $.compound_assignment_expr,
        $.type_cast_expression,
        $.type_check_expression,
        $.call_expression,
        $.universal_macro_invocation,
        $.field_expression,
        $.index_expression,
        $.tuple_expression,
        $.array_expression,
        prec.left(1, $.macro_invocation),
        $.et_cetera_expression,
        $.lambda_expression,
        $._literal,
        prec.left($.identifier),
        prec.left($.macro_identifier),
        alias(choice(...primitive_types), $.identifier),
        $.scoped_identifier,
        $.turbofish,
        $.parenthesized_expression,
        $.struct_expression,
        $._expression_ending_with_block
        // TODO: other kinds of expressions
      ),

    _expression: ($) => choice($.range_expression, $._expression_except_range),

    unary_expression: ($) =>
      prec(
        PREC.unary,
        seq(
          field("operator", choice("-", "!", "~")),
          field("value", $._expression)
        )
      ),

    // Those two are special
    reference_expression: ($) =>
      prec(PREC.unary, seq("&", field("value", $._expression))),

    dereference_expression: ($) =>
      prec(PREC.unary, seq("*", field("value", $._expression))),

    try_expression: ($) =>
      prec(PREC.try, seq(field("inner", $._expression), "?")),

    binary_expression: ($) => {
      const table = [
        [PREC.and, "&&"],
        [PREC.or, "||"],
        [PREC.bitand, "&"],
        [PREC.bitor, "|"],
        [PREC.bitxor, "^"],
        [PREC.comparative, choice("==", "!=", "<", "<=", ">", ">=")],
        [PREC.shift, choice("<<", ">>")],
        [PREC.additive, choice("+", "-")],
        [PREC.multiplicative, choice("*", "/", "%")],
      ];

      return choice(
        ...table.map(([precedence, operator]) =>
          prec.left(
            precedence,
            seq(
              field("left", $._expression),
              field("operator", operator),
              field("right", $._expression)
            )
          )
        )
      );
    },

    field_expression: ($) =>
      prec.left(
        PREC.field,
        seq(
          field("value", $._expression),
          ".",
          choice(
            field("field", $.identifier),
            field("field", $.tuple_index_expression)
          )
        )
      ),

    tuple_index_expression: ($) =>
      choice(
        field("field", $.integer_literal),
        seq("(", field("field", $._expression), ")")
      ),

    universal_macro_invocation: ($) =>
      prec(
        PREC.universal_macro,
        seq(
          field("value", $._expression),
          ".",
          field("macro", $.identifier),
          "!",
          field("arguments", $.macro_arguments)
        )
      ),

    assignment_expression: ($) =>
      prec.left(
        PREC.assign,
        seq(field("left", $._expression), "=", field("right", $._expression))
      ),

    index_expression: ($) =>
      prec(
        PREC.call,
        seq(
          field("value", $._expression),
          "[",
          field("index", $._expression),
          "]"
        )
      ),

    range_expression: ($) =>
      prec.left(
        PREC.range,
        choice(
          seq(
            field("lower", $._expression),
            field("inclusive", choice("..", "..=")),
            field("upper", $._expression)
          ),
          seq(field("lower", $._expression), ".."),
          seq(
            field("inclusive", choice("..", "..=")),
            field("upper", $._expression)
          ),
          ".."
        )
      ),

    compound_assignment_expr: ($) =>
      prec.left(
        PREC.assign,
        seq(
          field("left", $._expression),
          field(
            "operator",
            choice("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=")
          ),
          field("right", $._expression)
        )
      ),

    type_cast_expression: ($) =>
      prec(
        PREC.cast,
        seq(field("value", $._expression), "as", field("type", $._type))
      ),

    type_check_expression: ($) =>
      prec(
        PREC.cast,
        seq(field("value", $._expression), "is", field("type", $._type))
      ),

    call_expression: ($) =>
      prec(
        PREC.call,
        seq(
          field("function", $._expression_except_range),
          field("arguments", $.arguments)
        )
      ),

    macro_invocation: ($) =>
      prec.left(
        1,
        seq(
          field("macro", $._expression_except_range),
          "!",
          field("arguments", $.macro_arguments)
        )
      ),

    struct_initializer_item: ($) =>
      seq(field("field", $.identifier), ":", field("value", $._expression)),

    scoped_identifier: ($) =>
      seq(
        field(
          "path",
          optional(
            choice(
              $._path,
              alias($.generic_type_with_turbofish, $.generic_type)
            )
          )
        ),
        "::",
        field("name", $.identifier)
      ),

    generic_type: ($) =>
      prec(
        1,
        seq(
          field("type", choice($._type_identifier, $.scoped_type_identifier)),
          field("type_arguments", $.type_arguments)
        )
      ),

    scoped_type_identifier_in_expression_position: ($) =>
      prec(
        -2,
        seq(
          field(
            "path",
            optional(
              choice(
                $._path,
                alias($.generic_type_with_turbofish, $.generic_type)
              )
            )
          ),
          "::",
          field("name", $._type_identifier)
        )
      ),

    generic_type_with_turbofish: ($) =>
      seq(
        field("type", choice($._type_identifier, $.scoped_identifier)),
        "::",
        field("type_arguments", $.type_arguments)
      ),

    scoped_type_identifier: ($) =>
      seq(
        field(
          "path",
          optional(
            choice(
              $._path,
              alias($.generic_type_with_turbofish, $.generic_type),
              $.generic_type
            )
          )
        ),
        "::",
        field("name", $._type_identifier)
      ),

    _type_identifier: ($) => alias($.identifier, $.type_identifier),
    _type_identifier: ($) => alias($.identifier, $.type_identifier),
    _field_identifier: ($) => alias($.identifier, $.field_identifier),

    _path: ($) =>
      choice(
        alias(choice(...primitive_types), $.identifier),
        $.identifier,
        $.macro_identifier,
        $.scoped_identifier
      ),

    struct_initializer: ($) =>
      seq(
        "{",
        sepBy(",", field("item", $.struct_initializer_item)),
        optional(","),
        "}"
      ),

    struct_expression: ($) =>
      seq(
        field(
          "name",
          choice(
            $._type_identifier,
            alias(
              $.scoped_type_identifier_in_expression_position,
              $.scoped_type_identifier
            ),
            $.generic_type_with_turbofish
          )
        ),
        field("arguments", $.struct_initializer)
      ),

    parenthesized_expression: ($) =>
      seq("(", field("inner", $._expression), ")"),

    _expression_ending_with_block: ($) =>
      choice(
        $.block,
        $.if_expression,
        $.switch_expression,
        $.while_expression,
        $.loop_expression,
        $.for_expression,
        $.static_for_expression
      ),

    if_expression: ($) =>
      seq(
        field("kind", choice("if", "when")),
        field("condition", $._expression),
        field("consequence", $.block),
        optional(field("alternative", $.else_clause))
      ),

    when_type: ($) =>
      seq(
        "when",
        field("condition", $._expression),
        "{",
        field("consequence", $._type),
        "}",
        "else",
        choice(
          seq("{", field("alternative", $._type), "}"),
          field("alternative", $.when_type)
        )
      ),

    switch_arm: ($) =>
      seq(
        field("pattern", $.pattern),
        "=>",
        choice(
          seq(field("value", $._expression), ","),
          field("value", prec(1, $._expression_ending_with_block))
        )
      ),

    last_switch_arm: ($) =>
      seq(
        field("pattern", $.pattern),
        "=>",
        field("value", $._expression),
        optional(",")
      ),

    pattern: ($) => choice(sepBy1(",", field("value", $._expression)), "_"),

    switch_expression: ($) =>
      seq(
        "switch",
        field("value", $._expression),
        field("body", $.switch_body)
      ),

    switch_body: ($) =>
      seq(
        "{",
        optional(
          seq(
            repeat(field("arm", $.switch_arm)),
            field("arm", alias($.last_switch_arm, $.switch_arm))
          )
        ),
        "}"
      ),

    else_clause: ($) =>
      seq("else", field("inner", choice($.block, $.if_expression))),

    while_expression: ($) =>
      seq("while", field("condition", $._expression), field("body", $.block)),

    break_expression: ($) =>
      prec.right(seq("break", field("inner", optional($._expression)))),

    continue_expression: ($) => "continue",

    loop_expression: ($) => seq("loop", field("body", $.block)),

    et_cetera_expression: ($) =>
      prec.right(
        PREC.et_cetera,
        seq(
          field("inner", $._expression),
          choice(field("tuple", "..."), field("macro", "$..."))
        )
      ),

    static_for_expression: ($) =>
      seq(
        "for",
        "const",
        choice(
          field("name", $.identifier),
          seq(
            "(",
            sepBy(",", field("element", $.identifier)),
            optional(","),
            ")"
          )
        ),
        "in",
        field("value", $._expression),
        field("body", $.block)
      ),

    for_expression: ($) =>
      seq(
        "for",
        choice(
          field("name", $.identifier),
          seq(
            "(",
            sepBy(",", field("element", $.identifier)),
            optional(","),
            ")"
          )
        ),
        "in",
        field("value", $._expression),
        field("body", $.block)
      ),

    _literal: ($) =>
      choice(
        $.string_literal,
        $.char_literal,
        $.boolean_literal,
        $.integer_literal,
        $.float_literal,
        $.ptr_literal
      ),

    integer_literal: ($) =>
      token(
        seq(
          optional("-"),
          choice(/[0-9][0-9]*/, /0x[0-9a-fA-F]+/, /0b[01]+/, /0o[0-7]+/),
          optional(choice(...integer_types))
        )
      ),

    float_literal: ($) =>
      token(
        seq(
          optional("-"),
          choice(
            seq(
              /([0-9][0-9]*)?(\.[0-9]+)([Ee][+\\-]?([0-9][0-9]*))?/,
              optional(choice(...float_types))
            ),
            seq(
              /([0-9][0-9]*)(\.[0-9]+)?([Ee][+\\-]?([0-9][0-9]*))?/,
              choice(...float_types)
            )
          )
        )
      ),

    lambda_expression: ($) =>
      prec(
        PREC.closure,
        seq(
          field("parameters", $.closure_parameters),
          seq(
            optional(seq("->", field("return_type", $._type))),
            field("body", $.block)
          )
        )
      ),

    closure_parameters: ($) =>
      seq(
        "|",
        sepBy(",", field("parameter", choice($.bound_identifier, $.parameter))),
        "|"
      ),

    bound_identifier: ($) =>
      seq(
        choice(field("by_reference", "&"), field("by_value", "=")),
        field("name", $.identifier)
      ),

    string_literal: ($) =>
      token(
        seq(
          '"',
          repeat(
            choice(
              seq(
                "\\",
                choice(
                  /[^xu]/,
                  /u[0-9a-fA-F]{4}/,
                  /u\{[0-9a-fA-F]+\}/,
                  /x[0-9a-fA-F]{2}/
                )
              ),
              /[^"\\\n]+/
            )
          ),
          '"'
        )
      ),

    char_literal: ($) =>
      token(
        seq(
          "'",
          choice(
            seq(
              "\\",
              choice(
                /[^xu]/,
                /u[0-9a-fA-F]{4}/,
                /u\{[0-9a-fA-F]+\}/,
                /x[0-9a-fA-F]{2}/
              )
            ),
            /[^'\\\n]+/
          ),
          "'"
        )
      ),

    boolean_literal: ($) => choice("true", "false"),
    ptr_literal: ($) => "null",
    identifier: ($) => /[_\p{XID_Start}][_\p{XID_Continue}]*/,
    macro_identifier: ($) => /\$[_\p{XID_Start}][_\p{XID_Continue}]*/,
  },
});
