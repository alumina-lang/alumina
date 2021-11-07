const PREC = {
    range: 15,
    call: 14,
    field: 13,
    unary: 11,
    multiplicative: 10,
    additive: 9,
    shift: 8,
    bitand: 7,
    bitxor: 6,
    bitor: 5,
    comparative: 4,
    and: 3,
    or: 2,
    assign: 0,
    closure: -1,
};

const integer_types = [
    'u8',
    'i8',
    'u16',
    'i16',
    'u32',
    'i32',
    'u64',
    'i64',
    'u128',
    'i128',
    'isize',
    'usize',
];

const float_types = [
    'f32',
    'f64'
];

const primitive_types = integer_types.concat(float_types).concat(['bool', 'str', 'void']);

function sepBy1(sep, rule) {
    return seq(rule, repeat(seq(sep, rule)))
}

function sepBy(sep, rule) {
    return optional(sepBy1(sep, rule))
}

module.exports = grammar({
    name: "alumina",
    extras: $ => [
        $._comment,
        /[\s]+/,
    ],

    word: $ => $.identifier,

    inline: $ => [
        $._path,
        $._type_identifier,
        $._field_identifier,
        $._non_special_token,
        $._expression_ending_with_block
    ],

    rules: {
        source_file: $ => repeat($._top_level_item),

        _non_special_token: $ => choice(
            $._literal, $.identifier,
            alias(choice(...primitive_types), $.primitive_type),
            /[/_\-=->,;:::!=?.@*&#%^+<>|~]+/,
            'as', 'break', 'const', 'continue', 'enum', 'fn', 'for', 'if',
            'let', 'loop', 'match', 'return', 'static', 'struct', 'type',
            'union', 'use', 'where', 'while', 'impl'
        ),

        _comment: $ => token(choice(
            seq('//', /[^\n\r]*/),
            seq(
                '/*',
                /[^*]*\*+([^/*][^*]*\*+)*/,
                '/'
            )
        )),

        attribute: $ => seq(
            '#[',
            sepBy1(',', $.identifier),
            ']'
        ),

        _top_level_item: $ => choice(
            $.function_definition,
            $.struct_definition,
            $.enum_definition,
            $.impl_block,
        ),

        function_definition: $ => seq(
            optional($.attribute),
            'fn',
            $.identifier,
            optional($.generic_argument_list),
            $.parameter_list,
            optional(seq(
                '->',
                field('return_type', $._type)
            )),
            field("body", $.block)
        ),

        struct_definition: $ => seq(
            optional($.attribute),
            'struct',
            $.identifier,
            optional($.generic_argument_list),
            $.struct_body
        ),

        impl_block: $ => seq(
            optional($.attribute),
            'impl',
            $.identifier,
            optional($.generic_argument_list),
            '{',
            repeat($.function_definition),
            '}'
        ),

        enum_definition: $ => seq(
            optional($.attribute),
            'enum',
            $.identifier,
            $.enum_body
        ),

        enum_body: $ => seq(
            '{',
            sepBy(',', $.identifier),
            optional(','),
            '}'
        ),

        struct_body: $ => seq(
            '{',
            sepBy(',', $.parameter),
            optional(','),
            '}'
        ),

        parameter: $ => seq(
            $.identifier,
            ":",
            $._type
        ),

        generic_argument_list: $ => seq(
            '<',
            sepBy(',', $.identifier),
            optional(','),
            alias(token(prec(1, '>')), '>')
        ),

        parameter_list: $ => seq(
            '(',
            sepBy(',', $.parameter),
            optional(','),
            ')'
        ),

        pointer_of: $ => seq(
            '&',
            $._type
        ),

        slice_of: $ => seq(
            '[',
            $._type,
            ']'
        ),

        array_of: $ => seq(
            '[',
            $._type,
            ';',
            $.integer_literal,
            ']'
        ),

        anonymous_struct: $ => seq(
            'struct',
            $.struct_body
        ),

        function_pointer: $ => seq(
            'fn',
            $.parameter_list,
            optional(seq('->', field('return_type', $._type))),
        ),

        type_arguments: $ => seq(
            token(prec(1, '<')),
            sepBy1(',', choice(
                $._type,
                $._literal,
                $.block,
            )),
            optional(','),
            '>'
        ),

        _type: $ => choice(
            $.scoped_type_identifier,
            $._type_identifier,
            alias(choice(...primitive_types), $.primitive_type),
            $.pointer_of,
            $.generic_type,
            $.slice_of,
            $.array_of,
            $.tuple_type,
            $.anonymous_struct,
            $.function_pointer,
        ),

        tuple_type: $ => seq(
            '(',
            sepBy(',', $._expression),
            optional(','),
            ')'
        ),

        block: $ => seq(
            '{',
            repeat($._statement),
            optional($._expression),
            '}'
        ),

        letiable_declaration: $ => seq(
            'let',
            $.identifier,
            choice(
                seq(
                    ':',
                    $._type,
                ),
                seq(
                    '=',
                    $._expression,
                ),
                seq(
                    ':',
                    $._type,
                    '=',
                    $._expression,
                ),
            ),
            ';'
        ),

        _statement: $ => choice(
            $._declaration_statement,
            $._expression_statement
        ),

        empty_statement: $ => ';',

        _declaration_statement: $ => choice(
            $.letiable_declaration,
            $.empty_statement
        ),

        _expression_statement: $ => choice(
            seq($._expression, ';'),
            prec(1, $._expression_ending_with_block)
        ),

        return_expression: $ => choice(
            prec.left(seq('return', $._expression)),
            prec(-1, 'return'),
        ),

        arguments: $ => seq(
            '(',
            sepBy(',', $._expression),
            optional(','),
            ')'
        ),

        tuple_expression: $ => seq(
            '(',
            seq($._expression, ','),
            repeat(seq($._expression, ',')),
            optional($._expression),
            ')'
        ),

        generic_function: $ => prec(1, seq(
            field('function', choice(
                $.identifier,
                $.scoped_identifier,
                $.field_expression
            )),
            '::',
            field('type_arguments', $.type_arguments)
        )),

        _expression: $ => choice(
            $.return_expression,
            $.unary_expression,
            $.binary_expression,
            $.reference_expression,
            $.assignment_expression,
            $.compound_assignment_expr,
            $.type_cast_expression,
            $.call_expression,
            $.struct_expression,
            $.field_expression,
            $.index_expression,
            $.tuple_expression,
            $._expression_ending_with_block,
            $._literal,
            prec.left($.identifier),
            alias(choice(...primitive_types), $.identifier),
            $.scoped_identifier,
            $.generic_function,
            $._parenthesized_expression,
            // TODO: other kinds of expressions
        ),

        unary_expression: $ => prec(PREC.unary, seq(
            choice('-', '*', '!'),
            $._expression
        )),

        reference_expression: $ => prec(PREC.unary, seq(
            '&',
            field('value', $._expression)
        )),

        binary_expression: $ => {
            const table = [
                [PREC.and, '&&'],
                [PREC.or, '||'],
                [PREC.bitand, '&'],
                [PREC.bitor, '|'],
                [PREC.bitxor, '^'],
                [PREC.comparative, choice('==', '!=', '<', '<=', '>', '>=')],
                [PREC.shift, choice('<<', '>>')],
                [PREC.additive, choice('+', '-')],
                [PREC.multiplicative, choice('*', '/', '%')],
            ];

            return choice(...table.map(([precedence, operator]) => prec.left(precedence, seq(
                field('left', $._expression),
                field('operator', operator),
                field('right', $._expression),
            ))));
        },

        field_expression: $ => prec(PREC.field, seq(
            field('value', $._expression),
            '.',
            field('field', choice(
                $.identifier,
                $.integer_literal
            ))
        )),

        assignment_expression: $ => prec.left(PREC.assign, seq(
            field('left', $._expression),
            '=',
            field('right', $._expression)
        )),

        index_expression: $ => prec(PREC.call, seq($._expression, '[', $._expression, ']')),

        compound_assignment_expr: $ => prec.left(PREC.assign, seq(
            field('left', $._expression),
            field('operator', choice('+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=')),
            field('right', $._expression)
        )),

        type_cast_expression: $ => seq(
            field('value', $._expression),
            'as',
            field('type', $._type)
        ),

        call_expression: $ => prec(PREC.call, seq(
            field('function', $._expression),
            field('arguments', $.arguments)
        )),

        struct_initializer_item: $ => seq(
            $.identifier,
            ":",
            $._expression
        ),

        scoped_identifier: $ => seq(
            field('path', optional(choice(
                $._path,
                alias($.generic_type_with_turbofish, $.generic_type)
            ))),
            '::',
            field('name', $.identifier)
        ),

        generic_type: $ => prec(1, seq(
            field('type', choice(
                $._type_identifier,
                $.scoped_type_identifier
            )),
            field('type_arguments', $.type_arguments)
        )),

        scoped_type_identifier_in_expression_position: $ => prec(-2, seq(
            field('path', optional(choice(
                $._path,
                alias($.generic_type_with_turbofish, $.generic_type)
            ))),
            '::',
            field('name', $._type_identifier)
        )),

        generic_type_with_turbofish: $ => seq(
            field('type', choice(
                $._type_identifier,
                $.scoped_identifier
            )),
            '::',
            field('type_arguments', $.type_arguments)
        ),

        scoped_type_identifier: $ => seq(
            field('path', optional(choice(
                $._path,
                alias($.generic_type_with_turbofish, $.generic_type),
                $.generic_type
            ))),
            '::',
            field('name', $._type_identifier)
        ),


        _type_identifier: $ => alias($.identifier, $.type_identifier),
        _field_identifier: $ => alias($.identifier, $.field_identifier),

        _path: $ => choice(
            alias(choice(...primitive_types), $.identifier),
            $.identifier,
            $.scoped_identifier,
        ),

        struct_initializer: $ => seq(
            '{',
            sepBy(',', $.struct_initializer_item),
            optional(','),
            '}'
        ),

        struct_expression: $ => prec(PREC.call, seq(
            field('name', choice(
                $._type_identifier,
                alias($.scoped_type_identifier_in_expression_position, $.scoped_type_identifier),
                $.generic_type_with_turbofish
            )),
            field('arguments', $.struct_initializer)
        )),

        _parenthesized_expression: $ => seq(
            '(',
            $._expression,
            ')'
        ),

        _expression_ending_with_block: $ => choice(
            $.block,
            $.if_expression,
            $.while_expression,
            $.loop_expression,
            $.for_expression,
        ),


        if_expression: $ => seq(
            'if',
            field('condition', $._expression),
            field('consequence', $.block),
            optional(field("alternative", $.else_clause))
        ),

        else_clause: $ => seq(
            'else',
            choice(
                $.block,
                $.if_expression,
            )
        ),


        while_expression: $ => seq(
            'while',
            field('condition', $._expression),
            field('body', $.block)
        ),


        loop_expression: $ => seq(
            'loop',
            field('body', $.block)
        ),

        for_expression: $ => seq(
            'for',
            field('start', $._expression),
            ',',
            field('stop', $._expression),
            ',',
            field('step', $._expression),
            field('body', $.block)
        ),

        _literal: $ => choice(
            $.string_literal,
            $.boolean_literal,
            $.integer_literal,
            $.float_literal,
            $.ptr_literal,
        ),

        integer_literal: $ => token(seq(
            choice(
                /[0-9][0-9]*/,
                /0x[0-9a-fA-F]+/,
                /0b[01]+/,
                /0o[0-7]+/
            ),
            optional(choice(...integer_types))
        )),

        float_literal: $ => token(choice(
            seq(
                /([0-9][0-9]*)?(\.[0-9]+)([Ee][+\\-]?([0-9][0-9]*))?/,
                optional(choice(...float_types))
            ),
            seq(
                /([0-9][0-9]*)(\.[0-9]+)?([Ee][+\\-]?([0-9][0-9]*))?/,
                choice(...float_types)
            ))
        ),

        string_literal: $ => token(seq(
            '"',
            repeat(choice(
                seq('\\',
                    choice(
                        /[^xu]/,
                        /u[0-9a-fA-F]{4}/,
                        /u{[0-9a-fA-F]+}/,
                        /x[0-9a-fA-F]{2}/
                    )
                ),
                /[^"\\\n]+/
            )),
            '"'
        )),

        boolean_literal: $ => choice('true', 'false'),
        ptr_literal: $ => choice('null'),
        identifier: $ => /(r#)?[_\p{XID_Start}][_\p{XID_Continue}]*/,
    }
});
