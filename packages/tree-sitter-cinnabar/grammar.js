/**
 * Cinnabar grammar for tree-sitter.
 *
 * Cinnabar has no braces and no semicolons: a block runs to `end`, and a
 * statement runs to the end of its line. That makes the newline a real
 * token rather than whitespace, and it is the one thing this grammar
 * cannot express in rules alone — a newline inside an open bracket is
 * continuation, not a terminator, and a parameter list is routinely spread
 * across lines. `src/scanner.c` tracks bracket depth and emits a newline
 * token only where one actually ends something.
 *
 * The other thing worth knowing when reading this file: casing is grammar
 * here, not convention. The compiler's lexer rejects a mis-cased
 * identifier, so `snake_case`, `PascalCase` and `SCREAMING_SNAKE_CASE` are
 * three distinct terminals, and a highlighter reading this grammar can
 * colour an identifier by what it *is* without a symbol table. Anywhere
 * this file accepts the wrong case it would be claiming the compiler
 * accepts a program it rejects.
 */

const PRECEDENCE = {
  or: 1,
  and: 2,
  comparison: 3,
  bitwise_or: 4,
  bitwise_xor: 5,
  bitwise_and: 6,
  shift: 7,
  additive: 8,
  multiplicative: 9,
  unary: 10,
  try: 11,
  postfix: 12,
};

module.exports = grammar({
  name: "cinnabar",

  externals: ($) => [$._newline, $._arm_start, $._error_sentinel],

  // A newline is an extra *and* an external token. Tree-sitter consults the
  // scanner before skipping extras, so where the grammar permits a
  // terminator the scanner supplies one, and everywhere else — inside a
  // parameter list, an argument list, an array literal — the line break is
  // skipped as the continuation it is. That is what removes the need to
  // track bracket depth, which the scanner cannot do reliably: it is only
  // ever invoked where an external token is valid, so it never sees most of
  // the brackets a program contains.
  extras: ($) => [/[ \t\r\n]/, $.line_comment, $.doc_line_comment, $.block_comment, $.doc_block_comment],

  word: ($) => $.identifier,

  supertypes: ($) => [$._item, $._statement, $._expression, $._pattern, $._type],

  // `f[U8]()` instantiates and `arr[i]` indexes, and a bracket holding a
  // PascalCase name could still be either when the parser reaches the
  // closing bracket — only the argument list that may follow decides. It is
  // resolved by looking further ahead rather than by a rule that would have
  // to guess.
  rules: {
    // The scanner collapses a run of blank lines into one newline token, so
    // every list below separates with exactly one rather than repeating it.
    source_file: ($) => seq(optional($._newline), repeat(seq($._item, $._newline))),

    // ---- comments -------------------------------------------------------
    // `#` always opens one. There is no `#` operator to disambiguate
    // against and no preprocessor, which is why comments can live in
    // `extras` without qualification. Block comments do not nest.
    line_comment: () => token(seq("#", /[^!|\n][^\n]*/)),
    doc_line_comment: () => token(seq("#!", /[^|\n][^\n]*/)),
    block_comment: () => token(seq("#|", repeat(choice(/[^|]/, /\|[^#]/)), "|#")),
    doc_block_comment: () => token(seq("#!|", repeat(choice(/[^|]/, /\|[^#]/)), "|#")),

    // ---- items ----------------------------------------------------------
    _item: ($) =>
      choice(
        $.module_declaration,
        $.use_declaration,
        $.type_declaration,
        $.native_type_declaration,
        $.trait_declaration,
        $.impl_declaration,
        $.function_declaration,
        $.native_function_declaration,
        $.const_declaration,
      ),

    visibility: () => "pub",

    module_declaration: ($) =>
      seq(
        optional($.visibility),
        "mod",
        field("name", $.type_identifier),
        $._newline,
        field("body", repeat(seq($._item, $._newline))),
        "end",
      ),

    use_declaration: ($) =>
      seq(
        optional($.visibility),
        "use",
        field("path", choice($.path, $.type_identifier, $.identifier)),
        optional(seq("as", field("alias", choice($.identifier, $.type_identifier)))),
      ),

    // One `type` keyword introduces both product and sum types: a body of
    // `name: Type` fields is a struct, a body of PascalCase names is an
    // enum. The compiler decides which from the same shape this rule sees.
    type_declaration: ($) =>
      seq(
        optional($.visibility),
        "type",
        field("name", $.type_identifier),
        optional($.type_parameters),
        $._newline,
        field("body", repeat(seq(choice($.field_declaration, $.variant_declaration), $._newline))),
        "end",
      ),

    field_declaration: ($) =>
      seq(optional($.visibility), field("name", $.identifier), ":", field("type", $._type)),

    variant_declaration: ($) =>
      seq(
        optional($.visibility),
        field("name", $.type_identifier),
        optional(seq("(", commaSeparated($._type), ")")),
      ),

    native_type_declaration: ($) =>
      seq(
        optional($.visibility),
        "nat",
        "type",
        field("name", $.type_identifier),
        optional($.type_parameters),
      ),

    trait_declaration: ($) =>
      seq(
        optional($.visibility),
        "trait",
        field("name", $.type_identifier),
        optional($.type_parameters),
        $._newline,
        // Signatures only. A trait method has no body here — the parser
        // treats `fun` inside a trait as opening nothing, so an `impl` is
        // the only place a body may appear.
        field("body", repeat(seq($.function_signature, $._newline))),
        "end",
      ),

    impl_declaration: ($) =>
      seq(
        optional($.visibility),
        "impl",
        field("trait", choice($.path, $.type_identifier)),
        "for",
        field("type", $._type),
        $._newline,
        field("body", repeat(seq($.function_declaration, $._newline))),
        "end",
      ),

    type_parameters: ($) => seq("(", commaSeparated($.type_identifier), ")"),

    // A function's type parameters use angle brackets; a type
    // constructor's use parentheses. They are different syntax for
    // different things and the grammar keeps them apart.
    function_type_parameters: ($) =>
      seq(
        "<",
        commaSeparated(seq(field("name", $.type_identifier), optional(seq(":", field("bound", choice($.path, $.type_identifier)))))),
        ">",
      ),

    function_signature: ($) =>
      seq(
        optional($.visibility),
        "fun",
        field("name", $.identifier),
        optional($.function_type_parameters),
        field("parameters", $.parameters),
        optional($.impure),
        field("return_type", $._type),
      ),

    function_declaration: ($) =>
      seq(field("signature", $.function_signature), $._newline, field("body", optional($.block)), "end"),

    // A native function is a signature and nothing else: it names a surface
    // the runtime provides, so there is no body to give it.
    native_function_declaration: ($) =>
      seq(
        optional($.visibility),
        "nat",
        "fun",
        field("name", $.identifier),
        optional($.function_type_parameters),
        field("parameters", $.parameters),
        optional($.impure),
        field("return_type", $._type),
      ),

    impure: () => "impure",

    parameters: ($) => seq("(", optional(commaSeparated($.parameter)), ")"),

    parameter: ($) => seq(field("name", $.identifier), ":", field("type", $._type)),

    const_declaration: ($) =>
      seq(
        optional($.visibility),
        "const",
        // A one-letter constant is legal SCREAMING_SNAKE_CASE, and a single
        // uppercase letter is equally a legal type name. Nothing in the
        // syntax separates them — the compiler tells them apart by which
        // symbol table the name lands in — so both are accepted here.
        field("name", choice($.constant_identifier, $.type_identifier)),
        ":",
        field("type", $._type),
        "=",
        field("value", $._expression),
      ),

    // ---- types ----------------------------------------------------------
    _type: ($) =>
      choice(
        $.generic_type,
        $.reference_type,
        $.mutable_reference_type,
        $.slice_type,
        $.array_type,
        $.self_type,
        $.path,
        $.type_identifier,
      ),

    self_type: () => "Self",

    generic_type: ($) =>
      seq(field("constructor", choice($.path, $.type_identifier)), "(", commaSeparated($._type), ")"),

    reference_type: ($) => seq("&", field("type", $._type)),
    mutable_reference_type: ($) => seq("&", "mut", field("type", $._type)),
    slice_type: ($) => seq("[", field("element", $._type), "]"),
    array_type: ($) => seq("[", field("element", $._type), ";", field("length", $._expression), "]"),

    // ---- statements -----------------------------------------------------
    // An empty block is legal: an empty function body, an empty `while`
    // body and empty `if`/`else` bodies all compile and lower to Unit.
    block: ($) => repeat1(seq($._statement, $._newline)),

    _statement: ($) =>
      choice(
        $.let_statement,
        $.assignment_statement,
        $.while_statement,
        $.if_statement,
        $.return_statement,
        $.break_statement,
        $.continue_statement,
        $.expression_statement,
      ),

    let_statement: ($) =>
      seq(
        field("kind", choice("val", "var")),
        field("name", $.identifier),
        optional(seq(":", field("type", $._type))),
        "=",
        field("value", $._expression),
      ),

    // An assignment target is a place — a name, a field chain, or an index,
    // possibly through a `&mut` reference — never an arbitrary expression.
    assignment_statement: ($) => seq(field("target", $._callable), "=", field("value", $._expression)),

    while_statement: ($) =>
      seq("while", field("condition", $._expression), $._newline, field("body", optional($.block)), "end"),

    if_statement: ($) =>
      seq(
        "if",
        field("condition", $._expression),
        $._newline,
        field("consequence", optional($.block)),
        repeat(field("alternative", $.elif_clause)),
        optional(field("alternative", $.else_clause)),
        "end",
      ),

    elif_clause: ($) =>
      seq("elif", field("condition", $._expression), $._newline, field("body", optional($.block))),

    else_clause: ($) => seq("else", $._newline, field("body", optional($.block))),

    return_statement: ($) => seq("return", optional(field("value", $._expression))),
    break_statement: () => "break",
    continue_statement: () => "continue",
    // A statement may not be a bare array literal. Allowing one would make
    // the `[` opening the next match arm's array pattern indistinguishable
    // from a statement continuing the arm body above it — and an array
    // literal evaluated for its own sake does nothing anyway, so nothing
    // real is excluded.
    expression_statement: ($) =>
      choice(
        $.call_expression,
        $.struct_expression,
        $.try_expression,
        $.match_expression,
        $.field_expression,
        $.index_expression,
        $.path,
        $.identifier,
        $.type_identifier,
        $.constant_identifier,
        $.integer_literal,
        $.hex_literal,
        $.string_literal,
        $.boolean_literal,
        $.unary_expression,
        $.binary_expression,
        $.parenthesized_expression,
      ),

    // ---- expressions ----------------------------------------------------
    _expression: ($) =>
      choice(
        $.integer_literal,
        $.hex_literal,
        $.string_literal,
        $.boolean_literal,
        $.path,
        $.identifier,
        $.type_identifier,
        $.constant_identifier,
        $.call_expression,
        $.struct_expression,
        $.index_expression,
        $.field_expression,
        $.array_expression,
        $.unary_expression,
        $.binary_expression,
        $.try_expression,
        $.match_expression,
        $.parenthesized_expression,
      ),

    parenthesized_expression: ($) => seq("(", $._expression, ")"),

    // `f[U8]()` is the explicit instantiation form. It is a call whose type
    // arguments were written out rather than inferred, not an index.
    // What can be called, indexed, or have a field taken from it: never a
    // bare array literal, which would put a `[` at statement start and make
    // the next match arm's array pattern unreadable as one.
    //
    // Explicit instantiation — `vec_new[U8]()` — has no rule of its own.
    // Its bracket group holds a type where an index holds a value, and
    // nothing before the `]` distinguishes them, so the grammar reads it as
    // an `index_expression` that is then called. The `U8` is still a
    // `type_identifier` and still highlights as a type; what is lost is only
    // the name of the node above it. Recovering that name would need a
    // `_type`/`_expression` ambiguity declared across the whole grammar,
    // which makes every `Name(...)` constructor call unparseable — a much
    // worse trade for a highlighting and navigation grammar.
    _callable: ($) =>
      choice(
        $.path,
        $.identifier,
        $.type_identifier,
        $.constant_identifier,
        $.call_expression,
        $.index_expression,
        $.field_expression,
        $.struct_expression,
        $.parenthesized_expression,
      ),

    // `Name(` opens either a call or a struct literal, and only what
    // follows tells them apart: a struct literal names its fields. Both
    // readings are carried across the bracket group, and the call wins on
    // dynamic precedence where both complete — which happens only when no
    // field was named, and an unnamed field is not a struct literal.
    call_expression: ($) =>
      prec.dynamic(
        2,
        prec(PRECEDENCE.postfix, seq(field("function", $._callable), field("arguments", $.arguments))),
      ),

    arguments: ($) => seq("(", optional(commaSeparated($._expression)), ")"),

    struct_expression: ($) =>
      prec.dynamic(
        1,
        prec(
          PRECEDENCE.postfix,
          seq(
            field("type", $._callable),
            "(",
            commaSeparated(field("field", $.field_initializer)),
            ")",
          ),
        ),
      ),

    field_initializer: ($) => seq(field("name", $.identifier), ":", field("value", $._expression)),

    index_expression: ($) =>
      prec(
        PRECEDENCE.postfix,
        seq(field("base", $._callable), "[", commaSeparated(field("index", $._expression)), "]"),
      ),

    // A dotted chain of identifiers is a `path`, exactly as the compiler
    // reads it: `header.bytes` and `Collections.EmptySlice` are the same
    // shape, and which one names a field is a question for the resolver.
    // `field_expression` is what the compiler calls field access on a
    // non-path base — the `.len` in `f(x).len`.
    field_expression: ($) =>
      prec(
        PRECEDENCE.postfix,
        seq(
          field(
            "base",
            choice($.call_expression, $.index_expression, $.parenthesized_expression, $.struct_expression, $.field_expression),
          ),
          ".",
          field("field", $.identifier),
        ),
      ),

    array_expression: ($) => seq("[", optional(commaSeparated($._expression)), "]"),

    unary_expression: ($) =>
      prec(
        PRECEDENCE.unary,
        seq(field("operator", choice("-", "!", seq("&", "mut"), "&")), field("operand", $._expression)),
      ),

    try_expression: ($) => prec(PRECEDENCE.try, seq("try", field("value", $._expression))),

    binary_expression: ($) => {
      const table = [
        [PRECEDENCE.or, "||"],
        [PRECEDENCE.and, "&&"],
        [PRECEDENCE.comparison, choice("==", "!=", "<", ">", "<=", ">=")],
        [PRECEDENCE.bitwise_or, "|"],
        [PRECEDENCE.bitwise_xor, "^"],
        [PRECEDENCE.bitwise_and, "&"],
        [PRECEDENCE.shift, choice("<<", ">>")],
        [PRECEDENCE.additive, choice("+", "-")],
        [PRECEDENCE.multiplicative, choice("*", "/", "%")],
      ];
      return choice(
        ...table.map(([precedence, operator]) =>
          prec.left(
            precedence,
            seq(field("left", $._expression), field("operator", operator), field("right", $._expression)),
          ),
        ),
      );
    },

    // A match is exhaustive and `end`-delimited. An arm's body is either a
    // single expression on the same line or statements on the lines after
    // the `=>`.
    match_expression: ($) =>
      seq(
        "match",
        field("value", $._expression),
        $._newline,
        repeat1(field("arm", $.match_arm)),
        "end",
      ),

    // An arm's body is either one statement on the same line as the `=>`
    // — `Ok(value) => return value` is the common shape — or a block on the
    // lines after it. The block already ends each of its statements with a
    // newline, so only the one-line form needs a terminator of its own.
    match_arm: ($) =>
      seq(
        $._arm_start,
        field("pattern", $._pattern),
        "=>",
        field("body", choice(seq($._statement, $._newline), seq($._newline, $.block))),
      ),

    // ---- patterns -------------------------------------------------------
    _pattern: ($) =>
      choice($.variant_pattern, $.array_pattern, $.literal_pattern, $.path, $.type_identifier, $.identifier),

    variant_pattern: ($) =>
      seq(field("variant", choice($.path, $.type_identifier)), "(", optional(commaSeparated($._pattern)), ")"),

    // `[first, rest @ ..]` binds the head and names what is left. The rest
    // binder is a real binding, not a discard: this language has no `_`.
    array_pattern: ($) =>
      seq(
        "[",
        optional(commaSeparated($._pattern)),
        optional(seq(optional(","), field("rest", $.rest_pattern))),
        "]",
      ),

    rest_pattern: ($) => seq(field("name", $.identifier), "@", ".."),

    literal_pattern: ($) => choice($.integer_literal, $.hex_literal, $.boolean_literal, $.string_literal),

    // ---- terminals ------------------------------------------------------
    path: ($) =>
      prec.left(
        seq(
          choice($.type_identifier, $.identifier, $.constant_identifier),
          repeat1(seq(".", choice($.type_identifier, $.identifier, $.constant_identifier))),
        ),
      ),

    // Three identifier shapes, because the compiler enforces three. A
    // grammar that accepted one identifier rule everywhere would accept
    // programs the lexer rejects.
    identifier: () => /[a-z][a-z0-9_]*/,
    type_identifier: () => /[A-Z][A-Za-z0-9]*/,
    constant_identifier: () => /[A-Z][A-Z0-9_]+/,

    integer_literal: () => /[0-9]+/,
    hex_literal: () => /0[xX][0-9a-fA-F]+/,
    boolean_literal: () => choice("true", "false"),
    string_literal: () => token(seq('"', repeat(choice(/[^"\\\n]/, seq("\\", /./))), '"')),
  },
});

function commaSeparated(rule) {
  return seq(rule, repeat(seq(",", rule)), optional(","));
}
