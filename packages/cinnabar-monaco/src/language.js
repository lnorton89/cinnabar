// The Cinnabar language surface: keywords, builtins, and the shapes an
// identifier may take.
//
// One definition, consumed by the Monarch tokenizer next door and by
// anything else that needs to know what a keyword is. It is checked against
// the compiler's own `KEYWORDS` table in `src/analysis.rs` by
// `test/drift.test.js`, so a keyword added to or removed from the language
// fails a test here rather than silently leaving this file describing a
// language that no longer exists.

/**
 * Every keyword the compiler recognizes.
 *
 * Kept in the compiler's order so a diff against `src/analysis.rs` reads as
 * a diff rather than a reordering.
 */
const KEYWORDS = [
  "fun",
  "val",
  "var",
  "const",
  "if",
  "elif",
  "else",
  "while",
  "match",
  "return",
  "break",
  "continue",
  "end",
  "use",
  "as",
  "pub",
  "impure",
  "nat",
  "try",
  "mod",
  "type",
  "trait",
  "impl",
  "true",
  "false"
];

/**
 * Keywords that steer control flow, for editors that colour those apart
 * from declaration keywords. A subset of `KEYWORDS`, never a second list —
 * `test/drift.test.js` checks that every member is one.
 */
const CONTROL_KEYWORDS = [
  "if",
  "elif",
  "else",
  "while",
  "match",
  "return",
  "break",
  "continue",
  "try",
  "end"
];

/** Keywords that modify a declaration rather than introduce one. */
const MODIFIER_KEYWORDS = ["pub", "impure", "nat", "mut"];

/**
 * The built-in type grid.
 *
 * These are ordinary PascalCase symbols to the compiler — seeded into the
 * symbol table, not lexed as keywords — which is why they are listed
 * separately from `KEYWORDS` and why a user type named the same way would
 * shadow rather than collide.
 */
const BUILTIN_TYPES = [
  "Unit",
  "Bool",
  "I8",
  "I16",
  "I32",
  "I64",
  "Isize",
  "U8",
  "U16",
  "U32",
  "U64",
  "Usize",
  "Result",
  "Option",
  "DivError",
  "IndexError",
  "Self"
];

/** The variant constructors every program has without importing them. */
const BUILTIN_CONSTRUCTORS = ["Ok", "Err", "Some", "None"];

/**
 * The three identifier shapes, as anchored patterns.
 *
 * Casing is grammar in Cinnabar, enforced by the lexer: a function, `val`
 * or `var` is snake_case, a type/trait/module/variant is PascalCase, a
 * constant is SCREAMING_SNAKE_CASE. So a tokenizer can classify an
 * identifier by its shape alone, with no symbol table — which is what makes
 * highlighting here semantic rather than a guess.
 */
const IDENTIFIER_PATTERNS = {
  binding: /^[a-z][a-z0-9_]*$/,
  type: /^[A-Z][A-Za-z0-9]*$/,
  constant: /^[A-Z][A-Z0-9_]+$/
};

/** Which of the three shapes `text` has, or "unknown" if it has none. */
function classifyIdentifier(text) {
  if (IDENTIFIER_PATTERNS.constant.test(text)) {
    return "constant";
  }
  if (IDENTIFIER_PATTERNS.type.test(text)) {
    return "type";
  }
  if (IDENTIFIER_PATTERNS.binding.test(text)) {
    return "binding";
  }
  return "unknown";
}

module.exports = {
  KEYWORDS,
  CONTROL_KEYWORDS,
  MODIFIER_KEYWORDS,
  BUILTIN_TYPES,
  BUILTIN_CONSTRUCTORS,
  IDENTIFIER_PATTERNS,
  classifyIdentifier
};
