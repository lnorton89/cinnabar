// Cinnabar for Monaco: a Monarch tokenizer and a language configuration.
//
// Monaco tokenizes line by line with a small state machine, so this cannot
// be a parser and does not pretend to be one. It does not have to be:
// casing is grammar in Cinnabar, so an identifier's shape already says
// whether it names a type, a constant, or a binding, and `#` always opens a
// comment — there is no `#` operator to disambiguate against and no
// preprocessor. Those two facts are what let a regular-expression tokenizer
// be accurate here rather than approximate.
//
// What it cannot know is anything the typechecker computes — whether a
// handle is linear, what a name resolved to. Nothing below claims to.

import {
  KEYWORDS,
  CONTROL_KEYWORDS,
  MODIFIER_KEYWORDS,
  BUILTIN_TYPES,
  BUILTIN_CONSTRUCTORS
} from "./language.js";

/** The language id to register Cinnabar under. */
export const LANGUAGE_ID = "cinnabar";

/** What `monaco.languages.register` needs to associate `.cnb` with it. */
export const languageExtensionPoint = {
  id: LANGUAGE_ID,
  extensions: [".cnb"],
  aliases: ["Cinnabar", "cinnabar"],
  mimetypes: ["text/x-cinnabar"]
};

/**
 * Bracket, comment and indentation rules.
 *
 * Blocks end with `end` rather than a closing brace, so the auto-indent
 * rules key on the keywords that open and close one. `elif` and `else`
 * outdent to match the `if` they belong to.
 */
export const languageConfiguration = {
  comments: {
    lineComment: "#",
    blockComment: ["#|", "|#"]
  },
  brackets: [
    ["(", ")"],
    ["[", "]"]
  ],
  autoClosingPairs: [
    { open: "(", close: ")" },
    { open: "[", close: "]" },
    { open: '"', close: '"', notIn: ["string", "comment"] }
  ],
  surroundingPairs: [
    { open: "(", close: ")" },
    { open: "[", close: "]" },
    { open: '"', close: '"' }
  ],
  indentationRules: {
    increaseIndentPattern: /^\s*(pub\s+)?(mod|type|trait|impl|fun|if|elif|else|while|match)\b.*$/,
    decreaseIndentPattern: /^\s*(end|elif|else)\b.*$/
  },
  onEnterRules: [
    {
      // Continue a documentation block comment, which is how a declaration
      // gets the prose the compiler attaches to it.
      beforeText: /^\s*#!\|.*$/,
      action: { indentAction: 0, appendText: "  " }
    }
  ],
  wordPattern: /[A-Za-z][A-Za-z0-9_]*/
};

/**
 * The Monarch tokenizer.
 *
 * Rule order is the whole design. Comments come first because `#` always
 * opens one. Declaration forms come next so that the name after `fun`,
 * `type`, `mod`, `trait` or `const` is coloured as a declaration rather than
 * as whatever its shape would otherwise make it. Then keywords, then the
 * three identifier shapes, in the order that makes the most specific one
 * win: SCREAMING_SNAKE_CASE before PascalCase, because `MAX_PORT` is a
 * constant and not a type.
 */
export const monarchLanguage = {
  defaultToken: "",
  tokenPostfix: ".cnb",
  keywords: KEYWORDS,
  controlKeywords: CONTROL_KEYWORDS,
  modifierKeywords: MODIFIER_KEYWORDS,
  builtinTypes: BUILTIN_TYPES,
  builtinConstructors: BUILTIN_CONSTRUCTORS,

  operators: [
    "+", "-", "*", "/", "%", "<<", ">>", "&", "|", "^", "==", "!=", "<", ">",
    "<=", ">=", "&&", "||", "!", "=", "=>", "@", ".."
  ],

  symbols: /[=><!~?:&|+\-*/^%@.]+/,
  escapes: /\\[nt0"\\]/,

  tokenizer: {
    root: [
      // Comments. `#!|` and `#|` open blocks that run to `|#` and do not
      // nest; `#!` and `#` run to end of line. The documentation forms are
      // distinguished because the compiler attaches them to declarations.
      [/#!\|/, { token: "comment.doc", next: "@docBlock" }],
      [/#\|/, { token: "comment", next: "@block" }],
      [/#!.*$/, "comment.doc"],
      [/#.*$/, "comment"],

      // Declarations: colour the declared name by what is being declared,
      // rather than leaving it to the identifier rules below.
      [/\b(fun)(\s+)([a-z][a-z0-9_]*)/, ["keyword", "white", "entity.name.function"]],
      [/\b(mod|type|trait)(\s+)([A-Z][A-Za-z0-9]*)/, ["keyword", "white", "entity.name.type"]],
      [/\b(const)(\s+)([A-Z][A-Z0-9_]*)/, ["keyword", "white", "constant"]],
      [/\b(val|var)(\s+)([a-z][a-z0-9_]*)/, ["keyword", "white", "variable"]],

      // A call: the name immediately before an open parenthesis.
      [/\b([a-z][a-z0-9_]*)(?=\s*\()/, "entity.name.function"],

      [/[a-z][a-z0-9_]*/, { cases: { "@keywords": "keyword", "@default": "identifier" } }],

      // SCREAMING_SNAKE_CASE first: `MAX_PORT` is a constant, and the
      // PascalCase pattern below would otherwise claim its first segment.
      [/[A-Z][A-Z0-9_]+\b/, { cases: { "@builtinTypes": "type.identifier", "@default": "constant" } }],
      [
        /[A-Z][A-Za-z0-9]*/,
        {
          cases: {
            "@builtinTypes": "type.identifier",
            "@builtinConstructors": "constant.language",
            "@default": "type"
          }
        }
      ],

      [/0[xX][0-9a-fA-F]+/, "number.hex"],
      [/\d+/, "number"],

      [/"/, { token: "string.quote", bracket: "@open", next: "@string" }],

      [/[()[\]]/, "@brackets"],
      [/@symbols/, { cases: { "@operators": "operator", "@default": "" } }],
      [/[,;]/, "delimiter"],
      [/\s+/, "white"]
    ],

    block: [
      [/[^|]+/, "comment"],
      [/\|#/, { token: "comment", next: "@pop" }],
      [/\|/, "comment"]
    ],

    docBlock: [
      [/[^|]+/, "comment.doc"],
      [/\|#/, { token: "comment.doc", next: "@pop" }],
      [/\|/, "comment.doc"]
    ],

    string: [
      [/[^\\"]+/, "string"],
      [/@escapes/, "string.escape"],
      [/\\./, "string.escape.invalid"],
      [/"/, { token: "string.quote", bracket: "@close", next: "@pop" }]
    ]
  }
};

/**
 * Register Cinnabar with a Monaco instance.
 *
 * Takes the instance rather than importing it, so this package never
 * bundles a second copy of Monaco into a page that already has one.
 */
export function registerCinnabar(monaco) {
  monaco.languages.register(languageExtensionPoint);
  monaco.languages.setLanguageConfiguration(LANGUAGE_ID, languageConfiguration);
  monaco.languages.setMonarchTokensProvider(LANGUAGE_ID, monarchLanguage);
  return LANGUAGE_ID;
}
