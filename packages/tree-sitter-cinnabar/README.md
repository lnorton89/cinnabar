# tree-sitter-cinnabar

A [tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar for
[Cinnabar](https://github.com/lnorton89/cinnabar), with highlight queries.

It feeds the editors and tools that want structure without running the compiler:
tree-sitter-based editors (Neovim, Helix, Zed, Emacs), GitHub's own syntax
highlighting once the grammar lands in
[linguist](https://github.com/github-linguist/linguist), and anything else that
speaks tree-sitter.

## What it knows about the language

Two properties of Cinnabar make a grammar unusually informative here.

**Casing is grammar, not convention.** The compiler's lexer rejects a mis-cased
identifier, so `snake_case`, `PascalCase` and `SCREAMING_SNAKE_CASE` are three
distinct terminals in this grammar rather than one `identifier` rule. A
highlighter reading the parse tree can colour an identifier by what it *is* —
type, constant, or binding — with no symbol table and no heuristics. Anywhere
this grammar accepted the wrong case it would be claiming the compiler accepts a
program it rejects.

**A statement ends at the end of its line, and a block ends at `end`.** There are
no braces and no semicolons. That makes the newline a real token, and it is the
one thing the rules cannot express alone: a newline inside a parameter list is
continuation, not a terminator. `src/scanner.c` supplies newline tokens where the
grammar permits one, and the grammar lists the newline as an extra so that
everywhere else it is skipped as the continuation it is.

The scanner does one more thing. A match arm's block has no closing keyword — it
ends when the next arm's pattern appears, and only the `=>` after that pattern
says so. The scanner looks ahead for that `=>` and emits a zero-width marker, so
the parser knows a pattern is coming before it reads one.

## Verifying it

The grammar is checked against the compiler rather than against itself:

```bash
tree-sitter generate
tree-sitter test                                   # the corpus in test/corpus/
node test/conformance.mjs path/to/cinnabar         # against every repo fixture
```

`test/conformance.mjs` runs both the compiler and the parser over every `.cnb`
under `tests/fixtures/` and compares verdicts. **Every program the compiler
accepts parses here with no error node.** The fixtures the compiler rejects are
reported separately rather than counted as passes — a grammar that also rejected
them would be a nice property, but it is not one this grammar claims: most of
those are rejected for reasons no parser can see, like a name that was never
declared.

## Known representation choices

**Explicit instantiation has no node of its own.** `vec_new[U8]()` reads as an
`index_expression` that is then called. Its bracket group holds a type where an
index holds a value, and nothing before the `]` distinguishes them; recovering
the distinction needs a `_type`/`_expression` ambiguity declared across the whole
grammar, which makes every `Name(...)` constructor call unparseable. The `U8` is
still a `type_identifier` and still highlights as a type — what is lost is only
the name of the node above it, which is a much better trade for a highlighting
and navigation grammar than losing constructor calls.

**Field access on a literal** — `42.some_field` — is not parsed. It is not a
valid program either; the compiler rejects it, and the only fixture containing it
exists to pin that diagnostic.

## Layout

```
grammar.js                 the grammar
src/scanner.c              newline and arm-start recognition
queries/highlights.scm     highlight captures
test/corpus/               parse-tree expectations
test/conformance.mjs       the check against the compiler
```
