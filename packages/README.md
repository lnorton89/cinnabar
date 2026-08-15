# packages/

Standalone npm packages for Cinnabar's syntax layer, published independently of
the compiler.

| Package | What it is |
|---|---|
| [`tree-sitter-cinnabar`](tree-sitter-cinnabar/) | A tree-sitter grammar and highlight queries. Feeds tree-sitter editors (Neovim, Helix, Zed, Emacs) and, once it lands in [linguist](https://github.com/github-linguist/linguist), GitHub's own highlighting |
| [`cinnabar-monaco`](cinnabar-monaco/) | A Monarch tokenizer and language configuration for the Monaco editor |

Both describe the same language and neither is the compiler, so both are
verified against it rather than against themselves:

- `tree-sitter-cinnabar` runs the compiler and the parser over every `.cnb` in
  `tests/fixtures/` and requires that every program the compiler accepts parses
  with no error node (`node test/conformance.mjs <cinnabar-binary>`).
- `cinnabar-monaco` reads the compiler's `KEYWORDS` table out of
  `src/analysis.rs` and requires its own list to match, in order.

That is the same discipline the rest of the repository holds itself to: a fact
about the language has one definition, and a copy of it that could drift is
checked against the original rather than trusted.
