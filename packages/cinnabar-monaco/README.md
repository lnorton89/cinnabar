# cinnabar-monaco

Cinnabar language support for the [Monaco](https://microsoft.github.io/monaco-editor/)
editor: a Monarch tokenizer, a language configuration, and the language's
keyword and builtin tables.

```bash
npm install cinnabar-monaco
```

```js
import * as monaco from "monaco-editor";
import { registerCinnabar } from "cinnabar-monaco";

const languageId = registerCinnabar(monaco);
monaco.editor.create(document.getElementById("editor"), {
  value: "pub fun main() I64\n  return 0\nend\n",
  language: languageId
});
```

Monaco is a peer dependency and is never imported here — `registerCinnabar`
takes the instance you already have, so this package cannot pull a second copy
of Monaco into your bundle.

## Why a regex tokenizer is accurate here

Monaco tokenizes line by line with a small state machine, which is usually a
compromise. Two properties of Cinnabar make it an unusually good fit.

**Casing is grammar, not convention.** The compiler's lexer rejects a mis-cased
identifier, so an identifier's shape already says what kind of thing it names:
`snake_case` is a function or binding, `PascalCase` is a type, trait, module or
variant, `SCREAMING_SNAKE_CASE` is a constant. Colouring by shape is therefore
semantic rather than a guess — `classifyIdentifier` is that rule, exported for
anything else that needs it.

**`#` always opens a comment.** There is no `#` operator to disambiguate against
and no preprocessor, so comment rules can come first unconditionally.

What a tokenizer cannot know is anything the typechecker computes — whether a
handle is linear, what a name resolved to. Nothing here claims to. For that,
run the compiler: `cinnabar --emit-json` gives the attached facts as structured
documents, and `cinnabar-lsp` gives them as language-server responses.

## Staying in step with the compiler

`src/language.js` holds the keyword list, and `test/drift.test.js` reads the
compiler's own `KEYWORDS` table out of `src/analysis.rs` and asserts they match,
in order. A keyword added to or removed from the language fails a test here
rather than leaving this package quietly describing a language that moved on.
The control-flow and modifier lists are checked to be subsets of that one list
rather than second copies of it.

```bash
npm test
```
