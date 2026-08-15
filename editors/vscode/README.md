# Cinnabar Language Support

This extension registers `.cnb` files, provides the canonical TextMate grammar, and launches
`cinnabar-lsp` over stdio.

## Language-server features

Beyond hover, go-to-definition, references, completion, signature help, and formatting,
`cinnabar-lsp` also provides:

- **Rename** (`F2`) — renames every occurrence of a function, type, trait, module, native
  declaration, constant, or enum variant across every open file. Struct fields and local
  `val`/`var` bindings aren't symbol-table entries in the compiler's resolver, so they can't be
  renamed this way yet; the command declines rather than producing a partial or wrong edit.
- **Document symbols** (`Ctrl+Shift+O` / Outline view) and **workspace symbols**
  (`Ctrl+T`) — a file's declarations nested by module/struct/enum/trait/impl, or a
  fuzzy-searchable list across every loaded file.
- **Folding ranges** — computed from the real parse tree (module, struct, enum, trait, impl,
  function, `while`, `if`, and `match` bodies), plus a source scan for `#|...|#`/`#!|...|#`
  comment blocks, which keep no parse-tree span of their own.
- **Semantic tokens** — colors identifier *uses* by what the resolver actually resolved them to
  (function, method, type, enum member, module, constant), which a static TextMate grammar can't
  do context-sensitively.
- **Inlay hints** — shows the typechecker's inferred type after a `val`/`var` binding that has no
  explicit `: Type` annotation.
- **Code actions** (quick fixes) — recognized by diagnostic message text rather than a
  `DiagKind` enum (the compiler doesn't have one): remove an unused import, remove an unused
  declaration, fix a casing-rule violation (renames every occurrence), and make a privately-used
  declaration `pub`. A diagnostic this layer doesn't recognize offers no fix rather than a guess.

## Status bar and commands

A status bar item on the right shows whether `cinnabar-lsp` is starting, running, or stopped;
clicking it opens the server's output channel. Two commands are also available from the Command
Palette:

- **Cinnabar: Restart Language Server** — stops and relaunches `cinnabar-lsp`, picking up a
  changed `cinnabar.server.mode` or `cinnabar.server.path` without reloading the window.
- **Cinnabar: Show Output Channel** — opens the same output channel as clicking the status bar
  item.

## Borrow explanations

Borrow-checker explanations appear as code lenses above the line they annotate. Clicking one opens
a panel beside the editor that draws the explanation as a diagram rather than stacking it as text:
the binding site at the top, the branches that disagree about the value as parallel lanes below it,
and the guidance last. Every node is clickable and reveals its span in the editor.

The shape is the point. A linear-type rejection is a claim about a value's path through a
function — bound here, consumed on this route, still live on that one — and a stack of secondary
labels makes the reader reassemble that shape in their head. `cinnabar-lsp` sends the whole
explanation with each lens, so the panel needs no second request to draw it.

Each node is classified by the `kind` the borrow checker attached to its note (`binding`,
`consumed`, `live`, `moved`, `guidance`, `context`), never by matching the wording of a message.
Messages are prose and may be reworded; the kinds are the checker's own vocabulary, so rewording a
diagnostic cannot silently change what the diagram claims.

## Tasks

The extension contributes `cinnabar` tasks for every project in the workspace — `build`, `run`,
`check`, `test`, and `test (update snapshots)` — discoverable from **Terminal → Run Task…**. A
project is a directory with a `build.cnb`, found by walking upward from each workspace folder, so a
workspace opened on a subdirectory still gets its tasks and a folder with no manifest anywhere
above it gets none rather than tasks that would fail on invocation. Two folders inside one project
contribute one set of tasks, not two.

`cinnabar.compiler.path` selects the executable those tasks invoke (default: `cinnabar` from
`PATH`). No task declares a problem matcher: the language server already publishes the compiler's
diagnostics with real spans, and a matcher scraping the same errors out of terminal text would
double every one of them in the Problems panel.

## Snippets

`snippets/cinnabar.json` covers the declaration and control-flow shapes (`fun`, `pubfun`, `natfun`,
`main`, `if`/`ifelse`/`ifelif`, `while`, `match`, `type`/`typevariants`/`nattype`, `mod`, `trait`,
`impl`, `const`, `val`, `var`, `use`, `docblock`, `commentblock`). Every keyword a snippet body
uses is checked against `src/analysis.rs`'s `KEYWORDS` table by `test/spec-drift.test.js`, so a
renamed or removed keyword fails the test suite instead of shipping a snippet that no longer
parses.

## Language-server launch modes

`cinnabar.server.mode` controls the process the extension starts:

- `auto` (default): launches `cinnabar.server.path` when that setting is non-empty; otherwise
  launches the installed `cinnabar-lsp` command from `PATH`.
- `installed`: always launches `cinnabar-lsp` from `PATH`.
- `path`: launches the executable configured by `cinnabar.server.path` and reports an error if it
  is empty.
- `docker-compose`: finds the nearest workspace ancestor containing `compose.dev.yaml` and
  `container/local/main/worktree.env`, sets that directory as the child process working directory,
  and launches:

  ```text
  docker compose --env-file container/local/main/worktree.env -f compose.dev.yaml exec -T dev ./target/debug/cinnabar-lsp
  ```

The repository workspace uses `docker-compose` mode in `.vscode/settings.json`, so it contains no
machine-specific executable or temporary wrapper. Before using that mode, start the development
container and ensure `container/local/main/worktree.env` identifies the checkout as required by
the Compose file.

For local development, run `npm install` in this directory and launch the extension through the
VS Code Extension Development Host. Run `npm test` to exercise launch-plan selection and
`npm run package:dry-run` to inspect the extension package contents.
