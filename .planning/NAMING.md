# The name

Raising this while it is still cheap, which is the only reason to raise it at
all.

## The collision

`cinnabar` is taken, twice, in the places that matter for a language:

- **git-cinnabar** — a Git remote helper for Mercurial, Mozilla-adjacent, with
  a decade of history and a few hundred stars. It owns the first page of results
  for the word in a developer context.
- **`cinnabar` on crates.io** — the crate name is registered. This project is a
  Rust compiler; the one registry where it would most naturally publish is the
  one where its name is already gone.

Neither is going anywhere, and neither is a language, so there is no
"disambiguation by category" to fall back on: a person searching for how to
install this, how to write a linear type in it, or why their borrow was
rejected, will land on a Mercurial bridge.

## Why now

The cost of renaming is not the rename. It is everything that has already been
written down:

| What a rename touches today | Roughly |
|---|---|
| Repository, module paths, binary names | mechanical |
| `.cnb` extension, `build.cnb` manifest keys | mechanical, but every fixture |
| `MANIFESTO.md`, `README.md`, `ARCHITECTURE.md`, `ROADMAP.md` | prose, the name appears throughout |
| The site, its OG images, its brand assets | prose and artwork |
| `editors/vscode` package id, `tree-sitter-cinnabar`, `cinnabar-monaco` | published names, once published |
| The `cinnabar.*.v1` document format tags | a compat surface, once consumed |

Every row of that table gets more expensive, and the last two rows become
genuinely hard the moment anything is published or anyone depends on a format
tag. Right now nothing is published and nothing external depends on those tags,
so the whole table is one determined afternoon.

At 5,000 commits, a published extension, a crates.io release and a linguist
entry, it is not an afternoon and it is not reversible.

## What is actually being decided

Not "is the name good" — it is a good name, and the mineral is exactly right for
a language whose whole argument is that the dangerous thing should be visible
and handled deliberately. The decision is narrower:

**Is permanent second place in search results an acceptable price for keeping
it?**

For a project whose adoption problem is that nobody has heard of it, that price
is high. For a project that will be found by word of mouth in a small community,
it is nearly zero.

That is a call only the maintainer can make, which is why this is a note and not
a patch.

## If the answer is rename

Two things worth doing in the same change, because they are cheap now and
annoying later:

1. **Reserve the name on crates.io and npm before announcing it.** Both are
   first-come; a name that is free today is not necessarily free the week the
   project gets attention.
2. **Version the document format tags with the new name from the start**
   (`<name>.diagnostics.v1` and so on). They are the one surface here that
   external tools bind to, and renaming them after something consumes them means
   supporting both.

## If the answer is keep it

Also fine, and there is a cheap mitigation: make every public surface carry a
qualifier that search engines can latch onto — "Cinnabar language", "Cinnabar
lang", `cinnabar-lang` as the npm scope and the crates.io name — so that the
searchable phrase is not the ambiguous single word. That is already what the
VS Code extension does (`publisher: cinnabar-lang`), and doing it consistently
everywhere else costs nothing.
