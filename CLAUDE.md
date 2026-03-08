## What is Bats?

Bats is a programming language that compiles to ATS2. The pipeline is: `.bats` → lexer → emit `.sats`/`.dats` → patsopt → `_dats.c` → clang → binary. It has its own package manager, safety model (`unsafe = true/false` in `bats.toml`), and calendar versioning.

## Key Repos

All bats repos live under github.com/bats-lang/

- **`bats/`** — The Bats compiler, self-hosting (written in Bats). Built with: `dist/debug/bats build --repository ../repository-prototype`.
- **`repository-prototype/`** — Package repository containing published `.bats` package archives.

## Library Packages

Each is its own git repo with a `bats.toml` (`kind = "lib"`). Some are `unsafe = true` (contain C FFI code), others are safe wrappers.

**Core/native:** argparse, arith, array, builder, dict, env, path, process, promise, result, sha256, sort, str, toml, zip, decompress

**Browser/WASM** (namespaced `wasm.bats-packages.dev/`): bridge, callback, clipboard, css, dom, dom-read, event, fetch, file-input, html, idb, nav, notify, timer, widget, window, xml, xml-tree

**Both targets:** file

## Project Structure (per package)

```
bats.toml          # Package config: name, kind, unsafe, [dependencies]
src/lib.bats       # Library entry point
src/bin/<name>.bats # Binary entry points (kind = "bin" only)
bats_modules/      # Fetched dependencies
build/             # Generated .sats/.dats/_dats.c (never edit)
dist/              # Output binaries
```

## Workflow

All changes in ANY repo go through: feature branch → PR → CI green → merge. Never commit directly to main. Use `gh pr merge --merge` (no squash).

## CI Pattern

All library packages use the same CI pattern: download the `bats-c` artifact (pre-compiled C files) from the bats repo's latest successful main build, compile with `make`, and use the resulting binary.

**Library packages** (`.github/workflows/check.yml`):
1. Install ATS2 from source (patsopt for type-checking)
2. Symlink ATS2 to `~/.bats/ats2` (where the bats compiler expects it)
3. Download `bats-c` artifact from `bats-lang/bats` latest main build via `gh run download`
4. `make PATSHOME=...` to compile the C files into a bats binary
5. Run `bats lock` and `bats check` (with `bats` in PATH)

**Packages that need dependencies** use `--repository` pointing to `repository-prototype`. Packages without dependencies just run `bats check` directly.

## Publishing Packages

To publish an updated library package to repository-prototype:
1. Merge the change to main
2. Run `bats upload --repository ../repository-prototype` from the package directory
3. Commit and push the new archive in repository-prototype

## Code Quality Patterns

- **Avoid magic in the compiler**: Prefer steering `.bats` source code to be correct over adding clever transformations in the emitter/lexer. Deep magic confuses other agents. Small, explicit fixes in source are better than invisible compiler rewrites.
- **Avoid copy-paste**: Use generic helpers instead of duplicating code with different constants. Example: `bytes_match` + `has_suffix` + `name_eq` replaced 7 copy-paste extension-checking functions in the bats compiler.
- **Use `text_of_chars`**: The str library provides `text_of_chars(n, @[char][n](...))` for creating text constants. Use this instead of verbose `text_build`/`text_putc`/`text_done` sequences.
- **Use `chars_match`/`has_suffix`/`name_eq`**: The str library provides these for matching byte arrays against string literals. Use instead of manual byte comparisons.
- **ATS2 reserved words**: `prefix`, `postfix`, `infixl`, `infixr` are ATS2 keywords. Never use them as variable or parameter names — patsopt silently corrupts its parser state.
- **No bounds checking**: Prove that bounds are satisfied at compile time
- **No runtime assertions**: Prove that assertions are satisfied
- **No unsafe constructs**: `$UNSAFE`, `$extfcall`, and `castfn` are all unsafe (unchecked type assertions). Never use them. Prove properties at compile time via dependent types and the constraint solver instead. If a package does only data manipulation, it must be `unsafe = false`.

## Local Verification

- Always run `bats check` locally before pushing. Do not depend on CI to catch errors.
- To get the bats binary: `gh run download --repo bats-lang/bats --name bats-c --dir /tmp/bats-c && cd /tmp/bats-c && PATSHOME=~/.bats/ats2 make && cp release/bats <target>`

## Problem Resolution

- Never work around bugs. Fix them properly. If the version resolver picks the wrong version, fix the resolver — don't manually edit the lock file.
- Nothing is someone else's problem. If I see a problem in a dependency, I fix it there — not work around it.

## Package Discipline

- Unless specifically authorized, do not create or split packages.
- Packages must never be made `unsafe = true` without explicit user authorization. If a package is currently safe, keep it safe.

## Development Discipline

- Do not use CI to build things speculatively. CI is for end-to-end testing or confirming what you already know works locally. Run `bats check`, `bats build`, and patsopt locally first.

## Task Discipline

- Each task must be one concrete action. "all", commas, "and", "do 3 things" are never tasks. Break them down.
- A goal is not a task. "Remove unsafety" is a goal. "Replace $UNSAFE.cast{arg(T)} with _arg_of_int in add_string" is a task.
