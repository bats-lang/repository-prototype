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
- **Unsafety is NEVER acceptable unless ALL ELSE FAILED**: Clever tricks to use unsafe APIs (e.g. `borrow_to_string` from bridge) are DISALLOWED if there's a safe, correct solution. Do not use unsafe library functions as shortcuts — find the safe path first.

## Conditional Compilation

When shared module code references WASM-only APIs (bridge, dom, IDB, etc.) and won't link for native targets, wrap those sections with `#target wasm begin/end`. Do NOT restructure the build, move files to separate packages, or change CI workflows. This is how bridge itself works — every sub-module (idb.bats, dom.bats, event.bats, etc.) wraps its entire body in `#target wasm begin/end`. The pwa/example/ pattern shows sister binaries: `#target native` for build-pwa.bats, `#target wasm binary` for pwa-web.bats, sharing the same package.

## arith castfn — UNSAFE, DO NOT USE

`$AR.checked_idx`, `$AR.checked_byte`, `$AR.checked_nat`, `$AR.checked_pos`, `$AR.checked_arr_size`, `$AR.checked_text_size`, and `$AR.g0_of_g1` are ALL `castfn` — unsafe casts that assert a property without proving it. They erase at compile time and the constraint solver just trusts them. **Do not use these.** Thread constraints through the types properly instead. When the constraint solver rejects something, add the right constraint to the function signature (`{n:pos | n < 65536}`, `{l:agz}`, `{k:int | k == 1}`, etc.) and thread it through the call chain. `$AR.byte_of_char` is safe (`fn` not `castfn`) but should not use `checked_byte` internally. The dependent-typed `$AR.band_g1 {a,b:nat}(int(a), int(b)): [r:nat | r <= b] int(r)` can prove `< 256` bounds directly.

## Array split/join for sub-array work

The array library provides `$A.split`/`$A.join` (and `$A.borrow_split`/`$A.borrow_join` for borrows). When you need to read or write specific byte ranges in an array, split the array at the offset, work on the sub-array (where proving `0 < 4` is trivial), then join back. This eliminates manual index arithmetic and the need to prove `off + k < n` chains. Note: `borrow_split` increments refcount on frozen, `borrow_join` decrements it.

## Byte array construction from character literals

To construct a byte array from character literals:
```
var key = @[char][4]('b', 'o', 'o', 'k')
val key_arr = $S.from_char_array(key, 4)
```
For text values: `$S.text_of_chars(chars, n)`. Never use `int2byte0` with ASCII codes for string construction. Never use `$A.alloc` + multiple `$A.set<byte>` calls for string-like keys.

## Typed write operations for serialization

The array library has `write_byte`, `write_u16le`, `write_i32`, `write_borrow`, and `write_text` — all with proper dependent-type constraints (e.g., `write_i32` requires `{i:nat | i + 4 <= n}`). Use these instead of manual `$A.set<byte>` calls for multi-byte values.

## General principle: use language/library facilities before restructuring builds

When something won't compile or link for a specific target, check whether the language has conditional compilation, the library has a helper function, or the type system has a way to express the constraint. Restructuring the build (moving files, splitting packages, changing CI) is a last resort. Always `grep` the library and dependency source before concluding something is impossible or requires a workaround.

## Local Verification

- Always run `bats check` locally before pushing. Do not depend on CI to catch errors.
- To get the bats binary: `gh run download --repo bats-lang/bats --name bats-c --dir /tmp/bats-c && cd /tmp/bats-c && PATSHOME=~/.bats/ats2 make && cp release/bats <target>`

## Problem Resolution

- Never work around bugs. Fix them properly. If the version resolver picks the wrong version, fix the resolver — don't manually edit the lock file.
- Nothing is someone else's problem. If I see a problem in a dependency, I fix it there — not work around it.
- Quire is a forcing function for Bats. Whenever quire reveals missing functionality in a library package (widget, css, dom, etc.), stop and fix the library first. Then use the fix in quire.

## Package Discipline

- Unless specifically authorized, do not create or split packages.
- Packages must never be made `unsafe = true` without explicit user authorization. If a package is currently safe, keep it safe.

## Development Discipline

- Do not use CI to build things speculatively. CI is for end-to-end testing or confirming what you already know works locally. Run `bats check`, `bats build`, and patsopt locally first.

## Task Discipline

- Each task must be one concrete action. "all", commas, "and", "do 3 things" are never tasks. Break them down.
- A goal is not a task. "Remove unsafety" is a goal. "Replace $UNSAFE.cast{arg(T)} with _arg_of_int in add_string" is a task.
