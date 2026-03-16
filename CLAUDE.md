## What is Bats?

Bats is a programming language that compiles to ATS2. The pipeline is: `.bats` → lexer → emit `.sats`/`.dats` → patsopt → `_dats.c` → clang → binary. It has its own package manager, safety model (`unsafe = true/false` in `bats.toml`), and calendar versioning.

## Key Repos

All bats repos live under github.com/bats-lang/

* **`bats/`** — The Bats compiler, self-hosting (written in Bats). Built with: `dist/debug/bats build --repository ../repository-prototype`.

* **`repository-prototype/`** — Package repository containing published `.bats` package archives.

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

## Safety Rules

All safety is compile-time. The constraint solver proves properties; you never assert them at runtime.

* **No `$UNSAFE`, `$extfcall`, or `castfn`** in application code. If a package does only data manipulation, it must be `unsafe = false`.

* **No runtime bounds checks or assertions.** Prove bounds and invariants via dependent types. When the constraint solver rejects something, add the right constraint to the function signature (`{n:pos | n < 65536}`, `{l:agz}`, `{k:int | k == 1}`, etc.) and thread it through the call chain. If you can't prove it, make it provable. You don't know anything you can't prove.

* **Never use unsafe library functions as shortcuts.** If there's a safe, correct solution (even if it's more work), use it. Clever tricks to reach for unsafe APIs are not acceptable.

* **Packages must never be made `unsafe = true`** without explicit user authorization. If a package is currently safe, keep it safe.

## Conditional Compilation

When shared module code references WASM-only APIs (bridge, dom, IDB, etc.) and won't link for native targets, wrap those sections with `#target wasm begin/end`. Do NOT restructure the build, move files to separate packages, or change CI workflows. This is how bridge itself works — every sub-module (idb.bats, dom.bats, event.bats, etc.) wraps its entire body in `#target wasm begin/end`. The pwa/example/ pattern shows sister binaries: `#target native` for build-pwa.bats, `#target wasm binary` for pwa-web.bats, sharing the same package.

## Code Quality Patterns

* **Avoid magic in the compiler**: Prefer steering `.bats` source code to be correct over adding clever transformations in the emitter/lexer. Deep magic confuses other agents. Small, explicit fixes in source are better than invisible compiler rewrites.

* **Avoid copy-paste**: Use generic helpers instead of duplicating code with different constants. Example: `bytes_match` + `has_suffix` + `name_eq` replaced 7 copy-paste extension-checking functions in the bats compiler.

* **ATS2 reserved words**: `prefix`, `postfix`, `infixl`, `infixr` are ATS2 keywords. Never use them as variable or parameter names — patsopt silently corrupts its parser state.

## Array and String Library Patterns

**Byte array construction from character literals** — use `$S.from_char_array`:

```
var key = @[char][4]('b', 'o', 'o', 'k')
val key_arr = $S.from_char_array(key, 4)
```

Never use `int2byte0` with ASCII codes. Never use `$A.alloc` + multiple `$A.set<byte>` calls for string-like keys.

**Text values** — use `$S.text_of_chars`:

```
var chars = @[char][7]('U', 'n', 'k', 'n', 'o', 'w', 'n')
val t = $S.text_of_chars(chars, 7)
```

**String matching** — use `$S.chars_match`, `$S.has_suffix`, `$S.name_eq` instead of manual byte comparisons.

**Typed write operations** — the array library has `write_byte`, `write_u16le`, `write_i32`, `write_borrow`, and `write_text`, all with dependent-type constraints (e.g., `write_i32` requires `{i:nat | i + 4 <= n}`). Use these instead of manual `$A.set<byte>` calls for multi-byte values.

**Split/join for sub-array work** — when you need to work with a specific byte range in an array, use `$A.split`/`$A.join` to decompose it. Example: to write 4 bytes at offset `off` in a size-`n` array:

```
val @(left, right) = $A.split<byte>(arr, off)       (* left: arr(byte, l, off), right: arr(byte, l+off, n-off) *)
val @(target, rest) = $A.split<byte>(right, 4)       (* target: arr(byte, l+off, 4) *)
val () = $A.set<byte>(target, 0, b0)                  (* 0 < 4: trivially proved *)
val () = $A.set<byte>(target, 1, b1)
val () = $A.set<byte>(target, 2, b2)
val () = $A.set<byte>(target, 3, b3)
val right = $A.join<byte>(target, rest)
val arr = $A.join<byte>(left, right)
```

This eliminates manual index arithmetic and the need to prove `off + k < n` chains. For borrows, `$A.borrow_split`/`$A.borrow_join` work similarly but adjust the frozen refcount.

## Problem Resolution

* **Errors are never OK, never expected, never "already there."** If you encounter an error — a type error, a linker error, a test failure, a warning — you stop and fix it immediately, before doing anything else. Do not proceed with other work while errors exist.

* Nothing is someone else's problem. If you see a problem in a dependency, fix it there — not work around it.

* Never work around bugs. Fix them properly. If the version resolver picks the wrong version, fix the resolver — don't manually edit the lock file.

* Quire is a forcing function for Bats. Whenever quire reveals missing functionality in a library package (widget, css, dom, etc.), stop and fix the library first. Then use the fix in quire.

* When something won't compile or link, check whether the language has conditional compilation, the library has a helper function, or the type system has a way to express the constraint before restructuring the build. Always `grep` the library and dependency source before concluding something is impossible or requires a workaround.

* Unless specifically authorized, do not create or split packages.

## Local Verification

* Always run `bats check` locally before pushing. Do not depend on CI to catch errors.

* Do not use CI to build things speculatively. CI is for confirming what you already know works locally. Run `bats check`, `bats build`, patsopt, and e2e tests locally first.

* To get the bats binary: `gh run download --repo bats-lang/bats --name bats-c --dir /tmp/bats-c && cd /tmp/bats-c && PATSHOME=~/.bats/ats2 make && cp release/bats <target>`

## Task Discipline

* Each task must be one concrete action. "all", commas, "and", "do 3 things" are never tasks. Break them down.

* A goal is not a task. "Remove unsafety" is a goal. "Replace `$UNSAFE.cast{arg(T)}` with `_arg_of_int` in `add_string`" is a task.
