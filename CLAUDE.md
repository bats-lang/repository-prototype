## What is Bats?

Bats is a programming language that compiles to ATS2. The pipeline is: `.bats` → lexer → emit `.sats`/`.dats` → patsopt → `_dats.c` → clang → binary. It has its own package manager, safety model (`unsafe = true/false` in `bats.toml`), and calendar versioning.

## Key Repos

All bats repos live under github.com/bats-lang/

* **`bats/`** — The Bats compiler, self-hosting (written in Bats). Built with: `dist/debug/bats build --repository ../repository-prototype`.

* **`repository-prototype/`** — Package repository containing published `.bats` package archives.

## Library Packages

Each is its own git repo with a `bats.toml` (`kind = "lib"`). Some are `unsafe = true` (contain C FFI code), others are safe wrappers.

**Core/native:** argparse, arith, array, builder, dict, env, json, list, path, process, promise, result, sha256, sort, str, toml, xml-tree, zip

**Browser/WASM** (namespaced `wasm.bats-packages.dev/`): bridge, dom, html

**For browser apps, published without the namespace:** css, gestures, pwa, widget

**Both targets:** file

**Superseded by bridge (archived):** callback, clipboard, dom-read, event, fetch, idb, nav, notify, timer, window, xml. Their published archives stay here for old lockfiles; new code uses bridge.

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

## CI Pattern: every input is pinned (#269)

A package's CI depends only on its own source, so a commit that passes
keeps passing; pins move only through a reviewed pull request that runs
the same CI.

* **The lock:** `bats.lock` is committed (a package with no dependencies
  has none). CI never runs `bats lock` for the package: `bats check` and
  `bats build` fetch exactly the locked versions, and fail when the lock
  is missing or does not match `bats.toml`. A library's lock pins only
  its own CI and tests; its dependents still resolve their own.
* **The compiler:** its commit is in `.github/bats-version`, read by
  every workflow that builds bats (and by `publish.yml` here).
* **The package repository:** CI fetches this repository at the commit in
  `.github/repository-version`, so what test packages lock (`bats lock
  --dev` in `tests/`) is pinned too.
* **Called workflows:** `publish.yml` and `relock-pins.yml` here (and
  pwa's `android.yml` for an app) are called by commit, never `@main`.
* **The daily relock:** each repository's `relock.yml` calls
  `relock-pins.yml` here by commit. It relocks, moves the compiler, the
  repository and the workflow pins to their newest, pushes
  `relock/<date>`, opens a pull request listing what moved, and dispatches
  `check.yml` on it (`workflow_dispatch`). A breaking publish shows as a
  red relock pull request, and no main goes red. GITHUB_TOKEN cannot edit
  `.github/workflows`, so without a `RELOCK_TOKEN` secret a workflow pin
  that would move is listed in the pull request, to move by hand.

This repository's own `verify` is the exception: it checks a new archive
against every package's newest version, which is the point of it.

## Branches

After a PR merges, restart the same branch from main. PRs merge with `--merge`, so main contains the branch and the push is a fast-forward: never force-push.

```
git fetch origin main && git checkout -B <branch> origin/main && git push -u origin <branch>
```

## Publishing Packages

To publish an updated library package to repository-prototype:

1. Merge the change to main.

2. Check out main itself: `git fetch origin main && git checkout -B main origin/main`. `bats upload` names the version after the checked-out branch; anything but `main` uploads a `dev1` version.

3. Run `bats upload --repository ../repository-prototype` from the package directory, with a compiler built from bats main.

4. Check each sidecar (`sha256sum -c <archive>.sha256`), then commit the archive and sidecar in repository-prototype and open a PR.

**A package whose API changed is published together with its dependents.** Before publishing, update every package that uses it (grep all repos' `src/`), verify each against a scratch copy of repository-prototype that holds the new archives, and put all of them in one repository-prototype PR. Publishing one alone breaks anyone who locks the latest versions.

**`bats lock` does not refresh `bats_modules/`** (as in the Rust bats). After relocking, rebuild `bats_modules/` from `bats.lock` before trusting `bats check` or `bats build`; stale modules hide API mismatches.

**Generated directories** (`build/`, `dist/`, `docs/`, `bats_modules/`) are in every package's `.gitignore`; `bats clean` removes the first three. Never delete them by hand.

## Safety Rules

All safety is compile-time. The constraint solver proves properties; you never assert them at runtime.

* **No `$UNSAFE`, `$extfcall`, or `castfn`** in application code. If a package does only data manipulation, it must be `unsafe = false`.

* **No runtime bounds checks or assertions.** Prove bounds and invariants via dependent types. When the constraint solver rejects something, add the right constraint to the function signature (`{n:pos | n < 65536}`, `{l:agz}`, `{k:int | k == 1}`, etc.) and thread it through the call chain. If you can't prove it, make it provable. You don't know anything you can't prove.

* **Never use `g1ofg0` to recover dependent types.** If a value needs dependent type constraints, declare it with the right type from the start. Thread constraints through function signatures — don't convert at the call site. `g1ofg0` is always a mistake; it means the upstream type was wrong.

* **Never use unsafe library functions as shortcuts.** If there's a safe, correct solution (even if it's more work), use it. Clever tricks to reach for unsafe APIs (e.g. `borrow_to_string` from bridge) are not acceptable.

* **Packages must never be made `unsafe = true`** without explicit user authorization. If a package is currently safe, keep it safe.

## Conditional Compilation

When shared module code references WASM-only APIs (bridge, dom, IDB, etc.) and won't link for native targets, wrap those sections with `#target wasm begin/end`. Do NOT restructure the build, move files to separate packages, or change CI workflows. This is how bridge itself works — every sub-module (idb.bats, dom.bats, event.bats, etc.) wraps its entire body in `#target wasm begin/end`. The pwa/example/ pattern shows sister binaries: `#target native` for build-pwa.bats, `#target wasm binary` for pwa-web.bats, sharing the same package.

## Code Quality Patterns

* **Avoid magic in the compiler**: Prefer steering `.bats` source code to be correct over adding clever transformations in the emitter/lexer. Deep magic confuses other agents. Small, explicit fixes in source are better than invisible compiler rewrites.

* **Avoid copy-paste**: Use generic helpers instead of duplicating code with different constants. Example: `bytes_match` + `has_suffix` + `name_eq` replaced 7 copy-paste extension-checking functions in the bats compiler.

* **ATS2 reserved words**: `prefix`, `postfix`, `infixl`, `infixr` are ATS2 keywords. Never use them as variable or parameter names — patsopt silently corrupts its parser state.

* **Char literals for `{`, `(`, `[`**: patsopt lexes `'{`, `'(` and `'[` as the record/tuple/list openers, so `'{'`, `'('` and `'['` fail with "the char constant is unclosed". Write `'\{'`, `'\('` and `'\['`. (`'"'` is fine.)

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

**Byte ranges** — to read part of an array, freeze it and split the borrow; borrow pieces can only be dropped, never freed:

```
val @(fz, bv) = $A.freeze<byte>(buf)
val @(left, right) = $A.borrow_split<byte>(fz, bv, k)   (* left: borrow(byte, l, k) *)
... read left ...
val () = $A.drop<byte>(fz, $A.borrow_join<byte>(fz, left, right))
val () = $A.free<byte>($A.thaw<byte>(fz))
```

To write at an offset, use `write_byte`, `write_u16le`, `write_i32` or `write_borrow`: their offsets are proven in range by their types. (The array library has no `split` for `arr`: a piece of an `arr` could be passed to `free`.)

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
