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

* **Copies of a pin's commit:** a reusable workflow cannot read its own ref, so a caller may repeat a pin's commit as an input (quire's `pwa-ref`, which pwa's `android.yml` and `play-release.yml` read). `relock-pins.yml`'s input `pin-copies` lists them, `<owner>/<repo>/<path> <input>` one per line: after a pin moves, every `<input>: <40 hex>` line of the files that call the pin gets the commit the pin got, comment after it kept, and any other spelling of that key (quoted, an expression, not 40 hex) fails the step naming the file, the line number and the line, with nothing written. Why: two copies of one commit drift at every relock otherwise (bats-lang/quire#821). `relock-pins-test.yml` relocks the scratch caller with a `source-ref` copy and runs the awk program between the `copy-rewrite` markers on `tests/relock-pins/copies`.

  `repin paths-check PATHS` and `repin members-check LISTING PATHS MAX_BYTES` are the repin path rule (#420) written once, in
  `pathrule.bats`, `pathrule_driver.bats`, `sizes.bats` and `fuel.bats` (#466; keyword: repin path rule): a path is refused when it
  is empty, starts with `/` or `-`, ends with `/`, has an empty, `.` or `..` component, has a character other than letters,
  digits and `._/@+=,-`, or has a component that is, in any case, `.git`, `.github`, `.gitmodules` or `.gitattributes`.
  `paths-check` reads the lines of the file PATHS (at least one path, none refused; blank lines are skipped). `members-check`
  reads the listing of a tar (`tar -tv --numeric-owner --quoting-style=escape`) and refuses, as the workflow's Python does:
  more than 100000 members, a line that is no member, a member that is not a regular file or a directory, a name the rule
  refuses (a directory's name has every trailing slash stripped, as tarfile does), a name that is neither a listed path nor
  under one, sizes of regular files that add up to more than MAX_BYTES, and a listed path that is no member. A size and
  MAX_BYTES are digit strings of any length compared exactly (leading zeros stripped, then the length, then the digits; the
  room left is kept as digits and the sizes are subtracted from it; a cap of more than 8200 significant digits is larger than
  any total, so it is unlimited). The files are streams read a byte at a time into one line of 8192 bytes, so any size is
  read; each loop ends on the end of the file and is made total by a fuel of three ints with a lexicographic metric
  (`fuel.bats`, 2^93 - 1 units, a platform assumption that no stream is longer; a gone fuel refuses and never accepts). The
  paths file is read again for each member and the listing for each listed path, so no list of either is held. A refusal is
  printed as a workflow `::error::` command and the status is 1. A name or a path over 8192 bytes is refused: a tree under a
  listed directory can have member names that long, the Python's rule accepts them and its write then fails with ENAMETOOLONG,
  so the run is red in both and nothing is committed. The workflow's two copies of the rule (the shell of job `repin`, the
  Python of `repin-take`) move to these calls in the next piece of #466. The bats `file` package has no unlink, lstat or tar
  reader, so removing a path, the link check of a parent and extracting stay `rm`, `realpath` and `tar` in that step; only the
  rule is ours.

* **The relock resolves each repository's main once (relock heads, #494):** before any line is written, `relock-pins.yml` asks `git ls-remote` for the main of each distinct owner and repository of `workflow-pins` and keeps the answers in a file of one line for each repository; the loop that rewrites the `uses:` lines and the `pin-copies` lines takes the commit of a pin from that file. Two pins of one repository, and a copy listed for both (quire's `pwa-ref` for pwa's `android.yml` and `play-release.yml`), therefore land on one commit even when the repository's main moves while the run goes (quire#851 was the workflow of one commit run with the script of another). No input or output changed. The text between the `pin-moves` markers is the program that the case runs. `relock-pins-test.yml`'s `skew` job builds `tools/pin-audit` and runs `skew_check` (a bats program, run in an empty directory): it extracts that text, runs it with bash on a copy of `tests/relock-pins/skew/workflows/caller.yml` and a stand-in `git` (`git_stand_in`, a bats program on the path under the name git) whose answer differs at every call, compares the caller with `expected.yml` and requires one call for each repository. With the per-pin lookup between the markers the comparison fails: the second pin of the repository and both copies hold the second answer.

* **The previous relock holds the next one back (#545, keyword: relock hold):** the first job of `relock-pins.yml`, `hold`, lists the open pull requests (`gh pr list`, of the repository the workflow runs in, or of the input `pull-requests-repository`, which a test points at its scratch repository) whose head branch starts with `branch-prefix`, leaves out today's branch (a re-run of the same day updates its pull request as before) and a pull request from a fork, and when one is left the run ends green without relocking or pushing anything: `repin` and `relock` do not run, the step summary names the pull request (`owner/repo#N` and its branch), and the new output `held` is its number (empty when none holds the run; `changed` and `patch` are then empty too). The reason: PR 811 (`relock/2026-10-22`) sat red and the next day's relock (PR 819) failed on the same check-pins errors, so a relock on top of an open one only repeats its failures; it is merged or closed first. This replaces the old rule that a new relock closed the older pull request as superseded (that step is gone). The stall report is the third piece of #540 and is not here. `relock-pins-test.yml`'s `hold` relocks with the prefix `relock-hold/`, whose open pull request is bats-lang/relock-scratch#29 (branch `relock-hold/2026-10-01`, a fixture to leave open), `hold-none` with a prefix nothing has, and `hold-check` requires `held` 29 and nothing relocked for the first, and `changed` yes for the second. The job is shell in a workflow because bats has no HTTP client (avenue exhausted: `gh` is the third-party tool used as it is).

* **A workflow the default branch runs is shown running before it merges (#509, keyword: text-lint gated):** text-lint (#487) merged with the lint tool run locally as its only evidence, and on main it failed at its setup step for every pull request (#504): a workflow on `pull_request_target` runs the default branch's file, so the pull request that adds or changes it has no run of it. GitHub's table of events lists 21 events whose `GITHUB_SHA` is the last commit on the default branch (`pull_request_target`, `issue_comment`, `workflow_run`, `schedule`, `repository_dispatch`, `issues`, `label`, `status`, `watch`, `fork`, `public`, `delete` and the rest; `tools/text-lint/gated-triggers.txt` holds all 21, one name on each line). Those workflows are tested where the file can be on the default branch, the fixture repository `bats-lang/relock-scratch`: the workflow (and its caller, with `tools-ref` the commit under test) is put on its main by a pull request there (a merge commit), then a pull request against main is opened, and the run it starts is the real one (the precedent is `relock-pins-test.yml`; a pull request whose base is another branch still ran main's file, relock-scratch#7 and #8). The body of a pull request that changes such a workflow cites that run and its job (`https://github.com/bats-lang/relock-scratch/actions/runs/<run>/job/<job>`) with the complete log of the step that matters. The row `scratch-run` of text-lint refuses the body otherwise: `text_lint event EVENT STATUS URL PHRASES CHANGES BASEDIR TRIGGERS` also reads `CHANGES` (the changed workflow files of the pull request, each `diff --git a/OLD b/NEW` and its patch, from one `gh api .../pulls/N/files --jq` call in `text-lint-check.yml`), `BASEDIR` (a sparse checkout of the base commit, read as data and never run) and `TRIGGERS`; a changed file is gated when one of the 21 is a trigger of it, in its patch or in its base copy (a new file has only its patch; a deleted one is not gated). A trigger is a key or a list item of the block of `on:`, a word of a flow list or of a single event after `on:`, or a word after `Called on:` in a comment (a reusable workflow names the event of its callers so, as `text-lint-check.yml` does); the same word as a permission (`issues: write`), as an option of a trigger (`branches: [public]`) or in a step is not one (`src/gated.bats` reads the block by its indentation, no YAML parser). In a patch the block is read from the lines it shows: git puts the last line that starts a section after the second `@@` of a hunk header, which is `on:` for a hunk inside the block. A body with no job URL of relock-scratch gets one finding for each gated file. The lint cites, it does not open the URL (no network): **the reviewer's checklist for such a pull request is the cited run, not the tool's local run**: open the run and job, check that the workflow file it ran is the one of the head (the commit named in its log), that the step that matters is in the log the body quotes in full, and that it passed (or, for a control, failed where the body says). Limits: a private repository (the `gh api` call needs the pull-requests read permission the callers do not give); a trigger written in a form the line reading does not follow (an `on:` block of a deeper first indentation than its hunk shows, a flow mapping of several lines, an anchor or alias); a reusable workflow that does not carry `Called on:`, which is gated by nothing.

* **An input is removed in two steps (#544, keyword: input-overlap):** pwa#136 replaced `e2e-setup`'s `node-version` input with `node-version-file` and no overlap, and `check-pins` rejected inputs quire still passed: GitHub refuses a `with:` input an action or a reusable workflow does not declare, so a removed or renamed input breaks every caller at its next pin move. The overlap rule above applies to them, and for a pin the relock moves daily one version is one relock cycle (24 hours). `tools/input-overlap` (a bats program, `unsafe = false`) is the check: `input_overlap check BASEDIR HEADDIR OLDDIR CHANGES` reads the paths of CHANGES (one per line, renames as both names); for each that is an `action.yml`/`action.yaml` or a `.github/workflows/*.yml|yaml` file, every input the base declares (an action's `inputs:`, a workflow's `on:` > `workflow_call:` > `inputs:`; `workflow_dispatch` inputs are the dispatcher's and are not read) must be declared by the head, unless OLDDIR (the default branch's commit one cycle before the base's) already marked it deprecated: a `deprecationMessage:` key (GitHub's own, which the runner logs as a warning for a caller that sets the input) or a one-line `description:` that starts with `Deprecated` (a workflow has no `deprecationMessage`). So the first pull request keeps the input working and marks it, the second removes it a cycle after the first merged. Each refusal is a `::error file=...::` line naming the file and the input, the status is 1; a file missing from a checkout reads as having no inputs. Lines, not YAML (`src/inputs.bats`): a flow-style `inputs: {...}` or a multi-line `description: >` are not read; a case-only change of a name is a removal. What it does not check: a changed `type`, `required` or `default` of a kept input, and `secrets:`. `.github/workflows/input-overlap-check.yml` is the shared workflow (inputs: `tools-ref`; on `pull_request`, read-only token, the three checkouts are data and never run; the commit of one cycle ago comes from one `gh api` call and `date`, the avenue exhausted being that bats has no clock or HTTP), this repository's `input-overlap.yml` calls it by path and `tools/pin-audit/templates/input-overlap.yml` is every other repository's caller (by commit); `required.txt` does not list it yet, each repository adopts it in a ticket of its own. `bats test` in `tools/input-overlap` (run by `tools-test.yml`) plays the cases in memory: removed, renamed, whole file gone, kept or added, deprecated a cycle ago and less than a cycle ago, the workflow forms and quoted keys. Research: GitHub documents `deprecationMessage` for action inputs and nothing for a reusable workflow's, and no tool of GitHub or Dependabot enforces an input's overlap, so the check is ours.

This repository's own `verify` is the exception: it checks a new archive
against every package's newest version, which is the point of it.

## A library's check.yml is a caller of package-check.yml

A library's `.github/workflows/check.yml` only calls `.github/workflows/package-check.yml` here, by commit (`uses: bats-lang/repository-prototype/.github/workflows/package-check.yml@<40 hex> # <version>`), on push to main, pull request to main (`types: [opened, synchronize, reopened, ready_for_review]`: GitHub's default three plus the transition to ready) and `workflow_dispatch`. It has no inputs: the library chooses what runs by which test directories it has, never by editing a workflow.

* The existence tests are `hashFiles('<dir>/**') != ''` expressions, so no shell decides anything.
* The lock is always required (the setup action's default `require-lock: 'true'`). `bats check` does not fail on a missing `bats.lock` (without one it fetches the newest of each package), and it refuses a `#use` the lock does not name only when a lock exists. So a package with no dependencies commits the empty `bats.lock` that `bats lock --repository <dir>` writes ("wrote bats.lock (no dependencies)"); adding a dependency without relocking then fails `bats check`.
* A draft pull request runs no job (#525, keyword: draft-ci): each job of `package-check.yml` carries `github.event_name != 'pull_request' || !github.event.pull_request.draft`, so a push to a draft starts nothing that costs runner time and the caller's `check / check` is reported as skipped, not missing (GitHub counts a skipped job as success for a required check; a draft cannot merge in any case). `ready_for_review` in the caller's `types` starts the check on the head when the pull request is marked ready; push, `workflow_dispatch` and the merge queue run unchanged. The caller template is `tools/pin-audit/templates/check.yml`; each library's caller adopts it in a ticket of its own (quire#939).

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

**A package's API or type change is additive: the old form stays beside the new one for one published version, and a test calls it.** This is the overlap rule, one requirement:

* The change adds the new form beside the old one, named by what it adds (as `_proved` is), and both are published in the same version with the old form's original types. A test calls the old form, so an edit cannot drop it.
* A dependent never changes to fit: a package's change must not break its dependents. A dependent moves to the new form later, in a pull request of its own under its own CI.
* A p2 ticket (never p1), filed with the change, removes the old form once every dependent has moved. It is not started while a dependent's newest archive still calls the old form.
* The package is published alone, never together with its dependents as the way to ship a breaking change.

`verify` (`scripts/verify-archives.sh`) is the rule's enforcement: it refuses a change when the latest published version of a package that passed `bats check` before it fails after it. A breaking change is therefore not publishable unless every dependent whose newest archive passed before still passes; the additive change is what keeps them passing.

The review of a pull request that changes a published signature or type checks each one, and a change in place gets `Verdict: changes needed` (the review form of bridge's CLAUDE.md):

* the old form is still there, beside the new one;
* a test calls the old form;
* the package is published alone, and no dependent was changed to fit;
* the p2 ticket that removes the old form exists and was filed with the change.

Precedents in the packages: process's CLAUDE.md, section "Spawn keeps its old signatures; the proved ones are beside them (#61, #64)", and array's `barr_get_inline` beside `barr_get`.

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

* Before pushing, confirm locally what your change needs: `bats check`,
  plus the targeted tests that exercise what you changed (the e2e
  specs, static fixtures or dynamic tests that cover it, and `bats
  build` when the change could break the C or wasm compile). Do not
  run the whole suite locally: the machine is shared by many agents,
  and full local runs overload it.

* Then trust CI to run everything and to say if something unexpected
  broke. A red CI is still yours to root-cause and fix; it is never
  "a flake" and never re-run hoping for green.

* Do not use CI to build things speculatively: push only what the
  targeted local checks have confirmed.

* To get the bats binary: `gh run download --repo bats-lang/bats --name bats-c --dir /tmp/bats-c && cd /tmp/bats-c && PATSHOME=~/.bats/ats2 make && cp release/bats <target>`

## Task Discipline

* Each task must be one concrete action. "all", commas, "and", "do 3 things" are never tasks. Break them down.

* A goal is not a task. "Remove unsafety" is a goal. "Replace `$UNSAFE.cast{arg(T)}` with `_arg_of_int` in `add_string`" is a task.
