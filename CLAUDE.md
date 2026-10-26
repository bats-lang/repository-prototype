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
  commits the empty one `bats lock` writes). CI never runs `bats lock` for the package: `bats check` and
  `bats build` fetch exactly the locked versions, and fail when the lock
  does not match `bats.toml`; the setup action fails when it is missing. A library's lock pins only
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

* **This repository's own relock (#448):** `.github/workflows/relock.yml` is the caller template filled (minute 7, `relock-pins.yml` by commit with the comment `repository-prototype main <7 hex>`), so the audit passes it by template. It moves `.github/bats-version` and `.github/repository-version` (they exist here, so the shared workflow moves them) and the third-party action pins; it has no `bats.lock` to relock. The template lists `publish.yml`, `package-check.yml` and `relock-pins.yml` as workflow pins, and this repository calls the first two by path inside itself (`./`) or not at all, so in the repository that hosts a pinned workflow `relock-pins.yml` leaves a mention that is not a plain `uses:` line alone and skips a pin no plain line calls (an `::notice::`); every other repository is still refused for such a line and still fails for a pin nobody calls. A repository with no `.github/workflows/<check-workflow>` has nothing to dispatch on the relock branch (a notice); with `RELOCK_TOKEN` the pull request's own checks run (`verify.yml` on every pull request, `tools-test.yml` when a pin file changes). The npm and Gradle steps leave `tests/relock-pins` alone in a run of that repository (the input `hosting-repository`, default `bats-lang/repository-prototype`, compared with `GITHUB_REPOSITORY`; #452), since its fixtures are outdated on purpose and the template passes no ignore input; `relock-pins-test.yml` names another repository for the calls that relock a fixture (a foreign caller moves it as before) and `fixtures-own` shows the own side.

* **The version comment:** `relock-pins.yml` writes `uses: <pin>@<commit> # <repo> main <first 7 hex of the commit>` (`<repo>` of `<owner>/<repo>`) for every workflow pin line, replacing the comment the line had (a line holding the pin that is not a plain `uses:` line, as a quoted value, flow style or a commented-out line, fails the step and is never written back), because `bats check-pins` fails a commit with no comment saying which version it is; the caller templates' `@@COMMENT@@` takes that text (#395). `.github/workflows/relock-pins-test.yml` relocks a scratch caller (`tests/relock-pins/workflows`, `publish: 'false'`) and fails when a moved line lacks the comment, and runs the step's awk on `tests/relock-pins/rewrite` (a wrong comment healed, the one form kept, other spellings refused).

* **Copies of a pin's commit:** a reusable workflow cannot read its own ref, so a caller may repeat a pin's commit as an input (quire's `pwa-ref`, which pwa's `android.yml` and `play-release.yml` read). `relock-pins.yml`'s input `pin-copies` lists them, `<owner>/<repo>/<path> <input>` one per line: after a pin moves, every `<input>: <40 hex>` line of the files that call the pin gets the commit the pin got, comment after it kept, and any other spelling of that key (quoted, an expression, not 40 hex) fails the step naming the file, the line number and the line, with nothing written. Why: two copies of one commit drift at every relock otherwise (bats-lang/quire#821). `relock-pins-test.yml` relocks the scratch caller with a `source-ref` copy and runs the awk program between the `copy-rewrite` markers on `tests/relock-pins/copies`.

* **The regenerate command (bats#299, #344):** a caller that commits something derived from its lock (bats's `bootstrap/c`) gives `relock-pins.yml` the inputs `regenerate` (a shell command) and `regenerate-paths` (the files and directories it writes, one per line; required with `regenerate`). It is trusted as the compiler is: it builds and runs the newest packages, which we published through reviewed pull requests, so there is one `relock` job and no validator of the paths (repository-prototype#342 had split it into three jobs with a path rule in Python and again in shell; those are gone, as code in languages we do not write). The order of the steps is the design: the relock is made and staged; the command runs in a step of its own with `GH_TOKEN`, `GITHUB_TOKEN` and `RELOCK_TOKEN` emptied (the checkout keeps no credentials) and `regenerate-timeout-minutes`; the listed paths are then staged as they are (deletions included) and the patch outputs are made from the index; only the last step holds the token, commits the index (so a file written anywhere unlisted is not in the commit) and pushes. A failing command ends the run red before the push step, so nothing is pushed and the day's existing relock branch is not replaced. `concurrency` (`relock-pins-<repository>-<branch-prefix>`), `branch-prefix` and the timeouts are as #342 made them; `regenerate-max-bytes` is accepted and limits nothing; the patch outputs are written to a file, not an environment variable, so the pull request has no size limit of ours, and a patch of 400000 characters or more is not an output, since a job's outputs together may not exceed 1,048,576 bytes (GitHub failed bats's evidence run at the end of the job, after the push, with a patch under 800000 characters); a run that does not publish fails, one that publishes leaves `patch` empty. `relock-pins-test.yml` runs a command that derives a file from the moved pin, deletes a tracked file and writes an unlisted one (`regenerate`, `regenerate-check`), and a dispatch with `refusal` `regenerate-fails` runs a failing command through the whole workflow. The step that stages the relock lists the tracked npm and Gradle files with `git ls-files` and stages only those (`git add -u -- <pathspec>` exits 128 for a pathspec nothing tracked matches, which broke a repository with no `package.json`, as bats is; the staging had that defect since #415); `relock-pins-test.yml`'s `bare` relocks a base commit that tracks none of those files.

* **The repin command:** a caller whose pins are not `uses:` lines (pwa's Android SDK revisions, quire's `pwa-ref`) gives `relock-pins.yml` the inputs `repin-command` and `repin-paths` (both default to off, and then the run is the relock it was). The command runs in a job of its own (`repin`: `permissions: {}`, no RELOCK_TOKEN, no credentials, a timeout) on the base, before the relock decides whether anything changed; it may rewrite files under `repin-paths` only and appends move records (`tools/repin` format, a kind word of its own) to the file named by `REPIN_RECORDS`. The job refuses the run (red, and `relock` does not run, so nothing is pushed) when the command fails, when anything outside the paths was changed, made or removed (tracked, untracked and ignored files, compared with the checkout before the command), when a listed path is gone or holds a link, or when a path breaks the repin path rule (stated in the header of `relock-pins.yml`; it is #420's own, and is still written twice, in the shell of `repin` and in the Python of `relock`'s `repin-take` step, a follow-up of repository-prototype#344 which removed the regenerate command's two copies). The `relock` job takes the files as data (the `repin-take` Python, nothing extracted by tar) before the pins move, so they count in "anything changed?" and travel in the patch with the pins, and renders the records with `tools/repin table` as the section `### Moved by the repin command` of the pull request body (a line that is not a record fails the run). A run where nothing moved opens no pull request and says so in the step summary. The workflow's output `body` (the pull request's text, base64) is #414's; this change adds the section of the repin records after `### Actions` to that text. `relock-pins-test.yml` runs the workflow with a command that moves a fixture file (`tests/relock-pins/repin`) and writes a record, with one that moves nothing and with none of the inputs, runs the script between the `repin-check` markers on fixture repositories, and a dispatch with the input `refusal` plays one refused command through the whole workflow (#420).

* **The audit:** `tools/pin-audit` (a bats program, `unsafe = false`; run it at the root of this checkout after `bats build`) clones the default branch of every non-archived repository of the organisation (`gh api --paginate orgs/bats-lang/repos`, then `git clone --depth 1` into `audit-clones/<name>`) and passes each workflow file and each file under `.github/ISSUE_TEMPLATE/` (git `ls-tree` of `.github/workflows/` and `.github/ISSUE_TEMPLATE/`; any entry there, a directory or a link included, is judged and fails if it is not a readable file; #406) when exactly one of these holds, and fails it as "not canonical" otherwise: its sha256 is listed with its repository and path in `tools/pin-audit/allowlist.txt`, or its bytes are one of `tools/pin-audit/templates/*.yml` with the holes filled (for a file under `.github/ISSUE_TEMPLATE/`: one of `tools/pin-audit/templates/ISSUE_TEMPLATE/*.md`, today the canonical `ticket.md`, which has no hole, so byte for byte) (the template is split at its markers and each segment is compared byte for byte; `@@COMMIT@@` is 40 lowercase hex digits, `@@COMMENT@@` printable ASCII to the end of the line, `@@MINUTE@@` one or two digits). It reads no YAML, and has no line rule or per-job rule. A file that is both listed and a template fails, so an entry is dropped when its file becomes a caller. An allowlist entry is `<repository>/<path> <sha256> [<next sha256>] # <comment>`: the second hash is the next one, so a repository that changes a bespoke file first adds the new hash here, then changes the file, then a later pull request drops the old hash; every entry's comment names the ticket that says to fix the file (`<repository>#<number>`), so no exception is permanent. An entry with no such comment, a malformed entry and a repeated file fail the audit. A path over 255 bytes, a file over 524288 bytes and a failing clone are failures of their own, said and counted; the exit status is 1 when anything fails. `bats test` in `tools/pin-audit` plants repositories with `git init` and runs the built `dist/debug/pin_audit` against them, and `bats test` in `tests/verify-archives` does the same for `scripts/verify-archives.sh` with a stand-in `bats`; `.github/workflows/tools-test.yml` runs both.

* **The audit's options and its tickets (#405):** `pin_audit --repository <name>` audits that repository alone (one shallow clone, no list of the organisation, exit 0 only when it passes, 2 for arguments it does not take); it never files a ticket, so it is the check a ticket's Done-when names. After each clone the audit runs `env -C audit-clones/<name> bats check-pins --discover` (the process package has no working directory, so GNU `env -C` sets it; the compiler is the one on PATH, built from the commit in this repository's `.github/bats-version`, which the daily `relock.yml` moves to the newest bats main together with `.github/repository-version`; the audit workflows and `tools-test.yml` read both files through the setup action, so no pin of the audit's compiler is moved by hand, #448) and a nonzero exit is a failure of the repository, its failures printed under the repository's name; a repository with no workflow, action, `package.json` or `ats2.bats` fails it too (status 2). `pin_audit --file-tickets` (the weekly `.github/workflows/pin-audit.yml` passes it, with `GH_TOKEN` set from the secret `AUDIT_TOKEN`, #408) files one ticket, titled `Make <repository>'s workflow and issue-template files canonical` and labelled `p0`, in each repository that has a file that is not canonical: the body has each such file's path and the template of the same file name with its holes filled (the commit of this checkout, the comment `repository-prototype main <7 hex>`, the minute that follows the template's own text before the hole in the current file, else 17; a file with no template of its name says so and shows its sha256), and ends with the Done-when `pin_audit --repository <name>` exits 0. `gh issue list` finds an open ticket of that exact title: its body is replaced (`gh issue edit`) and nothing is created. A passing repository gets no call; an empty `GH_TOKEN` exits 1 saying `AUDIT_TOKEN` is missing, before anything is cloned. The audit opens no pull request. Its tests use `gh_stand_in`, which records each `gh issue` call in `gh-calls.txt`.

* **The skip list (#430):** `tools/pin-audit/skipped.txt` is the one list of repositories the audit does not audit, `<repository> <reason>` on each line (exact names, no pattern, the reason required; `#` lines and blank lines are not entries; a line that is neither fails the audit). A listed repository is neither cloned, checked nor ticketed: the audit prints `== <name>: skipped, listed in tools/pin-audit/skipped.txt (not cloned, no ticket)` and names it in its summary line (`; skipped (tools/pin-audit/skipped.txt): <count> <names>`). Today it holds `relock-scratch`, the fixture of the shared relock whose non-canonical workflow files and version ranges are what it tests. The tests plant a listed and an unlisted diverging repository (`test_skipped_repository_is_neither_cloned_nor_ticketed`).

* **The pin mover:** `tools/repin` (a bats program, `unsafe = false`) holds what every kind of pin
  move shares: the move record (one tab-separated line for each pin examined: kind, name, old,
  new, release age in whole days, status `moved`, `major, not moved`, `too new` or `current`; the
  kind is a plain word, so a new kind adds rows and no field), the release age rule (a release is
  a candidate only when it was published at least 7 days, 604800 seconds, before `now`, which is
  always an argument and never the clock, so a fixture is exact) and the Markdown table of the
  relock pull request body. `repin table RECORDS` prints the table of a records file and names the
  first bad line; `repin age NOW PUBLISHED` says whether a release is a candidate; `repin actions
  DIR NOW RELEASES` moves the action pins of the workflow files of DIR. The releases file has one
  line for each release, `<owner>/<repo> <tag> <commit> <published seconds>` (the commit a tag
  points to, an annotated tag already followed). A pin is `uses: <owner>/<repo>[/<path>]@<40 hex>
  # <version tag>`, the spelling `relock-pins.yml`'s awk accepts: it moves to the highest version of
  its major that is a candidate and higher than the pin, with that tag as the comment; a higher
  major is `major, not moved`, a higher version under 7 days is `too new`; `bats-lang/*` pins and
  the lines between the `pin-rewrite` markers are left alone. A line that holds a pin in another
  spelling is refused, and then no file is written (every file is rewritten in memory first). It
  reads the files it is given, makes no network call, reads no YAML and no file's time. Its tests
  are `bats test` in `tools/repin`, run by `.github/workflows/tools-test.yml`; a record or time the
  tests take as text is plain bytes, so they build their input in memory, and the directory cases
  plant files under `build/repin-tests`.
  `repin npm OUTDATED COMPATIBLE TIMES NOW UPDATES` decides the npm
  moves (npm.bats): OUTDATED is `pnpm outdated --format json`, COMPATIBLE its `--compatible` form (whose
  `latest` is the end of the range: pnpm's `wanted` is the lockfile's version), TIMES has a line
  `<name> <version> <published seconds>` for each version; a dependency moves to the newest version of
  its major, higher than the current one and inside the range, that is a candidate (7 days), the
  `name@version` lines of the moves are written to the file UPDATES, and a `latest` of a higher
  major is its own row, `major, not moved`, never a target (fixtures: `tools/repin/tests/npm`).
  `repin gradle PROPERTIES VERSIONS CHECKSUM NOW UPDATES` decides the move of a
  `gradle-wrapper.properties` (gradle.bats): PROPERTIES is read by line (`distributionUrl` must be exactly
  `https\://services.gradle.org/distributions/gradle-<version>-bin.zip`, `distributionSha256Sum` 64 lowercase
  hex digits; any other spelling of either key is refused, naming its line), VERSIONS is the body of
  `https://services.gradle.org/versions/all` (a release is stable when it has no `snapshot`, no `nightly`, no
  `rcFor` and a plain version tag; its `buildTime` is its published time, zone offset applied), CHECKSUM is the
  `.sha256` body of the target (read only when the pin moves, copied as it is, never computed). The target is the
  highest stable release of the wrapper's major that is higher than it and at least 7 days old; the version and the
  checksum, a line each, are written to the file UPDATES (an empty file when nothing moves), and the highest stable
  release of a higher major is its own row, `major, not moved` (fixtures: `tools/repin/tests/gradle`).
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

* **The relock moves the action pins (#414):** after the workflow pins, `relock-pins.yml` builds `tools/repin` (from the package repository its setup step cloned) and runs `repin actions` over `workflows-directory` at the clock's time. Its releases file is written by the step `Collect the releases of the actions`: the third-party `owner/repo` of the `uses:` lines (found as text; `bats-lang/*` is left to the workflow pins), `gh api` for each repository's releases (no draft, no prerelease) and `git ls-remote --tags` for the commit of each tag (the peeled `^{}` line when the tag is annotated). A move is a line of the relock patch like a workflow pin's; the move records (kind, name, old, new, release age, status) are the section `### Actions` of the pull request body, rendered by `repin table`, one row for each pin examined (a newer major is `major, not moved`, a newer release under 7 days `too new`). Without a `RELOCK_TOKEN` a workflow file cannot be changed (and a run that publishes nothing keeps the moves), so the records with status `moved` are not in the table: they are a list of `not moved` lines with the reason, as the workflow pins are (the awk programs between the `actions-left` and `actions-bullet` markers). The inputs `actions-releases` (a file of the checkout in repin's releases format) and `actions-now` (whole seconds) replace the two sources for a test and default to off; the output `body` is the pull request's text, base64. `relock-pins-test.yml` runs the workflow on `tests/relock-pins/actions` (patch and section compared with `expected.patch` and `expected-section.md`; a directory whose pins are all current gives `changed` no), on a real outdated `actions/checkout` pin with the releases fetched from GitHub, and the awk programs on fixture records. Records of other kinds (quire#821's `pwa-ref`, pwa#173's Android SDK pins, repository-prototype#420's `repin-command`) join the same pull request body as sections of their own.

* **The relock moves the npm dependencies (#415):** `relock-pins.yml` finds each directory with a `package.json` and a `pnpm-lock.yaml` (`find`, `node_modules` and `.git` left out, the directories of the input `npm-ignore` left out), and in each, with the repository's pinned pnpm (`packageManager`, run as `corepack pnpm`; Node by `.nvmrc` through setup-node when the checkout has the file the input `npm-node-version-file` names, else the runner's), lists the projects (`pnpm -r ls --depth -1 --json`: a workspace's members are the ones pnpm names, no lock is read), runs for each `pnpm outdated --format json` and its `--compatible` form, writes the registry publish time of every version of the majors in play (`pnpm view <name> time --json`, as `<name> <version> <seconds>` lines, at most 524288 bytes: `repin` refuses a larger file) and runs `repin npm` at the clock's time (`npm-now` replaces it for a test). Its update lines go to `pnpm update --lockfile-only --ignore-scripts name@version...`: no `--latest` (a major is never taken), no install (no script of the repository or of a package runs). A directory whose `package.json` has no `packageManager` of pnpm fails the run. The moved `package.json` and `pnpm-lock.yaml` (tracked files only) are in the relock patch; the records are the section `### npm` of the pull request body, after `### Actions` and before the repin command's records (a newer major is `major, not moved`); a run where nothing moved opens no pull request; a repository with no `pnpm-lock.yaml` is untouched. The step needs no RELOCK_TOKEN. `relock-pins-test.yml` relocks `tests/relock-pins/npm/project` (semver 7.0.0 under `^7.0.0`, uuid under `~8.3.2`) and `tests/relock-pins/npm/current` at a fixed time, and every other call gives `npm-ignore: tests/relock-pins/npm`.

* **The relock moves the Gradle wrapper (#416):** `relock-pins.yml` finds each `gradle/wrapper/gradle-wrapper.properties` (`find`, `node_modules` and `.git` left out, the directories of the input `gradle-ignore` left out). It fetches `https://services.gradle.org/versions/all` once (`jq -c`, so the text stays far under the 524288 bytes `repin` reads), runs `repin gradle` (#413) with a placeholder checksum of 64 zeros to learn the target, fetches the target's own `gradle-<version>-bin.zip.sha256` (copied, never computed), runs `repin gradle` again with it (which refuses anything but 64 lowercase hex digits) and then Gradle itself writes the files: `./gradlew wrapper --gradle-version <version> --gradle-distribution-sha256-sum <sha256>` twice in the wrapper's project (the old wrapper writes the properties, the new Gradle the scripts and the jar), under the JDK of `.java-version` (`actions/setup-java` when the checkout has the file the input `gradle-java-version-file` names, else the runner's) with `--project-cache-dir` outside the checkout so no file is left behind. The properties must then hold exactly the target's `distributionUrl` and `distributionSha256Sum` lines, else the step fails. The wrapper's tracked files (properties, jar, `gradlew`, `gradlew.bat`) are in the relock patch and the records are the section `### Gradle` of the pull request body, after `### npm` (a newer major is `major, not moved`, a release under 7 days `too new`); the relock pull request is dispatched to the repository's `check.yml` as always, so its Gradle wrapper validation and the rest of its CI run on the moved head. A repository with no wrapper is untouched; a run where nothing moved opens no pull request. The step needs no RELOCK_TOKEN. Because a wrapper's jar makes the patch about 100000 characters (gzipped, base64; the diff holds the jar in both directions), the patch travels in up to 8 pieces of 100000 characters: the output `patch` is its first 100000 characters (the whole patch when it is shorter, as before) and `patch-part-2` to `patch-part-8` the rest; a change of 400000 characters or more is not an output (see the regenerate command above; #344 lifted the limit on the pull request text). All additions are inputs `gradle-now`, `gradle-java-version-file`, `gradle-ignore` and outputs `patch-part-2` to `patch-part-8`, with defaults; no input or output changed. `relock-pins-test.yml` relocks `tests/relock-pins/gradle/project` (wrapper 8.5, JDK 17) at the fixed time 2026-10-24T12:00:00Z (`gradle-now`: 8.14.6, checksum compared with the published `.sha256` in the check) and `tests/relock-pins/gradle/current` (8.14.6: nothing moves), and every other call gives `gradle-ignore: tests/relock-pins/gradle`.

* **The pull request body lint (#487):** `tools/text-lint` (a bats program, `unsafe = false`; keyword: text-lint) is the form of a pull request body that bats-lang/quire's `tests/static/guidelines.py --pr-body` checked, for every repository of the organisation. `text_lint body BODY HEAD [PHRASES]` prints the findings of a body file, one line each (`ok` and success when there is none); `text_lint event EVENT STATUS URL [PHRASES]` reads the JSON of a pull request event (`GITHUB_EVENT_PATH`), prints the findings and writes the commit status to post (`state`, `context` `text-lint`, `description` the first finding in ASCII and cut short, `target_url`). The checks, each named at the end of its finding: `first-line` (the first line is `Fixes #N` or `Fixes owner/repo#N`), `one-ticket` (every `Fixes` names the same ticket), `head` (a line `Head: <commit SHA>` is there and the last one is the head), `evidence` (an `Evidence` heading and a fenced block that starts with `$ <command>`), `footer` (the body ends with the generated-by footer of the template, `_Generated by [Claude Code](https://claude.ai/code)_` or the robot line of the PR template, holds exactly one, and no session URL) and the phrases of `tools/text-lint/phrases.txt`. That file has a line for each phrase: a label, a pattern, an example the pattern matches and what to do instead, separated by tabs; the patterns are the text phrases of quire's `phrases.tsv` in the small pattern language of `src/pattern.bats` (a character, `\s`, `\d`, `\w`, `\b`, a class, and `?`, `+`, `*` on one atom; no group and no alternation, so an alternative is a line of its own; searched without regard to case). A relock branch (`relock/`) and a login that ends with `[bot]` are exempt (status success, `exempt`). It reads no YAML and makes no network call; what does not fit its buffers is refused by the types, and a refused event writes no status. `.github/workflows/text-lint-check.yml` is the shared workflow: it checks out this repository at the input `tools-ref` (a reusable workflow cannot read its own ref, so the caller repeats its commit; `relock-pins.yml`'s `pin-copies` keeps the two equal), builds the lint, runs `text_lint event`, and posts the status with `gh api` on the pull request's head; a newer edit cancels the older run. The caller is `.github/workflows/text-lint.yml` of each repository, `tools/pin-audit/templates/text-lint.yml` with its holes filled (event `pull_request_target`, types opened, edited, synchronize, reopened); this repository's own is allowlisted, since it calls the shared workflow by path with `tools-ref` the base commit, as `package-check.yml` is called, and has no pin to move. `tools/pin-audit/required.txt` lists the workflow files every audited repository must have: a repository without one fails the audit as one file not canonical (`missing`) and its ticket shows the template filled. `tools-test.yml` builds and tests the lint (`bats test` in `tools/text-lint`: a fixture body for each check and each kind of phrase in `tests/bodies`, events in `tests/events`, and the example of every phrase line found by its line).

This repository's own `verify` is the exception: it checks a new archive
against every package's newest version, which is the point of it.

## A library's check.yml is a caller of package-check.yml

A library's `.github/workflows/check.yml` only calls `.github/workflows/package-check.yml` here, by commit (`uses: bats-lang/repository-prototype/.github/workflows/package-check.yml@<40 hex> # <version>`), on push to main, pull request to main and `workflow_dispatch`. It has no inputs: the library chooses what runs by which test directories it has, never by editing a workflow.

* Always: the bats setup action, `bats check`, `bats test` (unit tests live in `src/`; a package with none prints "no tests found" and passes).
* `tests/static/` exists: `tests/static/run.sh "$REPOSITORY"`. `tests/dynamic/` exists: valgrind is installed and `tests/dynamic/run.sh "$REPOSITORY"` runs; when `tests/dynamic/package.json` exists too, Node (`.nvmrc`) and `npm ci` run first. `tests/c/` exists: `tests/c/run.sh` on ubuntu-24.04 and macos-26. A directory that exists must hold its `run.sh`; the step fails otherwise.
* The existence tests are `hashFiles('<dir>/**') != ''` expressions, so no shell decides anything.
* The lock is always required (the setup action's default `require-lock: 'true'`). `bats check` does not fail on a missing `bats.lock` (without one it fetches the newest of each package), and it refuses a `#use` the lock does not name only when a lock exists. So a package with no dependencies commits the empty `bats.lock` that `bats lock --repository <dir>` writes ("wrote bats.lock (no dependencies)"); adding a dependency without relocking then fails `bats check`.
* The job shows in a caller as `check / check` (caller job / called job).

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
