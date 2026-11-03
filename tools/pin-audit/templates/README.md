# Caller templates

`check.yml`, `relock.yml`, `publish.yml` and `text-lint.yml` (bats-lang/repository-prototype#487: the pull request body lint; its `@@COMMIT@@` holes are the same commit in a real caller, and `tools/pin-audit/required.txt` makes the file required in every repository) are the exact text of the workflow
files a library repository commits at `.github/workflows/`; `review-gate.yml` and
`review-gate-relay.yml` are bridge's two files at bridge commit
`d8d68f6e9302db86c4b6afb042238df2859bdd92` byte for byte, with no holes. Each is compared as
bytes: split at the markers below, every segment equal, every hole value in its
character class. Nothing else in a template is a hole, and a template is never
parsed as YAML.

| Marker | Character class | Where the value comes from |
|---|---|---|
| `@@COMMIT@@` | exactly 40 lowercase hex digits `[0-9a-f]` | The commit of repository-prototype whose workflow the `uses:` line calls. The daily relock writes it, together with `.github/repository-version`. |
| `@@COMMENT@@` | one or more printable ASCII characters (space to `~`), no line break; the rest of the `uses:` line after `# ` | The version comment `bats check-pins` requires. The relock writes it with the commit, in the form `repository-prototype main <7 hex>` (the first 7 digits of the commit). |
| `@@MINUTE@@` | one or two decimal digits | The minute of the repository's own daily relock cron line (`'<minute> 5 * * *'`). It is chosen once per repository and the relock never moves it. |

`@@COMMIT@@` follows the `@` of the `uses:` line, so a filled line reads
`...relock-pins.yml@<40 hex> # <comment>`.

## relock-regenerate.yml (bats-lang/repository-prototype#541)

`relock-regenerate.yml` is the second relock caller (after `relock.yml`): the compiler's (bats-lang/bats), which calls only `relock-pins.yml` (so `workflow-pins` lists that one), passes `regenerate` and `regenerate-paths` (it rewrites `bootstrap/c` after a moved lock) and has a `concurrency` group. It has the same three holes as `relock.yml`. The audit tries every `*.yml` here, so a `relock.yml` passes when it equals any of the relock templates (`relock.yml`, `relock-regenerate.yml`, `relock-repin.yml`); an allowlist entry cannot hold such a file, since the daily relock changes its bytes. The ticket text of a failing `relock.yml` shows the file of the same name, so `relock.yml` here, not this one.

## relock-repin.yml (bats-lang/repository-prototype#563)

`relock-repin.yml` is the third relock caller and is pwa's: it calls `relock-pins.yml` with `repin-command` and `repin-paths` (the Android SDK pins, `tools/android-sdk-pins`) and `npm-ignore`, which no other template has. The text is pwa's `.github/workflows/relock.yml` byte for byte except the three holes (`@@MINUTE@@`, `@@COMMIT@@`, `@@COMMENT@@`, as in `relock.yml`); it has no hole for the paths, so the command and the paths are part of the template and a change of either in pwa is a change of this file first. An allowlist entry cannot hold it, since the daily relock moves its `relock-pins.yml@<commit>` pin. The ticket text of a failing `relock.yml` shows the file of the same name, so `relock.yml` here, not this one.

Since bats-lang/repository-prototype#567 the template also moves the text-lint pin: the line `bats-lang/repository-prototype/.github/workflows/text-lint-check.yml` is in `workflow-pins` after `relock-pins.yml`, and the input `pin-copies` (`bats-lang/repository-prototype/.github/workflows/text-lint-check.yml tools-ref`) keeps the `tools-ref` copy of `text-lint.yml` equal to that pin. `relock-repin-before-text-lint.yml` is the old form (the template as #563 made it, without those lines), kept for one cycle by the overlap rule so that pwa's current `relock.yml` keeps passing the audit until pwa adopts the new form; it is removed by bats-lang/repository-prototype#569 (p2), which is not started while pwa's `relock.yml` still equals it.

## input-overlap.yml (bats-lang/repository-prototype#544)

`input-overlap.yml` is the caller of `input-overlap-check.yml`, which fails a pull request that removes an input of an action or a reusable workflow before the default branch marked it deprecated a relock cycle earlier. It has the holes `@@COMMIT@@` (twice, the same commit) and `@@COMMENT@@`. It is not in `required.txt`: each repository adopts it in a ticket of its own.

## ISSUE_TEMPLATE

`ISSUE_TEMPLATE/ticket.md` is the canonical ticket template (bats-lang/repository-prototype#406),
the text of that ticket's "The canonical template" byte for byte. It has no hole: a file under
`.github/ISSUE_TEMPLATE/` of a repository passes when its bytes equal a `*.md` file of this
directory, or when it is listed by hash with a ticket comment in `allowlist.txt` as the workflow
files are, and never both. Nothing is parsed: not YAML, not Markdown.
