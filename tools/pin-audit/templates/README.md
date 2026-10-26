# Caller templates

`check.yml`, `relock.yml`, `publish.yml` and `text-lint.yml` (bats-lang/repository-prototype#487: the pull request body lint; its two `@@COMMIT@@` holes are the same commit in a real caller, and `tools/pin-audit/required.txt` makes the file required in every repository) are the exact text of the workflow
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

## ISSUE_TEMPLATE

`ISSUE_TEMPLATE/ticket.md` is the canonical ticket template (bats-lang/repository-prototype#406),
the text of that ticket's "The canonical template" byte for byte. It has no hole: a file under
`.github/ISSUE_TEMPLATE/` of a repository passes when its bytes equal a `*.md` file of this
directory, or when it is listed by hash with a ticket comment in `allowlist.txt` as the workflow
files are, and never both. Nothing is parsed: not YAML, not Markdown.
