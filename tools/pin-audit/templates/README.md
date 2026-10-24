# Caller templates

`check.yml`, `relock.yml` and `publish.yml` are the exact text of the workflow
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
