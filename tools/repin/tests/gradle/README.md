# Fixtures of `repin gradle` (bats-lang/repository-prototype#413)

`versions.json` is the body of `https://services.gradle.org/versions/all` as the server gave it
on 2026-10-24 (`curl -sS https://services.gradle.org/versions/all`, 533 releases, 429548
bytes). Each directory holds a `gradle-wrapper.properties` of the usual shape (the
`distributionSha256Sum` of its version is that version's published `.sha256` body,
`curl -sSL https://services.gradle.org/distributions/gradle-<version>-bin.zip.sha256`) and
`checksum.sha256`, the published `.sha256` body of the version the case moves to (empty when
the case moves nothing). The tests give each case its `now`.

| Directory | Wrapper | What it shows |
| --- | --- | --- |
| `old-wrapper` | 8.5 | moved to 8.14.6, the newest stable release of major 8, with its published checksum; 9.8.2 is the row `major, not moved` |
| `snapshot-newer` | 9.4.0 | moved to 9.8.2; the snapshot 9.9.0-20261024023353+0000 and the nightly 9.10.0-20261023082214+0000 are newer and 17 days old at the case's `now` |
| `release-candidate-newer` | 9.6.0 | moved to 9.7.1; the release candidates 9.8.0-rc-1 to 3 are newer than 9.7.1 and 8 days old or more at the case's `now` |
| `six-days-old` | 9.6.0 | 9.8.0 is 6 days old (and 6 days less a second): the target is 9.7.1 |
| `seven-days-old` | 9.6.0 | 9.8.0 is exactly 7 days old: the target is 9.8.0 |
| `major-not-moved` | 8.14.6 | the newest of major 8; 9.8.2 is the only row, `major, not moved` |
| `current` | 9.8.2 | the newest stable release: `current` |
| `too-new` | 9.8.1 | the only newer release, 9.8.2, is 4 days old: `too new` |

The real body has no release with a plain version tag that is a snapshot, a nightly or has an
`rcFor` (Gradle spells those versions with a suffix), so the tests plant small versions texts
for the three flags in `build/repin-tests`.
