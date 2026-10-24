# Fixtures of `repin npm` (bats-lang/repository-prototype#412)

Each directory is one real run of pnpm 12.9.1 on a scratch project with one dependency, on
2026-10-24, and holds:

* `outdated.json`: the output of `pnpm outdated --format json`;
* `compatible.json`: the output of `pnpm outdated --format json --compatible`;
* `times.txt`: the registry's publish times of every version of the package, as `<name>
  <version> <published seconds>` lines (`pnpm view <name> time --json`, the keys `created` and
  `modified` left out, each time as whole seconds since the epoch).

pnpm's `wanted` is the version of the lockfile, so `outdated.json` alone does not say where the
range ends; the `latest` of `compatible.json` does (and it lists nothing for a dependency
already at the end of its range).

| Directory | Dependency installed, range | What it shows |
| --- | --- | --- |
| `semver-minor` | semver 7.0.0, `^7.0.0` | an in-range minor |
| `semver-patch` | semver 7.8.4, `~7.8.0` | an in-range patch |
| `psl-old` | psl 1.13.0, `^1.0.0` | psl 1.15.0 is its last release: at 6 days, at exactly 7 days and 1 second short of 7 days after 1.15.0 was published |
| `psl-last` | psl 1.14.0, `^1.0.0` | the only newer version is under 7 days: too new |
| `typescript` | typescript 6.0.2, `^6.0.0` | 6.0.3 in range, 7.0.2 a major |
| `semver-current` | semver 7.5.4, `~7.5.0` | at the end of its range; 7.8.5 is outside it |
| `uuid-open` | uuid 8.3.1, `>=8.0.0` | the range allows 14.0.3, a higher major |
