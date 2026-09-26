#!/bin/sh
# Checks the archives a change adds to this repository:
# - published archives and sidecars are only ever added, never modified
#   or removed (a published version never changes);
# - every added archive has its .sha256 sidecar, and the sidecar matches;
# - every added package passes bats lock + bats check against this
#   repository as the change leaves it;
# - no package regresses: the latest published version of every package
#   that passed bats check against the repository before the change
#   still passes after it (so publishing an API change without its
#   updated dependents fails here). Packages already failing before the
#   change (superseded ones, say) do not block it.
#
# usage: scripts/verify-archives.sh <base-commit>   (bats must be on PATH)
set -eu
BASE=$1
ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"
if command -v sha256sum >/dev/null 2>&1; then SUM="sha256sum"; else SUM="shasum -a 256"; fi
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail=0

git diff --no-renames --name-status "$BASE" HEAD -- '*.bats' '*.bats.sha256' > "$TMP/changes"
while read -r st path; do
  [ "$st" = "A" ] || { echo "FAIL: $path is $st: published archives are never modified or removed"; fail=1; }
done < "$TMP/changes"

n=0
for arc in $(awk '$1 == "A" && $2 ~ /\.bats$/ { print $2 }' "$TMP/changes"); do
  n=$((n + 1))
  if [ ! -f "$arc.sha256" ]; then echo "FAIL: $arc has no sidecar"; fail=1; continue; fi
  if ! (cd "$(dirname "$arc")" && $SUM -c "$(basename "$arc").sha256" >/dev/null); then
    echo "FAIL: $arc does not match its sidecar"; fail=1; continue
  fi
  w="$TMP/pkg$n"
  mkdir -p "$w" && (cd "$w" && unzip -q "$ROOT/$arc")
  if (cd "$w" && bats lock --repository "$ROOT" && bats check --repository "$ROOT") > "$w.log" 2>&1; then
    echo "ok   $arc"
  else
    echo "FAIL: $arc does not pass bats check against this repository"; grep -E 'error' "$w.log" | head -5; fail=1
  fi
done
[ "$n" -gt 0 ] || echo "no archives added"

# The latest non-dev archive in directory $2 of the repository at $1
latest() { ls "$1/$2"/*.bats 2>/dev/null | grep -v 'dev1\.bats$' | sort -V | tail -1; }
# Whether the archive $2 passes bats lock + bats check against repository $1
passes() {
  w=$(mktemp -d "$TMP/chk.XXXXXX")
  (cd "$w" && unzip -q "$2" && bats lock --repository "$1" && bats check --repository "$1") > "$w.log" 2>&1
}

if [ "$n" -gt 0 ]; then
  git worktree add -q --detach "$TMP/base" "$BASE"
  for dir in $(git ls-files '*.bats' | grep / | xargs -n1 dirname | sort -u); do
    head_arc=$(latest "$ROOT" "$dir")
    [ -n "$head_arc" ] || continue
    grep -qx "A	${head_arc#$ROOT/}" "$TMP/changes" && continue
    passes "$ROOT" "$head_arc" && continue
    head_log="$w.log"
    base_arc=$(latest "$TMP/base" "$dir")
    if [ -n "$base_arc" ] && passes "$TMP/base" "$base_arc"; then
      echo "FAIL: ${head_arc#$ROOT/} passed bats check before this change and fails after it"
      grep -E 'error' "$head_log" | head -3; fail=1
    fi
  done
  git worktree remove --force "$TMP/base"
fi
exit $fail
