#!/bin/sh
# Checks the archives a change adds to this repository:
# - published archives and sidecars are only ever added, never modified
#   or removed (a published version never changes);
# - every added archive has its .sha256 sidecar, and the sidecar matches;
# - every added package passes bats lock + bats check against this
#   repository as the change leaves it (so a package published without
#   its updated dependents, or against a missing dependency, fails here).
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
exit $fail
