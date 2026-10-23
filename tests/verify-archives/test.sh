#!/bin/sh
# Tests scripts/verify-archives.sh on scratch repositories: a .bats source file
# deep in the tree is not an archive (passes); an archive added without its
# sidecar fails, at the root, in a package directory and in a namespace's
# package directory; a modified archive fails. None reaches `bats`.
# usage: tests/verify-archives/test.sh
set -eu
SCRIPT=${SCRIPT:-$(cd "$(dirname "$0")/../.." && pwd)/scripts/verify-archives.sh}
W=$(mktemp -d)
trap 'rm -rf "$W"' EXIT
git_() { git -c user.email=t@example.com -c user.name=t "$@"; }

# case <name> <expected: pass|fail> <path to add> [modify]
run_case() {
  name=$1; want=$2; path=$3
  d="$W/$name"; mkdir -p "$d"; cd "$d"
  git init -q .; mkdir -p pkg; echo old > pkg/old_1.bats; echo s > pkg/old_1.bats.sha256
  git_ add -A; git_ commit -q -m base; base=$(git rev-parse HEAD)
  if [ "${4:-}" = modify ]; then echo changed >> "$path"; else mkdir -p "$(dirname "$path")"; echo new > "$path"; fi
  git_ add -A; git_ commit -q -m change
  if sh "$SCRIPT" "$base" > out.txt 2>&1; then got=pass; else got=fail; fi
  cat out.txt
  [ "$got" = "$want" ] || { echo "FAIL: $name: wanted $want, got $got"; exit 1; }
  echo "ok: $name ($got)"
}

run_case deep-source pass tools/pin-audit/src/bin/pin_audit.bats
run_case deep-source-four pass tools/pin-audit/src/audit.bats
run_case root-no-sidecar fail new_2.bats
run_case package-no-sidecar fail pkg/new_2.bats
run_case namespace-no-sidecar fail wasm.bats-packages.dev/bridge/new_2.bats
run_case modified-archive fail pkg/old_1.bats modify
