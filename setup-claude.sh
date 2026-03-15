#!/bin/bash
# Run once after cloning. Creates symlinks from ~/src/bats-lang/ into repository-prototype.
# Idempotent — safe to run again.
set -euo pipefail

DIR="$(cd "$(dirname "$0")/.." && pwd)"

mkdir -p "$DIR/.claude/hooks"

ln -sf "$DIR/repository-prototype/CLAUDE.md" "$DIR/CLAUDE.md"
ln -sf "$DIR/repository-prototype/claude-settings.json" "$DIR/.claude/settings.json"
ln -sf "$DIR/repository-prototype/enforce-claude-md.sh" "$DIR/.claude/hooks/enforce-claude-md.sh"
chmod +x "$DIR/repository-prototype/enforce-claude-md.sh"
