#!/bin/bash
# Stop hook: enforce CLAUDE.md principles against recent changes.
#
# How it works:
# 1. If stop_hook_active is true, we already ran — let the model stop.
# 2. Collect git diff (uncommitted, or last commit if clean).
# 3. If there's a diff, block the stop and tell the model to check
#    every CLAUDE.md rule against the diff.
# 4. If no diff, allow the stop.

set -euo pipefail

INPUT=$(cat)

# Prevent infinite loops
ACTIVE=$(echo "$INPUT" | jq -r '.stop_hook_active')
if [ "$ACTIVE" = "true" ]; then
  exit 0
fi

CWD=$(echo "$INPUT" | jq -r '.cwd')

# Collect changes
DIFF=$(cd "$CWD" && git diff HEAD 2>/dev/null || true)
if [ -z "$DIFF" ]; then
  DIFF=$(cd "$CWD" && git diff HEAD~1..HEAD 2>/dev/null || true)
fi

# No changes — nothing to enforce
if [ -z "$DIFF" ]; then
  exit 0
fi

# Write diff to a temp file the model can read
DIFF_FILE="/tmp/claude-enforce-diff-$$.txt"
echo "$DIFF" > "$DIFF_FILE"

# Block the stop and tell the model to enforce
jq -n --arg reason "ENFORCEMENT CHECK: Before you stop, verify your work complies with CLAUDE.md.

1. Read CLAUDE.md (find it in or above the working directory).
2. Read $DIFF_FILE (the git diff of your changes).
3. Check EVERY rule in CLAUDE.md against the diff. Be thorough.
4. If any rule is violated, list the violations and fix them.
5. Read success.txt (in the working directory). The success criteria MUST be achieved before you can stop. If not achieved, list what remains and KEEP WORKING — do not stop.
6. You may ONLY stop when BOTH: all CLAUDE.md rules are satisfied AND success.txt criteria are fully achieved." \
  '{"decision": "block", "reason": $reason}'
