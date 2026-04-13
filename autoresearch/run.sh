#!/bin/bash
#
# run.sh — Run one autoresearch bug formalization experiment.
#
# Usage:
#   ./run.sh <bug_number> [experiment_id] [model]
#
# Arguments:
#   bug_number    : 1-5 (maps to bugs/0N_*.md)
#   experiment_id : optional tag (default: timestamp)
#   model         : optional model override (default: sonnet)
#
# Example:
#   ./run.sh 1                          # Focus Energy, default model
#   ./run.sh 3 trial_02 opus            # Blaine AI, opus model
#
# What it does:
#   1. Creates a fresh Lean workspace (SM83 + Harness, NO existing proofs)
#   2. Copies the bug description into the workspace
#   3. Launches Claude Code with program.md as the agent prompt
#   4. The agent iterates autonomously until compilation + proofs or timeout
#   5. Results are captured in results/<workspace_name>/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

BUG_NUM="${1:?Usage: ./run.sh <bug_number> [experiment_id] [model]}"
EXPERIMENT_ID="${2:-$(date +%Y%m%d_%H%M%S)}"
MODEL="${3:-sonnet}"

# Validate bug number
if [[ "$BUG_NUM" -lt 1 || "$BUG_NUM" -gt 5 ]]; then
    echo "Error: bug_number must be 1-5"
    exit 1
fi

# Find the bug description file
BUG_FILE=$(ls "$SCRIPT_DIR/bugs/"0"${BUG_NUM}"_*.md 2>/dev/null | head -1)
if [[ -z "$BUG_FILE" ]]; then
    echo "Error: No bug description found for bug $BUG_NUM"
    exit 1
fi

BUG_NAME=$(basename "$BUG_FILE" .md | sed 's/^[0-9]*_//')
WORKSPACE_NAME="bug${BUG_NUM}_${BUG_NAME}_${EXPERIMENT_ID}"
WORKSPACE_DIR="$SCRIPT_DIR/results/$WORKSPACE_NAME"

echo "=== Autoresearch Bug Formalization ==="
echo "Bug:        #${BUG_NUM} — $(head -1 "$BUG_FILE" | sed 's/^# //')"
echo "Workspace:  $WORKSPACE_DIR"
echo "Model:      $MODEL"
echo "Experiment: $EXPERIMENT_ID"
echo ""

# ---- Step 1: Create fresh workspace ----
echo "[1/4] Creating workspace..."
mkdir -p "$WORKSPACE_DIR"

# Copy SM83 infrastructure (the CPU formalization — this is tooling, not answers)
cp -r "$PROJECT_ROOT/SM83" "$WORKSPACE_DIR/SM83"
cp    "$PROJECT_ROOT/SM83.lean" "$WORKSPACE_DIR/SM83.lean"

# Copy Harness (the BugClaim type — defines the contract)
cp -r "$PROJECT_ROOT/Harness" "$WORKSPACE_DIR/Harness"
cp    "$PROJECT_ROOT/Harness.lean" "$WORKSPACE_DIR/Harness.lean"

# Copy Lean project template
cp "$SCRIPT_DIR/template/lakefile.toml" "$WORKSPACE_DIR/lakefile.toml"
cp "$SCRIPT_DIR/template/lean-toolchain" "$WORKSPACE_DIR/lean-toolchain"
cp "$SCRIPT_DIR/template/Solution.lean" "$WORKSPACE_DIR/Solution.lean"

# Copy bug description
cp "$BUG_FILE" "$WORKSPACE_DIR/bug_description.md"

# ---- Step 2: Verify workspace compiles ----
echo "[2/4] Verifying workspace compiles (lake build)..."
cd "$WORKSPACE_DIR"

# Initialize git for the workspace (agent commits progress)
git init -q
git add -A
git commit -q -m "Initial workspace for bug #${BUG_NUM}: ${BUG_NAME}"

# Quick compilation check (just the infrastructure, not Solution.lean yet)
if ! lake build SM83 2>&1 | tail -5; then
    echo "ERROR: SM83 infrastructure failed to compile in workspace!"
    echo "Check that lean-toolchain matches the parent project."
    exit 1
fi
echo "Infrastructure compiles OK."

# ---- Step 3: Build the agent prompt ----
echo "[3/4] Launching Claude Code agent..."

AGENT_PROMPT="$(cat "$SCRIPT_DIR/program.md")

---

## Your Task

$(cat "$WORKSPACE_DIR/bug_description.md")

---

## Workspace

You are working in: $WORKSPACE_DIR
The pokered disassembly is at: /Users/victorgallego/pokered

Write your formalization in \`Solution.lean\`. It should compile with \`lake build\`.
When done, create \`results.md\` summarizing what you proved.

Begin by reading bug_description.md, then search the pokered codebase for the
relevant assembly, then start writing your formalization."

# ---- Step 4: Launch Claude Code ----
# Record start time
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$WORKSPACE_DIR/.start_time"

claude -p "$AGENT_PROMPT" \
    --model "$MODEL" \
    --max-turns 50 \
    --allowedTools "Read,Write,Edit,Bash,Glob,Grep" \
    2>&1 | tee "$WORKSPACE_DIR/agent_log.txt"

# Record end time
echo "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$WORKSPACE_DIR/.end_time"

# ---- Post-run: Check compilation status ----
echo ""
echo "=== Post-run Compilation Check ==="
cd "$WORKSPACE_DIR"
if lake build 2>&1 | tee "$WORKSPACE_DIR/final_build.log"; then
    echo "RESULT: Solution compiles successfully!"
    echo "compiles" > "$WORKSPACE_DIR/.compile_status"
else
    echo "RESULT: Solution has compilation errors."
    echo "errors" > "$WORKSPACE_DIR/.compile_status"
fi

echo ""
echo "=== Experiment Complete ==="
echo "Workspace: $WORKSPACE_DIR"
echo "Solution:  $WORKSPACE_DIR/Solution.lean"
echo "Log:       $WORKSPACE_DIR/agent_log.txt"
echo "Build:     $WORKSPACE_DIR/final_build.log"
echo ""
echo "Run evaluate.py to analyze results:"
echo "  python3 $SCRIPT_DIR/evaluate.py $WORKSPACE_DIR"
