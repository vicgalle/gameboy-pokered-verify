#!/bin/bash
#
# run_all.sh — Run all 5 bug formalization experiments sequentially.
#
# Usage:
#   ./run_all.sh [--minimal] [experiment_id] [model]
#
# Arguments:
#   --minimal     : only pass the Gameplay Description (no root cause / file hints)
#   experiment_id : shared tag for this batch (default: timestamp)
#   model         : model to use (default: sonnet)
#
# Example:
#   ./run_all.sh batch_01 sonnet               # full descriptions
#   ./run_all.sh --minimal batch_02 sonnet      # gameplay-only descriptions
#   ./run_all.sh --minimal batch_03 opus        # gameplay-only, opus model
#
# After completion, run evaluate.py to produce the comparison table.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Parse --minimal flag
MINIMAL_FLAG=""
if [[ "${1:-}" == "--minimal" ]]; then
    MINIMAL_FLAG="--minimal"
    shift
fi

EXPERIMENT_ID="${1:-$(date +%Y%m%d_%H%M%S)}"
MODEL="${2:-sonnet}"
CONDITION="full"
[[ -n "$MINIMAL_FLAG" ]] && CONDITION="minimal"

echo "============================================"
echo "  Autoresearch: Full Bug Formalization Run"
echo "============================================"
echo "Experiment: $EXPERIMENT_ID"
echo "Model:      $MODEL"
echo "Condition:  $CONDITION"
echo "Bugs:       5 (Focus Energy, 1/256, Blaine AI, Heal Overflow, Psywave)"
echo ""

RESULTS_FILE="$SCRIPT_DIR/results/summary_${EXPERIMENT_ID}.tsv"
echo -e "bug_num\tbug_name\tcondition\tcompiles\ttheorems\tlevels\tstart\tend" > "$RESULTS_FILE"

for BUG_NUM in 1 2 3 4 5; do
    BUG_FILE=$(ls "$SCRIPT_DIR/bugs/"0"${BUG_NUM}"_*.md 2>/dev/null | head -1)
    BUG_NAME=$(basename "$BUG_FILE" .md | sed 's/^[0-9]*_//')

    echo ""
    echo "--------------------------------------------"
    echo "  Bug #${BUG_NUM}: ${BUG_NAME} [$CONDITION]"
    echo "--------------------------------------------"

    START_TIME=$(date -u +%Y-%m-%dT%H:%M:%SZ)

    # Run the experiment (run.sh handles everything)
    "$SCRIPT_DIR/run.sh" $MINIMAL_FLAG "$BUG_NUM" "$EXPERIMENT_ID" "$MODEL" || true

    END_TIME=$(date -u +%Y-%m-%dT%H:%M:%SZ)

    # Collect quick stats
    WORKSPACE_DIR="$SCRIPT_DIR/results/bug${BUG_NUM}_${BUG_NAME}_${EXPERIMENT_ID}"
    COMPILE_STATUS="unknown"
    THEOREM_COUNT=0
    LEVELS=""

    if [[ -f "$WORKSPACE_DIR/.compile_status" ]]; then
        COMPILE_STATUS=$(cat "$WORKSPACE_DIR/.compile_status")
    fi

    if [[ -f "$WORKSPACE_DIR/Solution.lean" ]]; then
        THEOREM_COUNT=$(grep -c "^theorem\|^  theorem" "$WORKSPACE_DIR/Solution.lean" 2>/dev/null || echo 0)
    fi

    echo -e "${BUG_NUM}\t${BUG_NAME}\t${CONDITION}\t${COMPILE_STATUS}\t${THEOREM_COUNT}\t${LEVELS}\t${START_TIME}\t${END_TIME}" >> "$RESULTS_FILE"
done

echo ""
echo "============================================"
echo "  All experiments complete!"
echo "============================================"
echo "Summary: $RESULTS_FILE"
echo ""
echo "Run full evaluation:"
echo "  python3 $SCRIPT_DIR/evaluate.py --batch $EXPERIMENT_ID"
