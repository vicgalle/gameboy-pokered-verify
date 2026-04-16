#!/usr/bin/env bash
#
# measure.sh -- Run the inner formalization loop and report metrics.
#
# Usage:
#   ./autoresearch/measure.sh [sparse|dense] [--model MODEL] [--output-dir DIR] [--no-asm]
#
# Modes:
#   sparse  (default) -- score + pass/fail only
#   dense              -- all metrics + per-bug breakdown + timing + pipeline state
#
# Options:
#   --no-asm  Exclude assembly context from the formalizer prompt (ablation mode)
#
# All extra arguments are passed through to run_inner.py.
#
# Exit codes:
#   0 -- inner loop succeeded
#   1 -- inner loop failed
#

set -euo pipefail

FEEDBACK_MODE="${1:-sparse}"
shift 2>/dev/null || true

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

# Collect remaining args for run_inner.py
EXTRA_ARGS=()
while [[ $# -gt 0 ]]; do
    EXTRA_ARGS+=("$1")
    shift
done

# Create timestamped output dir
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_DIR="runs/${TIMESTAMP}"
mkdir -p "$OUTPUT_DIR"

BASELINE_FILE=".baseline_score"

# --- Run inner loop ---
echo "=== Running inner formalization loop ==="
echo "Feedback mode: $FEEDBACK_MODE"
echo "Extra args: ${EXTRA_ARGS[*]:-}"
echo "Output dir: $OUTPUT_DIR"
echo ""

RUN_START=$(date +%s)

RUN_OUTPUT=$(uv run python3 run_inner.py --output-dir "$OUTPUT_DIR" "${EXTRA_ARGS[@]}" 2>&1) || {
    RUN_END=$(date +%s)
    RUN_TIME=$((RUN_END - RUN_START))
    echo ""
    echo "--- RESULT ---"
    echo "status:     FAIL"
    echo "run_time:   ${RUN_TIME}s"
    echo ""
    if [[ "$FEEDBACK_MODE" == "dense" ]]; then
        echo "--- ERRORS ---"
        echo "$RUN_OUTPUT" | tail -50
    else
        echo "Inner loop failed. Run with 'dense' for error details."
    fi
    exit 1
}

RUN_END=$(date +%s)
RUN_TIME=$((RUN_END - RUN_START))

# --- Parse metrics ---
METRICS_JSON=$(echo "$RUN_OUTPUT" | sed -n '/=== INNER LOOP COMPLETE ===/,$ p' | tail -n +2)

if [[ -z "$METRICS_JSON" ]]; then
    echo "ERROR: Could not find metrics in output."
    echo "$RUN_OUTPUT" | tail -20
    exit 1
fi

# Parse with python
SCORE=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['score'])")
WALL_TIME=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['wall_time_s'])")

# Per-bug scores
BUG1=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['1']['score'])")
BUG2=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['2']['score'])")
BUG3=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['3']['score'])")
BUG4=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['4']['score'])")
BUG5=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['5']['score'])")
BUG6=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['6']['score'])")
BUG7=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['7']['score'])")
BUG8=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['8']['score'])")
BUG9=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['9']['score'])")
BUG10=$(echo "$METRICS_JSON" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['per_bug']['10']['score'])")

# Compute delta from baseline
DELTA="n/a"
if [[ -f "$BASELINE_FILE" ]]; then
    BASELINE=$(cat "$BASELINE_FILE")
    DELTA=$(python3 -c "b=$BASELINE; s=$SCORE; d=s-b; print(f'+{d:.3f}' if d>=0 else f'{d:.3f}')")
else
    echo "$SCORE" > "$BASELINE_FILE"
    DELTA="+0.000"
fi

# --- Report ---
echo ""
echo "--- RESULT ---"
echo "status:     OK"
echo "score:      ${SCORE}"
echo "delta:      ${DELTA}"
echo "run_time:   ${RUN_TIME}s"
echo "output_dir: ${OUTPUT_DIR}"

if [[ "$FEEDBACK_MODE" == "dense" ]]; then
    echo ""
    echo "--- PER-BUG SCORES ---"
    echo "  bug1  (focus_energy):    ${BUG1}"
    echo "  bug2  (one_in_256):      ${BUG2}"
    echo "  bug3  (blaine_ai):       ${BUG3}"
    echo "  bug4  (heal_overflow):   ${BUG4}"
    echo "  bug5  (psywave_desync):  ${BUG5}"
    echo "  bug6  (substitute):      ${BUG6}"
    echo "  bug7  (bide_desync):     ${BUG7}"
    echo "  bug8  (reflect_overflow):${BUG8}"
    echo "  bug9  (acc_eva_cancel):  ${BUG9}"
    echo "  bug10 (badge_reflect):   ${BUG10}"
    echo ""
    echo "--- FULL METRICS ---"
    echo "$METRICS_JSON" | python3 -c "
import json, sys
d = json.load(sys.stdin)
print(f\"  score:      {d['score']}\")
print(f\"  model:      {d['model']}\")
print(f\"  K:          {d['iterations_per_bug']}\")
print(f\"  wall_time:  {d['wall_time_s']}s\")
print()
for k in sorted(d['per_bug']):
    v = d['per_bug'][k]
    print(f\"  bug{k} ({v['bug_name']:.<20s}) score={v['score']:.3f}  compiles={v['compiles']}  theorems={v['theorems']}  sorry_free={v['sorry_free']}  iters={v['iterations_used']}\")
"
    echo ""
    echo "--- PIPELINE STATE ---"
    echo "Files in pipeline/:"
    for f in pipeline/*.py pipeline/*.yaml pipeline/*.md; do
        if [[ -f "$f" ]]; then
            echo "  $f ($(wc -l < "$f" | tr -d ' ') lines)"
        fi
    done
fi

# Save metrics for later analysis
echo "$METRICS_JSON" > "last_run_metrics.json"
