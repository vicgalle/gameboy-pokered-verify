#!/usr/bin/env bash
#
# run_experiment.sh -- Launch an autonomous autoresearch experiment.
#
# Usage:
#   ./autoresearch/run_experiment.sh <tag> [feedback_mode] [researcher_model] [policy_model]
#
# Examples:
#   ./autoresearch/run_experiment.sh apr15-test                              # Opus researcher, Sonnet formalizer
#   ./autoresearch/run_experiment.sh apr15-gemini dense opus gemini-2.5-pro  # Opus researcher, Gemini formalizer
#   ./autoresearch/run_experiment.sh apr15-fast sparse sonnet claude-sonnet-4-6  # Sonnet researcher+formalizer
#
# This script:
#   1. Creates a git branch ar/<tag> for the experiment
#   2. Launches Claude Code with the researcher program
#   3. The researcher agent runs autonomously until interrupted (Ctrl-C)
#

set -euo pipefail

TAG="${1:?Usage: $0 <tag> [sparse|dense] [researcher_model] [policy_model]}"
FEEDBACK="${2:-dense}"
RESEARCHER_MODEL="${3:-opus}"
POLICY_MODEL="${4:-claude-sonnet-4-6}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
cd "$REPO_ROOT"

BRANCH="ar/${TAG}"

echo "=== Autoresearch: Lean 4 Bug Formalization ==="
echo "Tag:              ${TAG}"
echo "Feedback:         ${FEEDBACK}"
echo "Researcher model: ${RESEARCHER_MODEL}"
echo "Policy model:     ${POLICY_MODEL}"
echo "Branch:           ${BRANCH}"
echo ""

# --- Setup branch ---
if git show-ref --verify --quiet "refs/heads/${BRANCH}" 2>/dev/null; then
    echo "Branch ${BRANCH} already exists. Checking it out..."
    git checkout "$BRANCH"
else
    echo "Creating branch ${BRANCH}..."
    git checkout -b "$BRANCH"
fi

echo "Working on: $(git branch --show-current)"
echo ""

# --- Verify infrastructure ---
echo "Verifying infrastructure..."
if [[ ! -f "autoresearch/run_inner.py" ]]; then
    echo "ERROR: autoresearch/run_inner.py not found."
    exit 1
fi
if [[ ! -d "autoresearch/pipeline" ]]; then
    echo "ERROR: autoresearch/pipeline/ directory not found."
    exit 1
fi
echo "OK."
echo ""

# --- Construct the prompt ---
PROMPT="Read autoresearch/researcher_program.md carefully. This is your research program.

Set up a new autoresearch run:
- Tag: ${TAG}
- Branch: ${BRANCH} (already created and checked out)
- Feedback mode: ${FEEDBACK}
- Policy LLM model: ${POLICY_MODEL}
- Measurement command: ./autoresearch/measure.sh ${FEEDBACK} --model ${POLICY_MODEL}

Important context:
- You are the RESEARCHER agent. You modify files in autoresearch/pipeline/ to improve how the FORMALIZER LLM produces Lean 4 proofs.
- The score Phi(c) ranges from 0.0 to 5.0 (higher = better).
- Each inner loop run takes ~10-30 minutes. Be patient.
- Read the existing bug descriptions, ground truth, and any previous results to understand the problem.
- Read the current pipeline/ files to understand the starting configuration.

The branch is ready. Establish the baseline by running:
  ./autoresearch/measure.sh ${FEEDBACK} --model ${POLICY_MODEL}
Then begin the experiment loop.

When running measure.sh, ALWAYS pass --model ${POLICY_MODEL} after the feedback mode.

Remember: NEVER STOP. Run experiments continuously until I interrupt you."

echo "Launching Claude Code researcher agent..."
echo "Press Ctrl-C to stop."
echo "---"

# --- Launch ---
claude --model "$RESEARCHER_MODEL" --dangerously-skip-permissions -p "$PROMPT"
