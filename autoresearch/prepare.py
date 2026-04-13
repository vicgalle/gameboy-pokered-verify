"""
prepare.py — Fixed evaluation harness for the autoresearch bug formalization pipeline.

DO NOT MODIFY. This file is read-only for the researcher agent.

Provides:
  - Lean project setup for evaluating formalizer output
  - Compilation testing with timeout
  - Scoring: compilation, theorem count, sorry-free, ground truth coverage
  - Leak detection against ground truth
  - Aggregate score computation Phi(c) across all bugs
"""

import os
import re
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
from difflib import SequenceMatcher

# ──────────────────────────────────────────────────────────────────────
# Constants
# ──────────────────────────────────────────────────────────────────────

BUGS = ["focus_energy", "one_in_256", "blaine_ai", "heal_overflow", "psywave_desync"]

BUG_TO_LEAN_NAME = {
    "focus_energy": "FocusEnergy",
    "one_in_256": "OneIn256",
    "blaine_ai": "BlaineAI",
    "heal_overflow": "HealOverflow",
    "psywave_desync": "PsywaveDesync",
}

AUTORESEARCH_DIR = Path(__file__).parent.resolve()
GROUND_TRUTH_DIR = AUTORESEARCH_DIR / "ground_truth"
POKERED_VERIFY_ROOT = AUTORESEARCH_DIR.parent.resolve()

LEAN_BUILD_TIMEOUT = 120  # seconds per build attempt
LEAN_TOOLCHAIN = "leanprover/lean4:v4.28.0"

# Ground truth theme keywords for coverage scoring.
# Each bug has a list of "themes" that a good formalization should cover.
# These are semantic categories, not exact theorem names.
GROUND_TRUTH_THEMES = {
    "focus_energy": [
        "bug_exists",          # existential witness
        "always_wrong",        # universal wrongness
        "reduces_rate",        # buggy <= correct
        "fix_correct",         # fix matches spec
    ],
    "one_in_256": [
        "bug_exists",          # existential witness
        "bug_characterization",# iff condition
        "every_threshold",     # universal across thresholds
        "fix_correct",         # fix matches spec
    ],
    "blaine_ai": [
        "heals_unconditionally", # always heals
        "wastes_at_full_hp",     # waste when healthy
        "fix_correct",           # fix heals only when needed
        "unique_unconditional",  # only trainer with this bug
    ],
    "heal_overflow": [
        "bug_exists",           # concrete false failure
        "no_bug_below_256",     # works for low maxHP
        "gap_enumeration",      # exact gaps: 255, 511, 767
        "fix_correct",          # correct check
    ],
    "psywave_desync": [
        "player_never_zero",    # player always deals >= 1
        "enemy_can_zero",       # enemy can deal 0
        "desync_exists",        # concrete desync example
        "desync_propagates",    # permanent divergence
    ],
}

# Keywords that indicate each theme is covered in generated code
THEME_KEYWORDS = {
    "bug_exists": ["exists", "∃", "witness", "bug_exists", "bug_exist"],
    "always_wrong": ["always", "∀", "forall", "unconditional", "all_"],
    "reduces_rate": ["reduces", "less", "≤", "<=", "worse", "quarter"],
    "fix_correct": ["fix", "correct", "fixed", "repair"],
    "bug_characterization": ["iff", "↔", "<->", "characteriz", "exactly"],
    "every_threshold": ["every", "all", "universal", "any_threshold"],
    "heals_unconditionally": ["unconditional", "always_heals", "always_uses"],
    "wastes_at_full_hp": ["waste", "full_hp", "zero_gain", "no_benefit"],
    "unique_unconditional": ["unique", "only_trainer", "only_one"],
    "no_bug_below_256": ["below_256", "low_hp", "no_false", "maxhp_le"],
    "gap_enumeration": ["255", "511", "767", "gap", "enumerat"],
    "player_never_zero": ["player_never", "never_zero", "always_positive", "geq_1"],
    "enemy_can_zero": ["enemy_can", "enemy_zero", "can_deal_zero"],
    "desync_exists": ["desync", "diverge", "out_of_sync"],
    "desync_propagates": ["propagat", "permanent", "cascade", "all_subsequent"],
}


# ──────────────────────────────────────────────────────────────────────
# Lean project setup for evaluation
# ──────────────────────────────────────────────────────────────────────

def create_eval_project(run_id: str) -> Path:
    """Create a temporary Lean project for evaluating formalizer output.

    The project depends on SM83 from the parent pokered-verify project
    but does NOT include any existing proofs or the BugClaim harness.
    """
    eval_dir = Path(tempfile.mkdtemp(prefix=f"pokered-eval-{run_id}-"))

    # lakefile.toml — depend on the parent project for SM83 only
    lakefile = f"""\
name = "pokered-verify-eval"
version = "0.1.0"
leanOptions = [
  {{ name = "autoImplicit", value = false }}
]

[[require]]
name = "SM83"
path = "{POKERED_VERIFY_ROOT}"

[[lean_lib]]
name = "Generated"
roots = ["Generated"]
"""
    (eval_dir / "lakefile.toml").write_text(lakefile)
    (eval_dir / "lean-toolchain").write_text(LEAN_TOOLCHAIN + "\n")
    (eval_dir / "Generated").mkdir()

    return eval_dir


# ──────────────────────────────────────────────────────────────────────
# Lean build & analysis
# ──────────────────────────────────────────────────────────────────────

def build_lean_file(eval_dir: Path, bug_name: str, lean_content: str) -> dict:
    """Write a Lean file into the eval project, build it, return results."""
    lean_name = BUG_TO_LEAN_NAME[bug_name]
    lean_path = eval_dir / "Generated" / f"{lean_name}.lean"
    lean_path.write_text(lean_content)

    try:
        result = subprocess.run(
            ["lake", "build", f"Generated.{lean_name}"],
            cwd=str(eval_dir),
            capture_output=True,
            text=True,
            timeout=LEAN_BUILD_TIMEOUT,
        )
        compiles = result.returncode == 0
        error_output = result.stderr + result.stdout
    except subprocess.TimeoutExpired:
        compiles = False
        error_output = f"BUILD TIMEOUT after {LEAN_BUILD_TIMEOUT}s"
    except Exception as e:
        compiles = False
        error_output = f"BUILD ERROR: {e}"

    return {
        "compiles": compiles,
        "error_output": error_output,
    }


def count_theorems(lean_content: str) -> list[str]:
    """Extract theorem names from Lean source."""
    pattern = r'^\s*theorem\s+(\w+)'
    return re.findall(pattern, lean_content, re.MULTILINE)


def count_sorry(lean_content: str) -> int:
    """Count sorry occurrences (incomplete proofs)."""
    # Match 'sorry' as a standalone tactic/term, not in comments or strings
    lines = lean_content.split('\n')
    count = 0
    for line in lines:
        stripped = line.split('--')[0]  # remove single-line comments
        count += len(re.findall(r'\bsorry\b', stripped))
    return count


def compute_theme_coverage(bug_name: str, lean_content: str) -> float:
    """Score how many ground truth themes are covered by the generated code.

    Returns a float in [0, 1] representing fraction of themes covered.
    """
    themes = GROUND_TRUTH_THEMES.get(bug_name, [])
    if not themes:
        return 0.0

    content_lower = lean_content.lower()
    theorem_names = [t.lower() for t in count_theorems(lean_content)]
    all_text = content_lower + " " + " ".join(theorem_names)

    covered = 0
    for theme in themes:
        keywords = THEME_KEYWORDS.get(theme, [])
        if any(kw.lower() in all_text for kw in keywords):
            covered += 1

    return covered / len(themes)


# ──────────────────────────────────────────────────────────────────────
# Leak detection
# ──────────────────────────────────────────────────────────────────────

def check_for_leaks(bug_name: str, lean_content: str) -> dict:
    """Check if generated code contains suspiciously long matches against ground truth.

    Returns a dict with leak_detected (bool) and longest_match (int).
    """
    gt_path = GROUND_TRUTH_DIR / f"{BUG_TO_LEAN_NAME[bug_name]}.lean"
    if not gt_path.exists():
        return {"leak_detected": False, "longest_match": 0}

    gt_content = gt_path.read_text()

    # Check for verbatim substring matches >= 100 chars (excluding imports/namespace)
    # Strip boilerplate that would legitimately match
    def strip_boilerplate(s):
        lines = s.split('\n')
        return '\n'.join(
            l for l in lines
            if not l.strip().startswith('import ')
            and not l.strip().startswith('namespace ')
            and not l.strip().startswith('end ')
            and not l.strip().startswith('open ')
            and l.strip()
        )

    gen_stripped = strip_boilerplate(lean_content)
    gt_stripped = strip_boilerplate(gt_content)

    matcher = SequenceMatcher(None, gen_stripped, gt_stripped)
    longest = 0
    for block in matcher.get_matching_blocks():
        if block.size > longest:
            longest = block.size

    return {
        "leak_detected": longest >= 100,
        "longest_match": longest,
    }


# ──────────────────────────────────────────────────────────────────────
# Scoring
# ──────────────────────────────────────────────────────────────────────

def score_bug(bug_name: str, lean_content: str, build_result: dict) -> dict:
    """Compute the score for a single bug formalization.

    Scoring breakdown (max 1.0 per bug):
      +0.2  if the Lean file compiles
      +0.1  per theorem proved (up to +0.3 for 3+ theorems)
      +0.3  if completely sorry-free
      +0.2  scaled by ground truth theme coverage
    """
    theorems = count_theorems(lean_content)
    num_sorry = count_sorry(lean_content)
    sorry_free = num_sorry == 0
    coverage = compute_theme_coverage(bug_name, lean_content)
    leak_info = check_for_leaks(bug_name, lean_content)

    score = 0.0

    # Tier 1: compilation
    if build_result["compiles"]:
        score += 0.2

    # Tier 2: theorem content
    theorem_score = min(len(theorems) * 0.1, 0.3)
    score += theorem_score

    # Tier 3: sorry-free (only counts if it compiles)
    if build_result["compiles"] and sorry_free and len(theorems) > 0:
        score += 0.3

    # Tier 4: coverage
    score += 0.2 * coverage

    # Penalty for detected leaks
    if leak_info["leak_detected"]:
        score = max(0.0, score - 0.5)

    return {
        "bug": bug_name,
        "score": round(score, 3),
        "compiles": build_result["compiles"],
        "num_theorems": len(theorems),
        "theorem_names": theorems,
        "num_sorry": num_sorry,
        "sorry_free": sorry_free,
        "coverage": round(coverage, 3),
        "leak_detected": leak_info["leak_detected"],
        "longest_match": leak_info["longest_match"],
        "error_output": build_result.get("error_output", "")[:500],
    }


def compute_aggregate_score(bug_scores: list[dict]) -> float:
    """Compute the aggregate score Phi(c) across all bugs.

    Returns a float in [0.0, 5.0].
    """
    return round(sum(s["score"] for s in bug_scores), 3)


# ──────────────────────────────────────────────────────────────────────
# Full evaluation pipeline
# ──────────────────────────────────────────────────────────────────────

def evaluate_all(run_id: str, generated_files: dict[str, str]) -> dict:
    """Evaluate all generated Lean files.

    Args:
        run_id: Unique identifier for this run
        generated_files: dict mapping bug_name -> Lean source code string

    Returns:
        dict with per-bug scores and aggregate score
    """
    eval_dir = create_eval_project(run_id)

    try:
        bug_scores = []
        for bug_name in BUGS:
            lean_content = generated_files.get(bug_name, "")
            if not lean_content.strip():
                bug_scores.append({
                    "bug": bug_name,
                    "score": 0.0,
                    "compiles": False,
                    "num_theorems": 0,
                    "theorem_names": [],
                    "num_sorry": 0,
                    "sorry_free": False,
                    "coverage": 0.0,
                    "leak_detected": False,
                    "longest_match": 0,
                    "error_output": "No output generated",
                })
                continue

            build_result = build_lean_file(eval_dir, bug_name, lean_content)
            bug_score = score_bug(bug_name, lean_content, build_result)
            bug_scores.append(bug_score)

        aggregate = compute_aggregate_score(bug_scores)

        return {
            "run_id": run_id,
            "score": aggregate,
            "bug_scores": bug_scores,
            "eval_dir": str(eval_dir),
        }
    finally:
        # Clean up eval project
        shutil.rmtree(eval_dir, ignore_errors=True)


# ──────────────────────────────────────────────────────────────────────
# CLI for standalone testing
# ──────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python prepare.py <workspace_dir>")
        print("  Evaluates .lean files in workspace_dir/*/final.lean")
        sys.exit(1)

    workspace = Path(sys.argv[1])
    generated = {}
    for bug in BUGS:
        final = workspace / bug / "final.lean"
        if final.exists():
            generated[bug] = final.read_text()
        else:
            print(f"WARNING: No final.lean found for {bug}")

    results = evaluate_all("manual-test", generated)
    print(json.dumps(results, indent=2))
