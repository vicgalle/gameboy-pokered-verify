#!/usr/bin/env python3
"""
evaluate.py — Evaluate autoresearch bug formalization experiments.

Analyzes Solution.lean files produced by the autonomous agent and compares
them against our ground truth (manually crafted formalizations).

Usage:
    python3 evaluate.py <workspace_dir>          # Evaluate one experiment
    python3 evaluate.py --batch <experiment_id>   # Evaluate all 5 bugs in a batch
    python3 evaluate.py --compare <exp1> <exp2>   # Compare two batches

Metrics computed:
    - Compilation: does the file compile?
    - Definitions: count of `def` declarations
    - Theorems: count of `theorem`/`lemma` declarations
    - Levels: heuristic detection of L1/L2/L3/L4 achievement
    - Lines of code: total, definitions, proofs
    - Tactics: which proof tactics are used
    - Model fidelity: (manual review needed — flagged for human)
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional


SCRIPT_DIR = Path(__file__).parent
GROUND_TRUTH_FILE = SCRIPT_DIR / "ground_truth.json"

BUG_NAMES = {
    1: "focus_energy",
    2: "one_in_256",
    3: "blaine_ai",
    4: "heal_overflow",
    5: "psywave_desync",
    6: "substitute",
    7: "bide_desync",
    8: "reflect_overflow",
    9: "acc_eva_cancel",
    10: "badge_reflect",
}


@dataclass
class ProofMetrics:
    """Metrics extracted from a Solution.lean file."""
    bug_num: int
    bug_name: str
    compiles: bool = False
    total_lines: int = 0
    blank_lines: int = 0
    comment_lines: int = 0
    def_count: int = 0
    theorem_count: int = 0
    lemma_count: int = 0
    eval_count: int = 0
    def_names: list = field(default_factory=list)
    theorem_names: list = field(default_factory=list)
    levels_detected: list = field(default_factory=list)
    tactics_used: dict = field(default_factory=dict)
    has_docstring: bool = False
    has_namespace: bool = False
    imports_sm83: bool = False
    imports_harness: bool = False
    condition: str = "full"  # "full" or "minimal"
    compile_errors: str = ""
    iterations: int = 0  # git commit count


# ---- Parsing ----

def parse_lean_file(filepath: Path) -> ProofMetrics:
    """Parse a Solution.lean file and extract metrics."""
    metrics = ProofMetrics(bug_num=0, bug_name="")

    if not filepath.exists():
        return metrics

    content = filepath.read_text()
    lines = content.split("\n")
    metrics.total_lines = len(lines)

    # Tactics to track
    tactic_patterns = {
        "native_decide": r"\bnative_decide\b",
        "decide": r"\bdecide\b",
        "rfl": r"\brfl\b",
        "omega": r"\bomega\b",
        "simp": r"\bsimp\b",
        "simp_all": r"\bsimp_all\b",
        "norm_num": r"\bnorm_num\b",
        "constructor": r"\bconstructor\b",
        "intro": r"\bintro\b",
        "exact": r"\bexact\b",
        "have": r"\bhave\b",
        "cases": r"\bcases\b",
        "induction": r"\binduction\b",
        "unfold": r"\bunfold\b",
        "split": r"\bsplit\b",
    }
    tactic_counts = {t: 0 for t in tactic_patterns}

    in_docstring = False

    for line in lines:
        stripped = line.strip()

        # Blank lines
        if not stripped:
            metrics.blank_lines += 1
            continue

        # Docstrings
        if stripped.startswith("/-"):
            in_docstring = True
            metrics.has_docstring = True
        if in_docstring:
            metrics.comment_lines += 1
            if "-/" in stripped:
                in_docstring = False
            continue

        # Single-line comments
        if stripped.startswith("--") or stripped.startswith("/-!"):
            metrics.comment_lines += 1
            continue

        # Imports
        if stripped.startswith("import SM83"):
            metrics.imports_sm83 = True
        if stripped.startswith("import Harness"):
            metrics.imports_harness = True

        # Namespace
        if stripped.startswith("namespace"):
            metrics.has_namespace = True

        # Definitions
        def_match = re.match(r"(?:private\s+)?def\s+(\w+)", stripped)
        if def_match:
            metrics.def_count += 1
            metrics.def_names.append(def_match.group(1))

        # Structures
        if re.match(r"structure\s+\w+", stripped):
            metrics.def_count += 1

        # Theorems
        thm_match = re.match(r"(?:private\s+)?theorem\s+(\w+)", stripped)
        if thm_match:
            metrics.theorem_count += 1
            metrics.theorem_names.append(thm_match.group(1))

        # Lemmas
        lem_match = re.match(r"(?:private\s+)?lemma\s+(\w+)", stripped)
        if lem_match:
            metrics.lemma_count += 1
            metrics.theorem_names.append(lem_match.group(1))

        # #eval
        if stripped.startswith("#eval"):
            metrics.eval_count += 1

        # Tactics
        for tactic, pattern in tactic_patterns.items():
            if re.search(pattern, stripped):
                tactic_counts[tactic] += 1

    metrics.tactics_used = {t: c for t, c in tactic_counts.items() if c > 0}
    return metrics


def detect_levels(metrics: ProofMetrics, content: str) -> list:
    """Heuristically detect which difficulty levels are achieved."""
    levels = []

    # L1: Existential witness — look for ∃ in theorem bodies (may span multiple lines)
    # Match theorem blocks that contain ∃ or Exists anywhere in the statement
    if re.search(r"theorem\s+\w+[\s\S]*?∃", content) or "Exists" in content:
        levels.append("L1")

    # Also L1 if theorem names suggest existence proofs
    if any(kw in name.lower() for name in metrics.theorem_names
           for kw in ["exist", "_bug", "witness", "can_deal", "can_fail"]):
        if "L1" not in levels:
            levels.append("L1")

    # L2: Universal characterization — ∀ with ↔ or broad properties
    has_universal = re.search(r"theorem\s+\w+[^:]*\(.*:.*\).*:", content)
    has_iff = "↔" in content
    has_characterization = any(
        kw in name.lower()
        for name in metrics.theorem_names
        for kw in ["always", "never", "iff", "characteriz", "every", "all_", "forall"]
    )
    if has_universal and (has_iff or has_characterization):
        levels.append("L2")

    # Also L2 if there are multiple universal theorems
    universal_count = len(re.findall(r"theorem\s+\w+[^:]*\(.*:.*\)[^:]*:", content))
    if universal_count >= 2 and "L2" not in levels:
        levels.append("L2")

    # L3: Fix correctness — look for fix-related definitions and theorems
    has_fix_def = any("fix" in name.lower() or "correct" in name.lower()
                      for name in metrics.def_names)
    has_fix_thm = any("fix" in name.lower() or "correct" in name.lower()
                      for name in metrics.theorem_names)
    if has_fix_def and has_fix_thm:
        levels.append("L3")

    # L4: Relational — two systems, desync, link
    has_relational = any(
        kw in name.lower()
        for name in metrics.theorem_names + metrics.def_names
        for kw in ["desync", "link", "player", "enemy", "host", "guest", "diverge"]
    )
    if has_relational and metrics.theorem_count >= 3:
        levels.append("L4")

    return levels


def check_compilation(workspace_dir: Path) -> tuple:
    """Run `lake build` in the workspace and return (success, error_output)."""
    # Check cached result first
    status_file = workspace_dir / ".compile_status"
    if status_file.exists():
        status = status_file.read_text().strip()
        build_log = workspace_dir / "final_build.log"
        errors = build_log.read_text() if build_log.exists() else ""
        return (status == "compiles", errors)

    # Run lake build
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=workspace_dir,
            capture_output=True,
            text=True,
            timeout=300,
        )
        success = result.returncode == 0
        errors = result.stderr if not success else ""
        return (success, errors)
    except subprocess.TimeoutExpired:
        return (False, "TIMEOUT: lake build exceeded 5 minutes")
    except FileNotFoundError:
        return (False, "ERROR: lake not found in PATH")


def count_iterations(workspace_dir: Path) -> int:
    """Count git commits in the workspace (proxy for iterations)."""
    try:
        result = subprocess.run(
            ["git", "log", "--oneline"],
            cwd=workspace_dir,
            capture_output=True,
            text=True,
        )
        return len(result.stdout.strip().split("\n")) if result.stdout.strip() else 0
    except Exception:
        return 0


# ---- Evaluation ----

def evaluate_workspace(workspace_dir: Path) -> ProofMetrics:
    """Full evaluation of a single workspace."""
    solution_file = workspace_dir / "Solution.lean"

    # Determine bug number from directory name
    dirname = workspace_dir.name
    bug_num = 0
    bug_name = ""
    for num, name in BUG_NAMES.items():
        if f"bug{num}" in dirname:
            bug_num = num
            bug_name = name
            break

    metrics = parse_lean_file(solution_file)
    metrics.bug_num = bug_num
    metrics.bug_name = bug_name

    # Check compilation
    metrics.compiles, metrics.compile_errors = check_compilation(workspace_dir)

    # Detect levels
    if solution_file.exists():
        content = solution_file.read_text()
        metrics.levels_detected = detect_levels(metrics, content)

    # Count iterations
    metrics.iterations = count_iterations(workspace_dir)

    # Read experimental condition
    condition_file = workspace_dir / ".condition"
    if condition_file.exists():
        metrics.condition = condition_file.read_text().strip()

    return metrics


def load_ground_truth() -> dict:
    """Load ground truth from JSON file."""
    if not GROUND_TRUTH_FILE.exists():
        print(f"Warning: Ground truth file not found: {GROUND_TRUTH_FILE}")
        return {}
    with open(GROUND_TRUTH_FILE) as f:
        return json.load(f)


# ---- Output ----

def print_single_report(metrics: ProofMetrics, ground_truth: Optional[dict] = None):
    """Print detailed report for one experiment."""
    print(f"\n{'='*60}")
    print(f"  Bug #{metrics.bug_num}: {metrics.bug_name}")
    print(f"{'='*60}")

    print(f"\n  Condition:    {metrics.condition}")
    print(f"  Compilation:  {'PASS' if metrics.compiles else 'FAIL'}")
    print(f"  Total lines:  {metrics.total_lines}")
    print(f"  Definitions:  {metrics.def_count}")
    print(f"  Theorems:     {metrics.theorem_count + metrics.lemma_count}")
    print(f"  #eval tests:  {metrics.eval_count}")
    print(f"  Levels:       {', '.join(metrics.levels_detected) or 'none detected'}")
    print(f"  Iterations:   {metrics.iterations} git commits")

    if metrics.def_names:
        print(f"\n  Definitions:")
        for name in metrics.def_names:
            print(f"    - {name}")

    if metrics.theorem_names:
        print(f"\n  Theorems:")
        for name in metrics.theorem_names:
            print(f"    - {name}")

    if metrics.tactics_used:
        print(f"\n  Tactics used:")
        for tactic, count in sorted(metrics.tactics_used.items(), key=lambda x: -x[1]):
            print(f"    {tactic:20s} {count:3d} occurrences")

    if not metrics.compiles and metrics.compile_errors:
        print(f"\n  Compilation errors (last 10 lines):")
        for line in metrics.compile_errors.strip().split("\n")[-10:]:
            print(f"    {line}")

    # Compare with ground truth
    if ground_truth and str(metrics.bug_num) in ground_truth:
        gt = ground_truth[str(metrics.bug_num)]
        print(f"\n  --- Comparison with Ground Truth ---")
        print(f"  {'Metric':<25s} {'Agent':>10s} {'Manual':>10s}")
        print(f"  {'-'*45}")
        print(f"  {'Compiles':<25s} {'yes' if metrics.compiles else 'no':>10s} {'yes':>10s}")
        print(f"  {'Theorems':<25s} {metrics.theorem_count + metrics.lemma_count:>10d} {gt['theorem_count']:>10d}")
        print(f"  {'Definitions':<25s} {metrics.def_count:>10d} {gt['def_count']:>10d}")
        print(f"  {'Levels':<25s} {','.join(metrics.levels_detected):>10s} {','.join(gt['levels']):>10s}")
        print(f"  {'Lines of code':<25s} {metrics.total_lines:>10d} {gt['total_lines']:>10d}")

        # Level coverage score
        gt_levels = set(gt["levels"])
        agent_levels = set(metrics.levels_detected)
        coverage = len(agent_levels & gt_levels) / max(len(gt_levels), 1)
        print(f"  {'Level coverage':<25s} {coverage*100:>9.0f}%")


def print_batch_summary(all_metrics: list, ground_truth: dict):
    """Print summary table for a batch of experiments."""
    print(f"\n{'='*80}")
    print(f"  Autoresearch Batch Summary")
    print(f"{'='*80}")
    print()

    # Header
    header = f"  {'#':<3s} {'Bug':<20s} {'Cond':<8s} {'Comp':>5s} {'Thm':>5s} {'Def':>5s} {'Levels':<12s} {'GT Levels':<12s} {'Cov':>5s}"
    print(header)
    print(f"  {'-'*78}")

    total_compiles = 0
    total_level_coverage = 0

    for m in all_metrics:
        gt = ground_truth.get(str(m.bug_num), {})
        gt_levels = gt.get("levels", [])
        coverage = len(set(m.levels_detected) & set(gt_levels)) / max(len(gt_levels), 1)

        comp = "yes" if m.compiles else "NO"
        levels_str = ",".join(m.levels_detected) or "-"
        gt_levels_str = ",".join(gt_levels) or "-"

        print(f"  {m.bug_num:<3d} {m.bug_name:<20s} {m.condition:<8s} {comp:>5s} "
              f"{m.theorem_count + m.lemma_count:>5d} {m.def_count:>5d} "
              f"{levels_str:<12s} {gt_levels_str:<12s} {coverage*100:>4.0f}%")

        if m.compiles:
            total_compiles += 1
        total_level_coverage += coverage

    n = len(all_metrics)
    print(f"  {'-'*70}")
    print(f"  {'TOTAL':<24s} {total_compiles:>5d}/{n:<1d} "
          f"{'':>5s} {'':>5s} {'':>12s} {'':>12s} "
          f"{total_level_coverage/max(n,1)*100:>4.0f}%")

    print(f"\n  Compilation rate: {total_compiles}/{n} ({total_compiles/max(n,1)*100:.0f}%)")
    print(f"  Mean level coverage: {total_level_coverage/max(n,1)*100:.0f}%")


def export_results(all_metrics: list, output_file: Path):
    """Export metrics as JSON for further analysis."""
    data = [asdict(m) for m in all_metrics]
    with open(output_file, "w") as f:
        json.dump(data, f, indent=2)
    print(f"\n  Results exported to: {output_file}")


# ---- Main ----

def main():
    parser = argparse.ArgumentParser(description="Evaluate autoresearch experiments")
    parser.add_argument("workspace", nargs="?", help="Path to a single workspace directory")
    parser.add_argument("--batch", help="Evaluate all bugs in a batch by experiment ID")
    parser.add_argument("--compare", nargs=2, metavar=("EXP1", "EXP2"),
                        help="Compare two experiment batches")
    parser.add_argument("--export", help="Export results to JSON file")
    args = parser.parse_args()

    ground_truth = load_ground_truth()

    if args.workspace:
        # Single workspace evaluation
        workspace = Path(args.workspace)
        if not workspace.exists():
            print(f"Error: workspace not found: {workspace}")
            sys.exit(1)
        metrics = evaluate_workspace(workspace)
        print_single_report(metrics, ground_truth)

    elif args.batch:
        # Batch evaluation
        results_dir = SCRIPT_DIR / "results"
        all_metrics = []
        for bug_num in range(1, 6):
            bug_name = BUG_NAMES[bug_num]
            workspace_name = f"bug{bug_num}_{bug_name}_{args.batch}"
            workspace = results_dir / workspace_name
            if workspace.exists():
                metrics = evaluate_workspace(workspace)
                all_metrics.append(metrics)
                print_single_report(metrics, ground_truth)
            else:
                print(f"\n  Warning: workspace not found for bug #{bug_num}: {workspace}")

        if all_metrics:
            print_batch_summary(all_metrics, ground_truth)

        if args.export:
            export_results(all_metrics, Path(args.export))

    elif args.compare:
        # Compare two batches
        exp1, exp2 = args.compare
        results_dir = SCRIPT_DIR / "results"

        print(f"\n{'='*90}")
        print(f"  Comparison: {exp1} vs {exp2}")
        print(f"{'='*90}")
        print()
        print(f"  {'#':<3s} {'Bug':<20s} {'Cond1':<8s} {'Cond2':<8s} "
              f"{'Comp1':>6s} {'Comp2':>6s} "
              f"{'Thm1':>5s} {'Thm2':>5s} {'Lvl1':<10s} {'Lvl2':<10s}")
        print(f"  {'-'*80}")

        for bug_num in range(1, 6):
            bug_name = BUG_NAMES[bug_num]
            ws1 = results_dir / f"bug{bug_num}_{bug_name}_{exp1}"
            ws2 = results_dir / f"bug{bug_num}_{bug_name}_{exp2}"

            m1 = evaluate_workspace(ws1) if ws1.exists() else ProofMetrics(bug_num, bug_name)
            m2 = evaluate_workspace(ws2) if ws2.exists() else ProofMetrics(bug_num, bug_name)

            c1 = "yes" if m1.compiles else "no"
            c2 = "yes" if m2.compiles else "no"
            l1 = ",".join(m1.levels_detected) or "-"
            l2 = ",".join(m2.levels_detected) or "-"

            print(f"  {bug_num:<3d} {bug_name:<20s} {m1.condition:<8s} {m2.condition:<8s} "
                  f"{c1:>6s} {c2:>6s} "
                  f"{m1.theorem_count:>5d} {m2.theorem_count:>5d} "
                  f"{l1:<10s} {l2:<10s}")

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
