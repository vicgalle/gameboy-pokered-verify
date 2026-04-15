#!/usr/bin/env python3
"""
analyze.py -- Analyze autoresearch experiment results.

Reads results.tsv (maintained by the researcher agent) and produces
summary statistics, trend analysis, and comparisons.

Usage:
    python3 analyze.py                           # Default: read results.tsv
    python3 analyze.py results.tsv               # Specify file
    python3 analyze.py results1.tsv results2.tsv # Compare multiple runs
"""

import sys
from pathlib import Path


SCRIPT_DIR = Path(__file__).parent

BUG_NAMES = {
    1: "focus_energy",
    2: "one_in_256",
    3: "blaine_ai",
    4: "heal_overflow",
    5: "psywave_desync",
}


def parse_tsv(filepath: Path) -> list[dict]:
    """Parse a tab-separated results file."""
    if not filepath.exists():
        print(f"File not found: {filepath}")
        return []

    rows = []
    with open(filepath) as f:
        header_line = f.readline().strip()
        if not header_line:
            return []
        header = header_line.split("\t")
        for line in f:
            line = line.strip()
            if not line:
                continue
            values = line.split("\t")
            row = dict(zip(header, values))
            rows.append(row)
    return rows


def safe_float(val: str, default: float = 0.0) -> float:
    """Safely parse a float, returning default on failure."""
    try:
        return float(val)
    except (ValueError, TypeError):
        return default


def analyze(filepath: Path):
    """Analyze a single results file."""
    rows = parse_tsv(filepath)
    if not rows:
        print(f"No results to analyze in {filepath}.")
        return

    print(f"\n{'=' * 70}")
    print(f"  Autoresearch Analysis: {filepath.name}")
    print(f"{'=' * 70}")

    total = len(rows)
    kept = sum(1 for r in rows if r.get("status") == "keep")
    discarded = sum(1 for r in rows if r.get("status") == "discard")
    crashed = sum(1 for r in rows if r.get("status") == "crash")

    print(f"\n  Total experiments: {total}")
    print(f"  Kept:             {kept}")
    print(f"  Discarded:        {discarded}")
    print(f"  Crashed:          {crashed}")

    # Score analysis
    scores = [safe_float(r.get("score", "0")) for r in rows]
    if scores:
        print(f"\n  Score range:  {min(scores):.3f} -- {max(scores):.3f}")
        print(f"  Best score:   {max(scores):.3f}")
        if len(scores) > 1:
            baseline = scores[0]
            improvement = max(scores) - baseline
            print(f"  Baseline:     {baseline:.3f}")
            print(f"  Improvement:  {improvement:+.3f}")

    # Per-bug analysis
    print(f"\n  --- Per-Bug Best Scores ---")
    for bug_num in range(1, 6):
        col = f"bug{bug_num}"
        bug_scores = [safe_float(r.get(col, "0")) for r in rows]
        if bug_scores:
            best = max(bug_scores)
            print(f"  Bug {bug_num} ({BUG_NAMES[bug_num]:.<20s}): best={best:.3f}")

    # Experiment timeline
    print(f"\n  --- Experiment Timeline ---")
    print(f"  {'#':<5s} {'Score':>6s} {'Delta':>8s} {'Status':<9s} {'Time':>7s}  Description")
    print(f"  {'-' * 70}")
    for r in rows:
        exp = r.get("experiment", "?")
        score = r.get("score", "?")
        delta = r.get("delta", "?")
        status = r.get("status", "?")
        time_s = r.get("run_time_s", "?")
        desc = r.get("description", "")[:45]
        print(f"  {exp:<5s} {score:>6s} {delta:>8s} {status:<9s} {time_s:>6s}s  {desc}")

    # Kept experiments only
    kept_rows = [r for r in rows if r.get("status") == "keep"]
    if kept_rows:
        print(f"\n  --- Kept Experiments (improvements) ---")
        for r in kept_rows:
            exp = r.get("experiment", "?")
            score = r.get("score", "?")
            delta = r.get("delta", "?")
            commit = r.get("commit", "?")
            desc = r.get("description", "")[:55]
            print(f"  #{exp}: score={score} delta={delta} commit={commit} -- {desc}")


def main():
    if len(sys.argv) > 1:
        for filepath in sys.argv[1:]:
            analyze(Path(filepath))
    else:
        default = SCRIPT_DIR / "results.tsv"
        analyze(default)


if __name__ == "__main__":
    main()
