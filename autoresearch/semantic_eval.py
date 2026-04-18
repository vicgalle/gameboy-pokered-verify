#!/usr/bin/env python3
"""
Semantic fidelity evaluation via differential #eval.

For each bug, defines matched semantic tests with condition-specific
Lean expressions but identical expected values. This ensures the
with-ASM vs no-ASM comparison is apples-to-apples.

Usage:
    uv run python3 autoresearch/semantic_eval.py --run-dir DIR --test-suite noasm|asm
"""

import argparse
import json
import re
import subprocess
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent

# --------------------------------------------------------------------------
# Matched semantic tests.
#
# Each test: (description, noasm_expr, asm_expr, expected)
# Same semantic question, same expected answer, different Lean expressions
# to account for signature differences between conditions.
#
# 3 tests per bug × 10 bugs = 30 tests total (matched across conditions).
# --------------------------------------------------------------------------

MATCHED_TESTS: dict[int, list[tuple[str, str, str, str]]] = {
    1: [  # focus_energy: impl reduces rate, spec increases it
        ("impl and spec diverge",
         "#eval (AutoResearch.impl (0x40 : BitVec 8) ≠ AutoResearch.spec (0x40 : BitVec 8))",
         "#eval (AutoResearch.impl (0x40 : BitVec 8) true ≠ AutoResearch.spec (0x40 : BitVec 8) true)",
         "true"),
        ("impl gives lower rate than spec (bug reduces instead of increasing)",
         "#eval ((AutoResearch.impl (0x40 : BitVec 8)).toNat < (AutoResearch.spec (0x40 : BitVec 8)).toNat)",
         "#eval ((AutoResearch.impl (0x40 : BitVec 8) true).toNat < (AutoResearch.spec (0x40 : BitVec 8) true).toNat)",
         "true"),
        ("spec gives a non-zero rate for non-trivial input",
         "#eval ((AutoResearch.spec (0x40 : BitVec 8)).toNat > 0)",
         "#eval ((AutoResearch.spec (0x40 : BitVec 8) true).toNat > 0)",
         "true"),
    ],
    2: [  # one_in_256: impl misses at 255/255, spec doesn't
        ("impl misses at max accuracy + max roll (the 1/256 bug)",
         "#eval AutoResearch.impl (255 : BitVec 8) (255 : BitVec 8)",
         "#eval AutoResearch.impl (255 : BitVec 8) (255 : BitVec 8)",
         "false"),
        ("spec hits at max accuracy + max roll (guaranteed hit)",
         "#eval AutoResearch.spec (255 : BitVec 8) (255 : BitVec 8)",
         "#eval AutoResearch.spec (255 : BitVec 8) (255 : BitVec 8)",
         "true"),
        ("impl and spec agree on normal hit (acc=255, rand=100)",
         "#eval (AutoResearch.impl (255 : BitVec 8) (100 : BitVec 8) = AutoResearch.spec (255 : BitVec 8) (100 : BitVec 8))",
         "#eval (AutoResearch.impl (255 : BitVec 8) (100 : BitVec 8) = AutoResearch.spec (255 : BitVec 8) (100 : BitVec 8))",
         "true"),
    ],
    3: [  # blaine_ai: impl uses potion at full HP, spec doesn't
        ("impl uses potion at full HP (the bug: no HP check)",
         "#eval AutoResearch.impl (50 : BitVec 8) (50 : BitVec 8) true",
         "#eval AutoResearch.impl (10 : BitVec 8) (200 : BitVec 16) (200 : BitVec 16)",
         "true"),
        ("spec does NOT use potion at full HP",
         "#eval AutoResearch.spec (50 : BitVec 8) (50 : BitVec 8) true",
         "#eval AutoResearch.spec (10 : BitVec 8) (200 : BitVec 16) (200 : BitVec 16)",
         "false"),
        ("spec uses potion when HP is low",
         "#eval AutoResearch.spec (30 : BitVec 8) (50 : BitVec 8) true",
         "#eval AutoResearch.spec (10 : BitVec 8) (50 : BitVec 16) (200 : BitVec 16)",
         "true"),
    ],
    4: [  # heal_overflow: impl blocks heal incorrectly at certain HP gaps
        # No-ASM witness: (512, 256) — difference is 256, a multiple of 256
        # With-ASM witness: (curHP=1, maxHP=256) — from the solution's bug_exists theorem
        ("bug exists: impl and spec disagree at overflow boundary",
         "#eval (AutoResearch.impl 512 256 ≠ AutoResearch.spec 512 256)",
         "#eval (AutoResearch.impl (BitVec.ofNat 16 1) (BitVec.ofNat 16 256) ≠ AutoResearch.spec (BitVec.ofNat 16 1) (BitVec.ofNat 16 256))",
         "true"),
        ("impl and spec agree when HP is full (no bug)",
         "#eval (AutoResearch.impl 100 100 = AutoResearch.spec 100 100)",
         "#eval (AutoResearch.impl (BitVec.ofNat 16 200) (BitVec.ofNat 16 200) = AutoResearch.spec (BitVec.ofNat 16 200) (BitVec.ofNat 16 200))",
         "true"),
        ("impl and spec agree at small HP gap (no overflow)",
         "#eval (AutoResearch.impl 200 190 = AutoResearch.spec 200 190)",
         "#eval (AutoResearch.impl (BitVec.ofNat 16 190) (BitVec.ofNat 16 200) = AutoResearch.spec (BitVec.ofNat 16 190) (BitVec.ofNat 16 200))",
         "true"),
    ],
    5: [  # psywave_desync: player and enemy get different damage
        # No-ASM: impl returns (Nat × Nat) = (player_dmg, enemy_dmg)
        # With-ASM: impl returns LinkBattleResult with .player_gb / .enemy_gb fields
        # With-ASM witness from bug_exists: level=10, stream=[0, 5]
        ("impl produces desync (player ≠ enemy)",
         "#eval (let r := AutoResearch.impl 50 (100 : BitVec 8) (200 : BitVec 8); r.1 ≠ r.2)",
         "#eval (let r := AutoResearch.impl (10 : BitVec 8) [(0 : BitVec 8), (5 : BitVec 8)]; r.player_gb ≠ r.enemy_gb)",
         "true"),
        ("spec has no desync (player = enemy)",
         "#eval (let r := AutoResearch.spec 50 (100 : BitVec 8) (200 : BitVec 8); r.1 = r.2)",
         "#eval (let r := AutoResearch.spec (10 : BitVec 8) [(0 : BitVec 8), (5 : BitVec 8)]; r.player_gb = r.enemy_gb)",
         "true"),
        ("impl and spec diverge",
         "#eval (AutoResearch.impl 50 (100 : BitVec 8) (200 : BitVec 8) ≠ AutoResearch.spec 50 (100 : BitVec 8) (200 : BitVec 8))",
         "#eval (AutoResearch.impl (10 : BitVec 8) [(0 : BitVec 8), (5 : BitVec 8)] ≠ AutoResearch.spec (10 : BitVec 8) [(0 : BitVec 8), (5 : BitVec 8)])",
         "true"),
    ],
    6: [  # substitute: 0-HP substitute at low maxHP; user at 0 HP
        # No-ASM: impl returns (Nat × Nat × Bool) = (remaining_hp, sub_hp, success)
        # With-ASM: impl returns Option (BitVec 16 × BitVec 8) = some (newCurHP, subHP) or none
        # With-ASM witness from zero_hp_substitute_exists: maxHP=3, curHP=3
        ("low maxHP: impl allows 0-cost substitute (the bug)",
         "#eval (AutoResearch.impl 3 3).2.1 = 0",
         "#eval (AutoResearch.impl (BitVec.ofNat 16 3) (BitVec.ofNat 16 3)).isSome",
         "true"),
        ("spec blocks 0-cost substitute",
         "#eval (AutoResearch.spec 3 3).2.2 = false",
         "#eval (AutoResearch.spec (BitVec.ofNat 16 3) (BitVec.ofNat 16 3)).isNone",
         "true"),
        ("normal case: impl allows substitute (maxHP=100, HP=50)",
         "#eval (AutoResearch.impl 100 50).2.2 = true",
         "#eval (AutoResearch.impl (BitVec.ofNat 16 100) (BitVec.ofNat 16 50)).isSome",
         "true"),
    ],
    7: [  # bide_desync: impl clears only high byte, spec clears both
        # Same signatures in both conditions: BitVec 16 → BitVec 16
        ("impl keeps low byte (only high byte cleared)",
         "#eval AutoResearch.impl (0x0102 : BitVec 16)",
         "#eval AutoResearch.impl (0x0102 : BitVec 16)",
         "2"),
        ("spec clears everything to 0",
         "#eval AutoResearch.spec (0x0102 : BitVec 16)",
         "#eval AutoResearch.spec (0x0102 : BitVec 16)",
         "0"),
        ("impl and spec diverge (the desync)",
         "#eval (AutoResearch.impl (0x0180 : BitVec 16) ≠ AutoResearch.spec (0x0180 : BitVec 16))",
         "#eval (AutoResearch.impl (0x0180 : BitVec 16) ≠ AutoResearch.spec (0x0180 : BitVec 16))",
         "true"),
    ],
    8: [  # reflect_overflow: doubling overflows for high stats
        # Same signatures: BitVec 16 → BitVec 16
        ("small stat: impl doubles correctly (100 → 200)",
         "#eval AutoResearch.impl (100 : BitVec 16)",
         "#eval AutoResearch.impl (100 : BitVec 16)",
         "200"),
        ("impl and spec diverge at high stat (overflow region)",
         "#eval (AutoResearch.impl (512 : BitVec 16) ≠ AutoResearch.spec (512 : BitVec 16))",
         "#eval (AutoResearch.impl (512 : BitVec 16) ≠ AutoResearch.spec (512 : BitVec 16))",
         "true"),
        ("spec gives reasonable value at high stat",
         "#eval ((AutoResearch.spec (512 : BitVec 16)).toNat > 100)",
         "#eval ((AutoResearch.spec (512 : BitVec 16)).toNat > 100)",
         "true"),
    ],
    9: [  # acc_eva_cancel: equal boosts don't cancel perfectly
        # No-ASM uses Nat args, with-ASM uses BitVec 8 args
        ("equal +1/+1 boosts: impl loses accuracy (< 255)",
         "#eval ((AutoResearch.impl 255 1 1 : Nat) < 255)",
         "#eval ((AutoResearch.impl (255 : BitVec 8) (1 : BitVec 8) (1 : BitVec 8)).toNat < 255)",
         "true"),
        ("spec preserves accuracy at equal boosts (= 255)",
         "#eval (AutoResearch.spec 255 1 1 : Nat)",
         "#eval (AutoResearch.spec (255 : BitVec 8) (1 : BitVec 8) (1 : BitVec 8)).toNat",
         "255"),
        ("impl and spec diverge at equal boosts",
         "#eval ((AutoResearch.impl 255 1 1 : Nat) ≠ (AutoResearch.spec 255 1 1 : Nat))",
         "#eval (AutoResearch.impl (255 : BitVec 8) (1 : BitVec 8) (1 : BitVec 8) ≠ AutoResearch.spec (255 : BitVec 8) (1 : BitVec 8) (1 : BitVec 8))",
         "true"),
    ],
    10: [  # badge_reflect: badge stacking + reflect → overflow
        # No-ASM: impl(raw_stat, num_changes, has_reflect) -> Nat
        # With-ASM: impl(stat : BitVec 16) -> BitVec 8 (includes boost+reflect internally)
        ("impl overflows for Cloyster-like defense",
         "#eval ((AutoResearch.impl 458 1 true : Nat) < 50)",
         "#eval ((AutoResearch.impl (458 : BitVec 16)).toNat < 50)",
         "true"),
        ("spec does not overflow for same input",
         "#eval ((AutoResearch.spec 458 1 true : Nat) > 50)",
         "#eval ((AutoResearch.spec (458 : BitVec 16)).toNat > 50)",
         "true"),
        ("impl and spec diverge at high defense",
         "#eval ((AutoResearch.impl 458 1 true : Nat) ≠ (AutoResearch.spec 458 1 true : Nat))",
         "#eval (AutoResearch.impl (458 : BitVec 16) ≠ AutoResearch.spec (458 : BitVec 16))",
         "true"),
    ],
}

BUG_NAMES = {
    1: "focus_energy", 2: "one_in_256", 3: "blaine_ai",
    4: "heal_overflow", 5: "psywave_desync", 6: "substitute",
    7: "bide_desync", 8: "reflect_overflow", 9: "acc_eva_cancel",
    10: "badge_reflect",
}


def create_eval_file(solution_path: Path, tests: list[tuple[str, str]]) -> str:
    """Create a Lean file: solution code + #eval! statements.

    """
    solution_code = solution_path.read_text()
    lines = [solution_code, "", "-- === SEMANTIC EVAL TESTS ==="]
    for desc, expr in tests:
        lines.append(f"-- {desc}")
        lines.append(expr)
    return "\n".join(lines)


def score_bug(bug_num: int, solution_path: Path, workspace_dir: Path,
              timeout: int = 180, suite: str = "noasm") -> dict:
    """Score a single bug solution for semantic fidelity."""
    matched = MATCHED_TESTS.get(bug_num, [])
    # Select the right expression column: index 1 = noasm, index 2 = asm
    expr_idx = 1 if suite == "noasm" else 2
    tests = [(desc, exprs[expr_idx - 1], exprs[expr_idx], exprs[2])
             for desc, *exprs in matched]
    # tests is now [(desc, chosen_expr, expected), ...] — wait, let me fix
    # Actually: matched is (desc, noasm_expr, asm_expr, expected)
    tests_for_eval = [(t[0], t[expr_idx]) for t in matched]  # (desc, expr)
    expected_vals = [t[3] for t in matched]

    if not matched:
        return {"bug": bug_num, "tests": 0, "passed": 0, "score": None, "details": []}

    sol_file = workspace_dir / "Solution.lean"
    original_code = sol_file.read_text() if sol_file.exists() else ""

    try:
        eval_code = create_eval_file(solution_path, tests_for_eval)
        sol_file.write_text(eval_code)

        # Delete cached Solution artifacts to force recompilation
        for pattern in ["Solution.olean", "Solution.ilean", "Solution.trace"]:
            for f in workspace_dir.rglob(pattern):
                f.unlink(missing_ok=True)
        sol_ir = workspace_dir / ".lake" / "build" / "ir" / "Solution.c"
        sol_ir.unlink(missing_ok=True)

        try:
            result = subprocess.run(
                ["lake", "build", "Solution"],
                capture_output=True, text=True, timeout=timeout,
                cwd=workspace_dir,
            )
            output = result.stdout + "\n" + result.stderr
        except subprocess.TimeoutExpired:
            return {"bug": bug_num, "tests": len(matched), "passed": 0,
                    "score": 0.0, "details": ["TIMEOUT"], "error": "timeout"}

        # Parse #eval results: "info: Solution.lean:LINE:COL: VALUE"
        eval_results = []
        for line in output.split("\n"):
            line = line.strip()
            m = re.match(r"info:\s+Solution\.lean:\d+:\d+:\s+(.*)", line)
            if m:
                val = m.group(1).strip()
                bv_match = re.match(r"0x([0-9a-fA-F]+)#(\d+)", val)
                if bv_match:
                    val = str(int(bv_match.group(1), 16))
                eval_results.append(val)

        details = []
        passed = 0

        for i, (desc, expected) in enumerate(zip([t[0] for t in matched], expected_vals)):
            if i < len(eval_results):
                actual = eval_results[i]
                ok = actual.strip() == expected.strip()
                if ok:
                    passed += 1
                details.append({"test": desc, "expected": expected,
                                "actual": actual, "pass": ok})
            else:
                details.append({"test": desc, "expected": expected,
                                "actual": f"NO OUTPUT (got {len(eval_results)} results)",
                                "pass": False})

        score = passed / len(matched) if matched else 0.0
        return {"bug": bug_num, "tests": len(matched), "passed": passed,
                "score": round(score, 3), "details": details}
    finally:
        sol_file.write_text(original_code)


def main():
    parser = argparse.ArgumentParser(
        description="Semantic fidelity evaluation via differential #eval")
    parser.add_argument("--run-dir", type=str, default=None,
                        help="Run directory (contains workspace_bug* and solutions/)")
    parser.add_argument("--timeout", type=int, default=180,
                        help="Timeout per bug in seconds")
    parser.add_argument("--test-suite", choices=["noasm", "asm"], default="noasm",
                        help="Which expression variant to use (noasm or asm)")
    args = parser.parse_args()

    if args.run_dir:
        run_dir = Path(args.run_dir)
    else:
        runs_dir = SCRIPT_DIR / "runs"
        run_dir = sorted(runs_dir.iterdir())[-1]

    sol_dir = run_dir / "solutions"
    if not sol_dir.exists():
        print(f"ERROR: Solutions directory not found: {sol_dir}")
        return

    suite = args.test_suite
    print(f"Run dir:    {run_dir}")
    print(f"Solutions:  {sol_dir}")
    print(f"Suite:      {suite}")
    print(f"Timeout:    {args.timeout}s")
    print(f"Tests/bug:  3 (matched across conditions)")
    print()

    results = {}
    total_tests = 0
    total_passed = 0

    for bug_num in range(1, 11):
        bug_name = BUG_NAMES[bug_num]
        sol_file = sol_dir / f"bug{bug_num}_{bug_name}.lean"
        workspace = run_dir / f"workspace_bug{bug_num}"

        if not sol_file.exists():
            print(f"  Bug {bug_num:>2} ({bug_name:.<20s}) MISSING (no solution)")
            results[bug_num] = {"bug": bug_num, "score": None, "error": "missing"}
            continue
        if not workspace.exists():
            print(f"  Bug {bug_num:>2} ({bug_name:.<20s}) MISSING (no workspace)")
            results[bug_num] = {"bug": bug_num, "score": None, "error": "no workspace"}
            continue

        result = score_bug(bug_num, sol_file, workspace, args.timeout, suite)
        results[bug_num] = result
        total_tests += result["tests"]
        total_passed += result["passed"]

        status = f"{result['passed']}/{result['tests']}"
        score_str = f"{result['score']:.0%}" if result['score'] is not None else "N/A"
        print(f"  Bug {bug_num:>2} ({bug_name:.<20s}) {status:>5}  ({score_str})")
        for d in result.get("details", []):
            if isinstance(d, dict) and not d.get("pass", True):
                print(f"         FAIL: {d['test']}")
                print(f"               expected={d['expected']}, actual={d['actual']}")

    agg = total_passed / total_tests if total_tests > 0 else 0.0
    print(f"\n{'=' * 60}")
    print(f"  SEMANTIC FIDELITY (Ψ): {total_passed}/{total_tests} ({agg:.1%})")
    print(f"{'=' * 60}")

    out = {"total_tests": total_tests, "total_passed": total_passed,
           "semantic_score": round(agg, 3), "per_bug": results}
    print("\n=== SEMANTIC EVAL COMPLETE ===")
    print(json.dumps(out, indent=2, default=str))


if __name__ == "__main__":
    main()
