#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""
mine_logs.py — Extract agent process data from Claude Code conversation logs.

Mines the JSONL conversation transcripts stored by Claude Code in
~/.claude/projects/-Users-victorgallego-pokered-verify/*.jsonl

For each `lake build` invocation, extracts:
  - Timestamp
  - Which module/bug was being built
  - Whether it succeeded or failed (exit code)
  - The error content (Lean errors, type mismatches, tactic failures)

Outputs:
  1. Per-bug iteration table (for the paper's Table 1)
  2. Error category classification
  3. Full build trace timeline with attribution
  4. Detailed error traces per bug
"""

import json
import os
import re
import glob
from collections import defaultdict, Counter

PROJECT_DIR = os.path.expanduser(
    "~/.claude/projects/-Users-victorgallego-pokered-verify/"
)

# Map build targets to bug names
TARGET_TO_BUG = {
    "FocusEnergy": "Focus Energy",
    "OneIn256": "1/256 Miss",
    "BlaineAI": "Blaine AI",
    "PsywaveDesync": "Psywave Desync",
    "StatScaling": "Stat Scaling",
    "AccEvaCancel": "Acc/Eva Cancel",
    "ReflectOverflow": "Reflect Overflow",
    "BadgeReflect": "Badge+Reflect",
    "Substitute": "Substitute",
    "BideDesync": "Bide Desync",
    "CooltrainerF": "CooltrainerF",
    "HealOverflow": "Heal Overflow",
}

# Infrastructure file patterns (not bug-specific)
INFRA_PATTERNS = [
    r"SM83/\w+\.lean",
    r"Harness/\w+\.lean",
    r"lakefile",
    r"Main\.lean",
]

# Error classification patterns — ordered by specificity (most specific first)
ERROR_CATEGORIES = [
    (
        "tactic_decision",
        [
            r"native_decide.*evaluated.*(?:true|false)",
            r"`native_decide` .* is (?:true|false)",
            r"native_decide.*proposition",
            r"`decide`.*failed",
        ],
    ),
    (
        "type_mismatch",
        [
            r"type mismatch",
            r"has type.*but is expected to have type",
            r"Expected type must not contain",
        ],
    ),
    (
        "goal_state",
        [
            r"unsolved goals",
            r"`grind` failed",
            r"Tactic `subst` failed",
            r"Tactic `rewrite` failed",
            r"Tactic `split` failed",
            r"No goals to be solved",
        ],
    ),
    (
        "tactic_applicability",
        [
            r"omega could not prove",
            r"Tactic `unfold` failed",
            r"application type mismatch",
            r"Unknown identifier",
            r"Unknown constant",
        ],
    ),
    (
        "syntax_error",
        [
            r"unexpected token",
            r"expected.*token",
        ],
    ),
    (
        "typeclass_error",
        [
            r"failed to synthesize instance",
        ],
    ),
]


def classify_error(error_text: str) -> str:
    """Classify a Lean error into a category using first-match priority."""
    for category, patterns in ERROR_CATEGORIES:
        for pattern in patterns:
            if re.search(pattern, error_text, re.IGNORECASE):
                return category
    return "other"


def infer_bugs_from_content(content: str) -> list[str]:
    """Extract bug names mentioned in build output, prioritizing ERROR lines.

    Returns bugs mentioned in error lines first, then any others.
    For failed builds, only the error-line bugs are relevant.
    """
    error_bugs = []
    info_bugs = []
    for line in content.split("\n"):
        for key in TARGET_TO_BUG:
            pattern = f"Proofs/{key}.lean"
            if pattern not in line:
                continue
            if "error:" in line.lower() or "✖" in line:
                if key not in error_bugs:
                    error_bugs.append(key)
            else:
                if key not in info_bugs:
                    info_bugs.append(key)
    # Error-line bugs take priority; if none, fall back to info-line bugs
    return error_bugs if error_bugs else info_bugs


def is_infra_only_error(content: str) -> bool:
    """Check if all errors are in infrastructure files (SM83/, Harness/, etc.)."""
    error_lines = [
        l for l in content.split("\n") if "error:" in l.lower() or "✖" in l
    ]
    if not error_lines:
        return False
    for line in error_lines:
        # If any error line mentions a bug file, it's not infra-only
        for key in TARGET_TO_BUG:
            if key in line:
                return False
    return True


def extract_build_target(command: str) -> str:
    """Extract the bug/module name from a lake build command."""
    m = re.search(r"lake build PokeredBugs\.Proofs\.(\w+)", command)
    if m:
        return m.group(1)
    if re.search(r"lake build (pokered-verify|PokeredBugs|SM83)", command):
        return "__full__"
    if "lake build" in command:
        return "__full__"
    return "__other__"


def parse_sessions() -> list[dict]:
    """Parse all session JSONL files and extract deduplicated build events."""
    jsonl_files = sorted(glob.glob(os.path.join(PROJECT_DIR, "*.jsonl")))

    all_events = []
    seen_tool_ids = set()

    for fp in jsonl_files:
        session_id = os.path.basename(fp).replace(".jsonl", "")
        entries = []
        with open(fp) as f:
            for line in f:
                try:
                    entries.append(json.loads(line))
                except json.JSONDecodeError:
                    continue

        tool_calls = {}
        tool_results = {}

        for entry in entries:
            ts = entry.get("timestamp", "")
            etype = entry.get("type", "")

            if etype == "assistant":
                for block in entry.get("message", {}).get("content", []) or []:
                    if not isinstance(block, dict) or block.get("type") != "tool_use":
                        continue
                    tool_id = block.get("id", "")
                    cmd = block.get("input", {}).get("command", "")
                    if "lake" in cmd and "build" in cmd:
                        tool_calls[tool_id] = {
                            "command": cmd,
                            "timestamp": ts,
                            "session_id": session_id,
                        }

            elif etype == "user":
                for block in entry.get("message", {}).get("content", []) or []:
                    if (
                        not isinstance(block, dict)
                        or block.get("type") != "tool_result"
                    ):
                        continue
                    tool_id = block.get("tool_use_id", "")
                    result_content = block.get("content", "")
                    if isinstance(result_content, list):
                        result_content = "\n".join(
                            b.get("text", str(b))
                            for b in result_content
                            if isinstance(b, dict)
                        )
                    result_content = str(result_content)
                    exit_code = 0
                    m = re.match(r"Exit code (\d+)", result_content)
                    if m:
                        exit_code = int(m.group(1))
                    tool_results[tool_id] = {
                        "content": result_content,
                        "exit_code": exit_code,
                    }

        for tool_id, call in tool_calls.items():
            if tool_id in seen_tool_ids:
                continue
            seen_tool_ids.add(tool_id)

            result = tool_results.get(tool_id, {})
            content = result.get("content", "")
            success = result.get("exit_code", -1) == 0

            event = {
                "timestamp": call["timestamp"],
                "session_id": call["session_id"],
                "command": call["command"],
                "target": extract_build_target(call["command"]),
                "success": success,
                "result_content": content,
                "error_category": classify_error(content) if not success else None,
                "mentioned_bugs": infer_bugs_from_content(content),
                "is_infra_error": is_infra_only_error(content) if not success else False,
            }
            all_events.append(event)

    all_events.sort(key=lambda e: e["timestamp"])
    return all_events


def assign_events_to_bugs(events: list[dict]) -> dict[str, list[dict]]:
    """
    Assign build events to bugs with high-confidence attribution.

    Rules:
    1. Bug-specific target (e.g., lake build PokeredBugs.Proofs.BlaineAI)
       → always attributed to that bug.
    2. Full build with error mentioning exactly one bug file
       → attributed to that bug.
    3. Full build with error mentioning multiple bug files, or only infra errors
       → attributed to __infra__.
    4. Successful full build → attributed to the most recent bug IF it was the
       first success after a failure for that bug (convergence build).
       Subsequent successes are verification → __verification__.
    """
    bug_events = defaultdict(list)
    current_bug = None
    bug_has_converged = set()  # Bugs that have had their first success

    for event in events:
        target = event["target"]

        # Case 1: Bug-specific target
        if target in TARGET_TO_BUG:
            current_bug = target
            if event["success"]:
                bug_has_converged.add(target)
            else:
                # New failure after convergence = new iteration round
                bug_has_converged.discard(target)
            bug_events[target].append(event)
            continue

        # Case 2-4: Full build or other
        if target == "__full__":
            mentioned = event["mentioned_bugs"]

            if not event["success"]:
                # Failed full build
                if event["is_infra_error"] and not mentioned:
                    bug_events["__infra__"].append(event)
                elif len(mentioned) == 1:
                    bug = mentioned[0]
                    current_bug = bug
                    bug_has_converged.discard(bug)
                    bug_events[bug].append(event)
                elif len(mentioned) > 1:
                    # Multiple bugs mentioned — attribute to first mentioned
                    # (usually the one with the error)
                    bug = mentioned[0]
                    current_bug = bug
                    bug_has_converged.discard(bug)
                    bug_events[bug].append(event)
                elif current_bug and current_bug not in bug_has_converged:
                    # No bug mentioned but we're in an active iteration
                    bug_events[current_bug].append(event)
                else:
                    bug_events["__infra__"].append(event)
            else:
                # Successful full build
                if current_bug and current_bug not in bug_has_converged:
                    # First success = convergence build
                    bug_has_converged.add(current_bug)
                    bug_events[current_bug].append(event)
                elif mentioned:
                    # Verification build mentioning specific bugs
                    bug_events["__verification__"].append(event)
                else:
                    bug_events["__verification__"].append(event)
        else:
            bug_events["__other__"].append(event)

    return bug_events


def analyze_bugs(bug_events: dict) -> dict:
    """Compute per-bug metrics: iterations, error categories, time span."""
    results = {}

    for target, events in bug_events.items():
        if target.startswith("__"):
            continue

        bug_name = TARGET_TO_BUG.get(target, target)
        failures = [e for e in events if not e["success"]]
        successes = [e for e in events if e["success"]]

        # Iterations = failed builds + first success (convergence)
        iterations = len(failures) + (1 if successes else 0)

        error_categories = Counter()
        for e in failures:
            cat = e.get("error_category") or "other"
            error_categories[cat] += 1

        results[target] = {
            "bug_name": bug_name,
            "total_builds": len(events),
            "failures": len(failures),
            "successes": len(successes),
            "iterations": iterations,
            "error_categories": dict(error_categories),
            "first_timestamp": events[0]["timestamp"] if events else "",
            "last_timestamp": events[-1]["timestamp"] if events else "",
            "events": events,
        }

    return results


# ============================================================
#  Output formatters
# ============================================================


def print_per_bug_table(results: dict):
    print("\n" + "=" * 95)
    print("  PER-BUG ITERATION TABLE (for paper Table 1)")
    print("=" * 95)

    header = (
        f"  {'Bug':22s} {'Iters':>5s} {'Fails':>5s} {'1st OK':>6s} "
        f"{'Builds':>6s} {'Dominant Error':30s}"
    )
    print(header)
    print("  " + "-" * 80)

    total_iters = 0
    total_fails = 0
    total_builds = 0

    for target in sorted(results, key=lambda t: results[t]["first_timestamp"]):
        r = results[target]
        total_iters += r["iterations"]
        total_fails += r["failures"]
        total_builds += r["total_builds"]

        cats = r["error_categories"]
        dominant = f"{max(cats, key=cats.get)} ({cats[max(cats, key=cats.get)]})" if cats else "none"

        print(
            f"  {r['bug_name']:22s} {r['iterations']:5d} {r['failures']:5d} "
            f"{'yes' if r['successes'] else 'NO':>6s} "
            f"{r['total_builds']:6d} {dominant:30s}"
        )

    print("  " + "-" * 80)
    print(
        f"  {'TOTAL':22s} {total_iters:5d} {total_fails:5d} "
        f"{'':>6s} {total_builds:6d}"
    )
    print(f"\n  Median iterations: {sorted(r['iterations'] for r in results.values())[len(results)//2]}")


def print_error_summary(results: dict):
    print("\n" + "=" * 95)
    print("  ERROR CATEGORY DISTRIBUTION (bug-specific failures only)")
    print("=" * 95)

    all_cats = Counter()
    for r in results.values():
        for cat, count in r["error_categories"].items():
            all_cats[cat] += count

    total = sum(all_cats.values())
    for cat, count in all_cats.most_common():
        pct = 100 * count / max(total, 1)
        bar = "█" * int(pct / 2) + "░" * (50 - int(pct / 2))
        print(f"  {cat:25s} {bar} {count:3d} ({pct:.1f}%)")
    print(f"\n  Total bug-specific error cycles: {total}")


def print_timeline(events: list[dict], bug_events: dict):
    """Print timeline with attribution shown."""
    # Build reverse map: event timestamp+command -> attributed bug
    attr_map = {}
    for bug, evts in bug_events.items():
        for e in evts:
            key = (e["timestamp"], e["command"])
            attr_map[key] = bug

    print("\n" + "=" * 95)
    print("  FULL BUILD TRACE TIMELINE (with attribution)")
    print("=" * 95)

    for e in events:
        ts = e["timestamp"][11:19] if len(e["timestamp"]) > 19 else "?"
        ok = "OK" if e["success"] else "FAIL"
        target = e["target"]
        attr = attr_map.get((e["timestamp"], e["command"]), "?")
        attr_label = TARGET_TO_BUG.get(attr, attr)
        cat = e.get("error_category") or ""
        marker = "  " if e["success"] else ">>"

        print(f"  {marker} [{ts}] {target:20s} {ok:4s}  -> {attr_label:20s} {cat}")

        if not e["success"] and e["result_content"]:
            for line in e["result_content"].split("\n"):
                stripped = line.strip()
                if any(
                    kw in stripped.lower()
                    for kw in [
                        "error:",
                        "failed",
                        "mismatch",
                        "unsolved",
                        "native_decide",
                        "proposition",
                    ]
                ):
                    print(f"       | {stripped[:110]}")
                    break  # one line per failure is enough for timeline


def print_error_details(results: dict):
    print("\n" + "=" * 95)
    print("  DETAILED ERROR TRACES PER BUG")
    print("=" * 95)

    for target in sorted(results, key=lambda t: results[t]["first_timestamp"]):
        r = results[target]
        print(f"\n  --- {r['bug_name']} (iters={r['iterations']}, fails={r['failures']}) ---")

        for i, e in enumerate(r["events"]):
            ts = e["timestamp"][11:19] if len(e["timestamp"]) > 19 else "?"
            if e["success"]:
                print(f"    [{i+1}] [{ts}] OK")
                continue

            cat = e.get("error_category") or "?"
            print(f"    [{i+1}] [{ts}] FAIL ({cat})")

            # Show the key error lines
            for line in e["result_content"].split("\n"):
                stripped = line.strip()
                if any(
                    kw in stripped.lower()
                    for kw in [
                        "error:",
                        "failed",
                        "mismatch",
                        "unsolved goals",
                        "native_decide",
                        "proposition",
                        "⊢",
                        "omega",
                        "grind",
                    ]
                ):
                    print(f"         {stripped[:120]}")


def print_unattributed(bug_events: dict):
    """Show infra / verification / unattributed builds."""
    print("\n" + "=" * 95)
    print("  NON-BUG BUILDS")
    print("=" * 95)

    for category in ("__infra__", "__verification__", "__other__"):
        evts = bug_events.get(category, [])
        if not evts:
            continue
        fails = sum(1 for e in evts if not e["success"])
        print(f"\n  {category}: {len(evts)} builds ({fails} failures)")
        for e in evts[:10]:
            ts = e["timestamp"][11:19] if len(e["timestamp"]) > 19 else "?"
            ok = "OK" if e["success"] else "FAIL"
            snippet = ""
            if not e["success"]:
                for line in e["result_content"].split("\n"):
                    if "error:" in line.lower():
                        snippet = line.strip()[:80]
                        break
            print(f"    [{ts}] {ok:4s}  {snippet}")


def main():
    print("=" * 95)
    print("  CLAUDE CODE LOG MINING — pokered-verify")
    print("  Mining agent process data from conversation transcripts")
    print("=" * 95)

    events = parse_sessions()
    print(f"\n  Found {len(events)} unique lake build events across all sessions")

    bug_events = assign_events_to_bugs(events)
    n_bugs = len([k for k in bug_events if not k.startswith("__")])
    print(f"  Attributed to {n_bugs} bugs")

    results = analyze_bugs(bug_events)

    print_per_bug_table(results)
    print_error_summary(results)
    print_timeline(events, bug_events)
    print_error_details(results)
    print_unattributed(bug_events)

    print("\n" + "=" * 95)
    print("  Done. Use these numbers to populate the paper's Table 1.")
    print("=" * 95)


if __name__ == "__main__":
    main()
