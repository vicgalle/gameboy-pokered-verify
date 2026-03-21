#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""
metrics.py — Quantitative evaluation of pokered-verify proof effort.

Computes:
  • Lines of code breakdown (proof, definition, comment/doc, blank, #eval)
  • Theorem/lemma counts per file and per bug
  • Tactic usage frequency
  • Automation rate: automated tactics (native_decide, decide, rfl) vs manual (simp, omega, split, …)
  • Infrastructure vs proof lines
  • Summary table

Usage:
    python3 metrics.py
"""

import re
import os
from pathlib import Path
from collections import Counter, defaultdict

ROOT = Path(__file__).resolve().parent.parent

# ---------- file categories ----------

PROOF_FILES = sorted(ROOT.glob("PokeredBugs/Proofs/*.lean"))
INFRA_FILES = (
    sorted(ROOT.glob("SM83/*.lean"))
    + sorted(ROOT.glob("Harness/*.lean"))
    + [ROOT / "SM83.lean", ROOT / "PokeredBugs.lean", ROOT / "Harness.lean", ROOT / "Main.lean"]
)
INFRA_FILES = [f for f in INFRA_FILES if f.exists()]

# ---------- tactic classification ----------

# Automated: the kernel / decision procedures do all the work
AUTOMATED_TACTICS = {"native_decide", "decide", "rfl", "norm_num", "exact?", "apply?"}
# Manual / semi-manual: require human guidance
MANUAL_TACTICS = {
    "simp", "simp_all", "omega", "split", "constructor", "intro", "exact",
    "refine", "apply", "rw", "have", "let", "cases", "induction", "rename_i",
    "generalize", "unfold", "funext", "ext", "ring", "linarith", "contradiction",
}

ALL_KNOWN = AUTOMATED_TACTICS | MANUAL_TACTICS

# ---------- helpers ----------

def classify_lines(filepath):
    """Return counts dict for a single .lean file."""
    counts = {
        "total": 0, "blank": 0, "comment": 0, "docstring": 0,
        "theorem_decl": 0, "def_decl": 0, "proof_body": 0,
        "eval": 0, "import": 0, "other_code": 0,
    }
    tactic_counts = Counter()
    theorem_names = []
    in_docstring = False
    in_proof = False

    lines = filepath.read_text().splitlines()
    counts["total"] = len(lines)

    for line in lines:
        stripped = line.strip()

        # blank
        if not stripped:
            counts["blank"] += 1
            continue

        # doc-string block /-  ... -/
        if in_docstring:
            counts["docstring"] += 1
            if "-/" in stripped:
                in_docstring = False
            continue
        if stripped.startswith("/-"):
            counts["docstring"] += 1
            if "-/" not in stripped or stripped.endswith("/-"):
                in_docstring = True
            continue

        # single-line comment
        if stripped.startswith("--"):
            counts["comment"] += 1
            continue

        # import / namespace / open / section / end
        if re.match(r"^(import|namespace|open|section|end)\b", stripped):
            counts["import"] += 1
            continue

        # #eval
        if stripped.startswith("#eval"):
            counts["eval"] += 1
            continue

        # theorem / lemma declaration
        m = re.match(r"^(theorem|lemma|private theorem|private lemma)\s+(\S+)", stripped)
        if m:
            counts["theorem_decl"] += 1
            theorem_names.append(m.group(2))
            if ":= by" in stripped or ":= by" in stripped:
                in_proof = True
            continue

        # def / structure / inductive declaration
        if re.match(r"^(def|private def|structure|inductive|abbrev)\s+", stripped):
            counts["def_decl"] += 1
            in_proof = False
            continue

        # detect start of proof body
        if stripped == "by" or stripped.endswith(":= by"):
            in_proof = True

        # tactic counting (inside proof body or on declaration line)
        if in_proof or "by" in stripped:
            # extract tactic-like tokens
            for tok in re.findall(r'\b([a-z_]+(?:\?)?)\b', stripped):
                if tok in ALL_KNOWN:
                    tactic_counts[tok] += 1

        # proof body lines (heuristic: indented lines after a theorem/lemma)
        if in_proof:
            counts["proof_body"] += 1
            # end of proof: un-indented line (next decl) or blank handled above
            if not line[0].isspace() and not stripped.startswith("|"):
                in_proof = False
        else:
            counts["other_code"] += 1

    return counts, tactic_counts, theorem_names


def print_bar(label, value, max_val, width=30):
    bar_len = int(value / max(max_val, 1) * width)
    bar = "█" * bar_len + "░" * (width - bar_len)
    print(f"  {label:25s} {bar} {value:4d}")


# ---------- main ----------

def main():
    print("=" * 72)
    print("  POKERED-VERIFY  —  Quantitative Proof Metrics")
    print("=" * 72)

    # ---- per-file analysis ----
    all_proof_counts = {}
    all_proof_tactics = {}
    all_proof_theorems = {}

    all_infra_counts = {}

    for f in PROOF_FILES:
        c, t, th = classify_lines(f)
        all_proof_counts[f.name] = c
        all_proof_tactics[f.name] = t
        all_proof_theorems[f.name] = th

    for f in INFRA_FILES:
        c, _, _ = classify_lines(f)
        all_infra_counts[f.name] = c

    # ---- 1. Line counts per proof file ----
    print("\n" + "-" * 72)
    print("  1. LINE BREAKDOWN PER PROOF FILE")
    print("-" * 72)
    header = f"{'File':24s} {'Total':>6s} {'Proof':>6s} {'Def':>6s} {'Doc':>6s} {'Comment':>7s} {'Eval':>6s} {'Blank':>6s}"
    print(header)
    print("  " + "-" * (len(header) - 2))

    totals = Counter()
    for name, c in sorted(all_proof_counts.items()):
        print(f"  {name:22s} {c['total']:6d} {c['proof_body']:6d} {c['def_decl']:6d} "
              f"{c['docstring']:6d} {c['comment']:7d} {c['eval']:6d} {c['blank']:6d}")
        for k, v in c.items():
            totals[k] += v

    print("  " + "-" * (len(header) - 2))
    print(f"  {'TOTAL':22s} {totals['total']:6d} {totals['proof_body']:6d} {totals['def_decl']:6d} "
          f"{totals['docstring']:6d} {totals['comment']:7d} {totals['eval']:6d} {totals['blank']:6d}")

    # ---- 2. Theorem counts ----
    print("\n" + "-" * 72)
    print("  2. THEOREMS / LEMMAS PER BUG")
    print("-" * 72)
    total_theorems = 0
    for name, ths in sorted(all_proof_theorems.items()):
        bug_name = name.replace(".lean", "")
        print(f"\n  {bug_name} ({len(ths)} theorems):")
        for th in ths:
            print(f"    - {th}")
        total_theorems += len(ths)
    print(f"\n  Total theorems/lemmas: {total_theorems}")

    # ---- 3. Tactic frequency ----
    print("\n" + "-" * 72)
    print("  3. TACTIC USAGE (across all proof files)")
    print("-" * 72)
    merged = Counter()
    for t in all_proof_tactics.values():
        merged += t
    max_count = max(merged.values()) if merged else 1
    for tactic, count in merged.most_common():
        kind = "AUTO" if tactic in AUTOMATED_TACTICS else "MANUAL"
        print_bar(f"{tactic} [{kind}]", count, max_count)

    # ---- 4. Automation rate ----
    print("\n" + "-" * 72)
    print("  4. AUTOMATION RATE")
    print("-" * 72)

    auto_total = sum(merged[t] for t in AUTOMATED_TACTICS if t in merged)
    manual_total = sum(merged[t] for t in MANUAL_TACTICS if t in merged)
    grand = auto_total + manual_total

    print(f"\n  Automated tactic invocations:  {auto_total:4d}  "
          f"({100*auto_total/max(grand,1):.1f}%)")
    print(f"  Manual tactic invocations:     {manual_total:4d}  "
          f"({100*manual_total/max(grand,1):.1f}%)")
    print(f"  Total tactic invocations:      {grand:4d}")

    # per-file automation
    print(f"\n  {'File':24s} {'Auto':>5s} {'Manual':>7s} {'Auto%':>6s}")
    print("  " + "-" * 44)
    for name in sorted(all_proof_tactics):
        tc = all_proof_tactics[name]
        a = sum(tc[t] for t in AUTOMATED_TACTICS if t in tc)
        m = sum(tc[t] for t in MANUAL_TACTICS if t in tc)
        pct = 100 * a / max(a + m, 1)
        print(f"  {name:22s} {a:5d} {m:7d} {pct:5.1f}%")

    # ---- 5. Infrastructure vs proofs ----
    print("\n" + "-" * 72)
    print("  5. INFRASTRUCTURE vs PROOF CODE")
    print("-" * 72)

    infra_total = sum(c["total"] for c in all_infra_counts.values())
    proof_total = totals["total"]

    print(f"\n  Infrastructure (SM83 + Harness):  {infra_total:5d} lines")
    print(f"  Proof files (4 bugs):             {proof_total:5d} lines")
    print(f"  Grand total:                      {infra_total + proof_total:5d} lines")
    print(f"\n  Proof / Total ratio:              {100*proof_total/max(infra_total+proof_total,1):.1f}%")
    print(f"  Infra / Total ratio:              {100*infra_total/max(infra_total+proof_total,1):.1f}%")

    # ---- 6. Per-bug summary ----
    print("\n" + "-" * 72)
    print("  6. PER-BUG SUMMARY TABLE")
    print("-" * 72)

    bug_meta = {
        "FocusEnergy.lean":    ("Focus Energy",     "Wrong bitwise op (srl vs sla)"),
        "BlaineAI.lean":       ("Blaine AI",        "Missing HP precondition"),
        "OneIn256.lean":       ("1/256 Miss",       "Off-by-one (< vs <=)"),
        "PsywaveDesync.lean":  ("Psywave Desync",   "Symmetry violation (link)"),
    }

    print(f"\n  {'Bug':18s} {'Lines':>5s} {'Thms':>5s} {'Auto%':>6s}  Category")
    print("  " + "-" * 60)

    for name in sorted(all_proof_counts):
        c = all_proof_counts[name]
        tc = all_proof_tactics[name]
        ths = all_proof_theorems[name]
        a = sum(tc[t] for t in AUTOMATED_TACTICS if t in tc)
        m = sum(tc[t] for t in MANUAL_TACTICS if t in tc)
        pct = 100 * a / max(a + m, 1)
        meta = bug_meta.get(name, (name, ""))
        print(f"  {meta[0]:18s} {c['total']:5d} {len(ths):5d} {pct:5.1f}%  {meta[1]}")

    # ---- 7. Theorem-level automation ----
    print("\n" + "-" * 72)
    print("  7. THEOREM-LEVEL AUTOMATION")
    print("-" * 72)
    print("\n  Classifies each theorem by whether its proof is fully automated")
    print("  (closed by native_decide / decide / rfl alone, possibly wrapped")
    print("  in exact / have / refine scaffolding) vs needs manual tactics.\n")

    auto_theorems = 0
    manual_theorems = 0
    for f in PROOF_FILES:
        text = f.read_text()
        # Split into theorem blocks
        thm_pattern = re.compile(
            r'^(?:private\s+)?(?:theorem|lemma)\s+(\S+).*?:=\s*by\b(.*?)(?=^(?:private\s+)?(?:theorem|lemma|def|structure|inductive|abbrev|end|#eval|/-)\b|\Z)',
            re.MULTILINE | re.DOTALL,
        )
        for m in thm_pattern.finditer(text):
            name = m.group(1)
            body = m.group(2)
            # Extract all tactic-like words from the body
            body_tactics = set(re.findall(r'\b([a-z_]+(?:\?)?)\b', body)) & ALL_KNOWN
            # "scaffolding" tactics that just wrap an automated proof
            scaffolding = {"exact", "have", "refine", "let", "intro", "constructor"}
            non_scaffold = body_tactics - scaffolding - AUTOMATED_TACTICS
            uses_auto = body_tactics & AUTOMATED_TACTICS
            is_fully_auto = len(non_scaffold) == 0 and len(uses_auto) > 0
            label = "AUTO" if is_fully_auto else "MANUAL"
            if is_fully_auto:
                auto_theorems += 1
            else:
                manual_theorems += 1
            print(f"  [{label:6s}] {name}")

    thm_total = auto_theorems + manual_theorems
    print(f"\n  Fully automated theorems:  {auto_theorems:3d} / {thm_total}  "
          f"({100*auto_theorems/max(thm_total,1):.1f}%)")
    print(f"  Manual / hybrid theorems:  {manual_theorems:3d} / {thm_total}  "
          f"({100*manual_theorems/max(thm_total,1):.1f}%)")

    # ---- 8. Key ratios ----
    print("\n" + "-" * 72)
    print("  8. KEY RATIOS")
    print("-" * 72)

    avg_thm_per_bug = total_theorems / max(len(PROOF_FILES), 1)
    proof_lines_per_thm = totals["proof_body"] / max(total_theorems, 1)
    doc_ratio = (totals["docstring"] + totals["comment"]) / max(totals["total"], 1)

    print(f"\n  Bugs verified:                    {len(PROOF_FILES)}")
    print(f"  Total theorems proved:            {total_theorems}")
    print(f"  Avg theorems per bug:             {avg_thm_per_bug:.1f}")
    print(f"  Avg proof lines per theorem:      {proof_lines_per_thm:.1f}")
    print(f"  Documentation ratio:              {100*doc_ratio:.1f}% of proof file lines")
    print(f"  Overall automation rate:           {100*auto_total/max(grand,1):.1f}%")

    print("\n" + "=" * 72)
    print("  Done.")
    print("=" * 72)


if __name__ == "__main__":
    main()
