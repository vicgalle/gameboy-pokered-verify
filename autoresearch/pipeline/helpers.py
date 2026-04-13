"""
pipeline/helpers.py — Helper utilities for the formalization pipeline.

The researcher CAN modify this file to improve:
  - Assembly extraction (what code the formalizer sees)
  - Lean scaffolding (starting templates)
  - Error parsing (how build errors are presented)
"""

import re
from pathlib import Path

POKERED_DIR = Path("/Users/victorgallego/pokered")

# Maps bug name -> Lean module name
BUG_LEAN_NAMES = {
    "focus_energy": "FocusEnergy",
    "one_in_256": "OneIn256",
    "blaine_ai": "BlaineAI",
    "heal_overflow": "HealOverflow",
    "psywave_desync": "PsywaveDesync",
}


def generate_lean_scaffold(bug_name: str) -> str:
    """Generate a minimal starting scaffold for the formalizer.

    Kept deliberately minimal — the formalizer should figure out the
    structure from the bug description and its Lean knowledge.
    """
    return f"""\
import SM83

namespace PokeredBugs

/-! ### Definitions -/

-- TODO: define impl (buggy) and spec (correct) functions

/-! ### Proofs -/

-- TODO: prove properties about the bug

end PokeredBugs
"""


def parse_lean_errors(build_output: str) -> list[str]:
    """Parse Lean build output into a list of human-readable error descriptions."""
    errors = []

    for line in build_output.split('\n'):
        # Match Lean error format: file:line:col: error: message
        m = re.match(r'.*\.lean:(\d+):(\d+):\s*(error|warning):\s*(.*)', line)
        if m:
            line_num, col, level, msg = m.groups()
            errors.append(f"Line {line_num}: [{level}] {msg.strip()}")

        # Match "unknown identifier" specifically
        if 'unknown identifier' in line:
            m2 = re.search(r"unknown identifier '([^']+)'", line)
            if m2:
                errors.append(f"Unknown identifier: '{m2.group(1)}' — check spelling and imports")

        # Match type mismatch
        if 'type mismatch' in line.lower():
            errors.append(f"Type mismatch: {line.strip()[:200]}")

        # Match timeout
        if 'timeout' in line.lower() or 'deterministic timeout' in line.lower():
            errors.append("Tactic timeout — try a simpler proof strategy or break into smaller lemmas")

    # Deduplicate
    seen = set()
    unique = []
    for e in errors:
        if e not in seen:
            seen.add(e)
            unique.append(e)

    return unique[:20]  # Cap at 20 errors
