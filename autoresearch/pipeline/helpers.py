"""
Pipeline configuration -- helper functions.

The researcher can modify these to improve:
- Assembly extraction (what pokered code the formalizer sees)
- Error parsing (how compilation errors are presented)
- Lean scaffolding (starting templates)

These are the primary levers for improving formalizer performance.
"""

import re
import subprocess
from pathlib import Path


# ---------------------------------------------------------------------------
# Assembly extraction
# ---------------------------------------------------------------------------

# Mapping from bug number to relevant assembly targets in the pokered disassembly.
# The researcher can add/modify labels, files, and grep patterns to provide
# better context to the formalizer.
BUG_ASM_TARGETS = {
    1: {
        "description": "Focus Energy critical hit rate bug",
        "labels": ["CriticalHitTest"],
        "files": ["engine/battle/core.asm"],
        "grep_patterns": ["FocusEnergyEffect"],
    },
    2: {
        "description": "1/256 miss chance on accuracy and critical hit checks",
        "labels": ["MoveHitTest", "CriticalHitTest"],
        "files": ["engine/battle/core.asm"],
        "grep_patterns": [],
    },
    3: {
        "description": "Blaine AI uses Super Potion at full HP",
        "labels": ["BlaineAI", "AIUseSuperPotion", "AICheckIfHPBelowFraction"],
        "files": ["engine/battle/trainer_ai.asm"],
        "grep_patterns": [],
    },
    4: {
        "description": "Heal moves fail at specific HP gaps due to overflow",
        "labels": ["HealEffect_"],
        "files": ["engine/battle/move_effects/heal.asm"],
        "grep_patterns": [],
    },
    5: {
        "description": "Psywave causes link battle desynchronization",
        "labels": [],
        "files": ["engine/battle/core.asm", "engine/battle/effects.asm"],
        "grep_patterns": ["PsywaveEffect", "Psywave"],
    },
    6: {
        "description": "Substitute creates 0 HP shield and leaves user at 0 HP",
        "labels": ["SubstituteEffect_"],
        "files": ["engine/battle/move_effects/substitute.asm"],
        "grep_patterns": [],
    },
    7: {
        "description": "Bide accumulated damage link desync (asymmetric memory zeroing)",
        "labels": ["FaintEnemyPokemon"],
        "files": ["engine/battle/core.asm"],
        "grep_patterns": ["RemoveFaintedPlayerMon", "wPlayerBideAccumulatedDamage"],
    },
    8: {
        "description": "Reflect/Light Screen overflow reduces defense instead of doubling",
        "labels": ["ReflectLightScreenEffect_"],
        "files": ["engine/battle/move_effects/reflect_light_screen.asm"],
        "grep_patterns": ["scaleStats"],
    },
    9: {
        "description": "Accuracy/Evasion stage boosts do not cancel when equal",
        "labels": ["CalcHitChance"],
        "files": ["engine/battle/core.asm"],
        "grep_patterns": ["StatModifierRatios"],
    },
    10: {
        "description": "Badge boost stacking enables catastrophic Reflect overflow",
        "labels": ["ApplyBadgeStatBoosts"],
        "files": ["engine/battle/core.asm"],
        "grep_patterns": ["applyBoostToStat"],
    },
}


def extract_relevant_asm(bug_num: int, pokered_path: Path) -> str:
    """Extract relevant assembly from pokered for a given bug.

    Searches for labels and grep patterns in the assembly source files.
    Returns a formatted string of relevant assembly snippets.

    The researcher can improve this by:
    - Adding more labels/patterns per bug
    - Increasing context window around matches
    - Adding cross-references between routines
    """
    targets = BUG_ASM_TARGETS.get(bug_num)
    if targets is None:
        return ""

    snippets = []

    # Extract labeled routines (full routine until next label)
    for label in targets.get("labels", []):
        for asm_file in targets.get("files", []):
            filepath = pokered_path / asm_file
            if not filepath.exists():
                continue
            snippet = _extract_routine(filepath, label)
            if snippet:
                snippets.append(
                    f"### {label} (from {asm_file})\n```asm\n{snippet}\n```"
                )

    # Grep for additional patterns with context
    for pattern in targets.get("grep_patterns", []):
        for asm_file in targets.get("files", []):
            filepath = pokered_path / asm_file
            if not filepath.exists():
                continue
            matches = _grep_context(filepath, pattern, context=10)
            if matches and not any(pattern in s for s in snippets):
                snippets.append(
                    f"### Grep: '{pattern}' in {asm_file}\n```asm\n{matches}\n```"
                )

    return "\n\n".join(snippets) if snippets else ""


def _extract_routine(filepath: Path, label: str, max_lines: int = 80) -> str:
    """Extract a labeled routine from an assembly file.

    Reads from the label until the next top-level label or max_lines.
    """
    content = filepath.read_text()
    lines = content.split("\n")

    start = None
    for i, line in enumerate(lines):
        if re.match(rf"^{re.escape(label)}\b", line):
            start = i
            break

    if start is None:
        return ""

    # Read until next top-level label or max_lines
    end = start + 1
    while end < len(lines) and end - start < max_lines:
        # Stop at next top-level label (not indented, ends with colon)
        if re.match(r"^[A-Za-z_]\w*:", lines[end]) and end > start + 1:
            break
        end += 1

    return "\n".join(lines[start:end])


def _grep_context(filepath: Path, pattern: str, context: int = 10) -> str:
    """Grep for a pattern with surrounding context lines."""
    try:
        result = subprocess.run(
            ["grep", "-n", "-i", f"-C{context}", pattern, str(filepath)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.stdout:
            # Limit output to first 50 lines to avoid overwhelming the prompt
            lines = result.stdout.strip().split("\n")[:50]
            return "\n".join(lines)
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass
    return ""


# ---------------------------------------------------------------------------
# Lean error parsing
# ---------------------------------------------------------------------------

def parse_lean_errors(stderr: str) -> str:
    """Parse lake build errors into a structured summary.

    The researcher can improve this to:
    - Categorize errors (type mismatch, tactic failure, unknown identifier, etc.)
    - Suggest specific fixes for common error patterns
    - Highlight the most important error (first one)
    """
    if not stderr:
        return "No error output captured."

    issues = []
    lines = stderr.split("\n")

    for i, line in enumerate(lines):
        # Match Lean error format: file:line:col: error: message
        match = re.match(r".*?:(\d+):\d+:\s*(error|warning):\s*(.*)", line)
        if match:
            line_num = match.group(1)
            severity = match.group(2)
            message = match.group(3)

            # Collect continuation lines for context
            detail_lines = [message]
            j = i + 1
            while j < len(lines) and not re.match(r".*?:\d+:\d+:", lines[j]):
                stripped = lines[j].strip()
                if stripped:
                    detail_lines.append(stripped)
                j += 1
                if len(detail_lines) > 5:
                    break

            full_msg = " ".join(detail_lines)
            issues.append(f"- Line {line_num} ({severity}): {full_msg}")

    if issues:
        return "\n".join(issues[:10])  # Show at most 10 issues

    # Fallback: return last meaningful lines of stderr
    meaningful = [l for l in lines if l.strip() and "warning" not in l.lower()]
    if meaningful:
        return "Could not parse structured errors. Raw output:\n" + "\n".join(meaningful[-10:])

    return "Build produced output but no parseable errors."


# ---------------------------------------------------------------------------
# Lean scaffolding
# ---------------------------------------------------------------------------

def generate_lean_scaffold(bug_num: int) -> str:
    """Generate a starting Lean scaffold for a bug.

    The researcher can customize this per bug category for better starting points.
    Currently returns a generic template.
    """
    desc = BUG_ASM_TARGETS.get(bug_num, {}).get("description", "")
    return f"""\
import SM83

namespace AutoResearch

-- Bug #{bug_num}: {desc}

-- Model the buggy behavior (matching the assembly)
def impl (input : BitVec 8) : BitVec 8 := sorry

-- Model the intended/correct behavior
def spec (input : BitVec 8) : BitVec 8 := sorry

-- L1: Bug exists (find a concrete witness)
theorem bug_exists : \\u2203 x, impl x \\u2260 spec x := sorry

end AutoResearch
"""
