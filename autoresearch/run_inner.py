#!/usr/bin/env python3
"""
run_inner.py -- Fixed orchestrator for the autoresearch inner loop.

For each of 5 bugs:
  1. Load bug description + extract assembly context via pipeline helpers
  2. Run K iterations: prompt -> LLM -> Lean code -> lake build -> feedback
  3. Save the best (highest-scoring) attempt

Reports aggregate score Phi(c) across all 5 bugs.

This file is FROZEN -- the researcher agent must NOT modify it.
The researcher modifies files in pipeline/ only.

Usage:
    uv run python3 run_inner.py
    uv run python3 run_inner.py --model gemini-2.5-pro-preview
    uv run python3 run_inner.py --output-dir runs/exp1
"""

from __future__ import annotations

import argparse
import asyncio
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

import yaml

# Allow launching Claude Agent SDK from within a Claude Code session
os.environ.pop("CLAUDECODE", None)


# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
BUGS_DIR = SCRIPT_DIR / "bugs"
TEMPLATE_DIR = SCRIPT_DIR / "template"
PIPELINE_DIR = SCRIPT_DIR / "pipeline"
GROUND_TRUTH_FILE = SCRIPT_DIR / "ground_truth.json"
POKERED_PATH = Path("/Users/victorgallego/pokered")

# Infrastructure source (from parent Lean project)
SM83_DIR = PROJECT_ROOT / "SM83"
SM83_LEAN = PROJECT_ROOT / "SM83.lean"
HARNESS_DIR = PROJECT_ROOT / "Harness"
HARNESS_LEAN = PROJECT_ROOT / "Harness.lean"

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


def log(msg: str = ""):
    """Print to stderr so stdout is reserved for machine-readable output."""
    sys.stderr.write(msg + "\n")
    sys.stderr.flush()


# ---------------------------------------------------------------------------
# LLM dispatch (Claude Agent SDK + Gemini API)
# ---------------------------------------------------------------------------

def _is_gemini_model(model: str) -> bool:
    """Check if the model name refers to a Gemini model."""
    return model.startswith("gemini")


async def _call_llm(
    system_prompt: str, user_prompt: str, model: str
) -> tuple[str, str]:
    """Call an LLM and return (full_text, reasoning).

    Dispatches to Claude Agent SDK or Google GenAI based on model name.
    """
    if _is_gemini_model(model):
        return await _call_gemini(system_prompt, user_prompt, model)
    else:
        return await _call_claude(system_prompt, user_prompt, model)


async def _call_claude(
    system_prompt: str, user_prompt: str, model: str
) -> tuple[str, str]:
    """Call Claude via the Agent SDK."""
    from claude_agent_sdk import (
        query,
        ClaudeAgentOptions,
        AssistantMessage,
        ResultMessage,
        TextBlock,
        ThinkingBlock,
    )
    from claude_agent_sdk._errors import MessageParseError

    options = ClaudeAgentOptions(
        system_prompt=system_prompt,
        max_turns=1,
        model=model,
        effort="high",
    )

    text_parts: list[str] = []
    thinking_parts: list[str] = []

    try:
        async for message in query(prompt=user_prompt, options=options):
            if isinstance(message, AssistantMessage):
                for block in message.content:
                    if isinstance(block, TextBlock):
                        text_parts.append(block.text)
                    elif isinstance(block, ThinkingBlock):
                        thinking_parts.append(block.thinking)
            elif isinstance(message, ResultMessage):
                if message.total_cost_usd:
                    log(f"  API cost: ${message.total_cost_usd:.4f}")
    except MessageParseError as e:
        log(f"  Warning: SDK parse error (skipped): {e}")
        if not text_parts:
            raise

    full_text = "\n".join(text_parts)
    reasoning = "\n".join(thinking_parts) if thinking_parts else ""
    return full_text, reasoning


async def _call_gemini(
    system_prompt: str, user_prompt: str, model: str
) -> tuple[str, str]:
    """Call Gemini via the Google GenAI SDK.

    Requires the ``google-genai`` package and a GEMINI_API_KEY (or
    GOOGLE_API_KEY) environment variable.
    """
    from google import genai
    from google.genai import types

    client = genai.Client()

    response = await client.aio.models.generate_content(
        model=model,
        contents=user_prompt,
        config=types.GenerateContentConfig(
            system_instruction=system_prompt,
            thinking_config=types.ThinkingConfig(thinking_budget=16384),
        ),
    )

    full_text = ""
    reasoning = ""
    if response.candidates and response.candidates[0].content:
        for part in response.candidates[0].content.parts:
            if hasattr(part, "thought") and part.thought:
                reasoning += part.text
            else:
                full_text += part.text

    return full_text, reasoning


# ---------------------------------------------------------------------------
# Pipeline loading
# ---------------------------------------------------------------------------

def load_config() -> dict:
    """Load pipeline configuration from config.yaml."""
    config_path = PIPELINE_DIR / "config.yaml"
    with open(config_path) as f:
        return yaml.safe_load(f)


def load_system_prompt() -> str:
    """Load the formalizer system prompt."""
    return (PIPELINE_DIR / "system_prompt.md").read_text()


def load_feedback_template() -> str:
    """Load the feedback template for compilation errors."""
    return (PIPELINE_DIR / "feedback_template.md").read_text()


def import_pipeline_module(name: str):
    """Import a Python module from the pipeline/ directory by absolute path."""
    module_path = PIPELINE_DIR / f"{name}.py"
    spec = importlib.util.spec_from_file_location(f"pipeline.{name}", module_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ---------------------------------------------------------------------------
# Information barrier enforcement
# ---------------------------------------------------------------------------

def check_information_barrier(prompt: str):
    """Quick check that ground truth content hasn't leaked into the prompt.

    Checks for verbatim key_insights from ground_truth.json -- these are
    specific enough that accidental matches are unlikely.
    """
    if not GROUND_TRUTH_FILE.exists():
        return
    with open(GROUND_TRUTH_FILE) as f:
        gt = json.load(f)
    for bug_key, bug_gt in gt.items():
        if not isinstance(bug_gt, dict):
            continue
        for insight in bug_gt.get("key_insights", []):
            if insight in prompt:
                log(
                    f"  WARNING: Information barrier -- ground truth insight "
                    f"detected in prompt for bug {bug_key}"
                )
                return


# ---------------------------------------------------------------------------
# Lean code extraction
# ---------------------------------------------------------------------------

def extract_lean_code(response: str) -> str | None:
    """Extract Lean code from an LLM response.

    Looks for ```lean ... ``` blocks first, then generic code blocks
    that contain Lean keywords.
    """
    # Try ```lean blocks
    matches = re.findall(r"```lean\n(.*?)```", response, re.DOTALL)
    if matches:
        return max(matches, key=len)

    # Try generic code blocks containing Lean keywords
    matches = re.findall(r"```\n(.*?)```", response, re.DOTALL)
    for m in matches:
        if "namespace" in m or "theorem" in m or "import SM83" in m:
            return m

    return None


# ---------------------------------------------------------------------------
# Workspace management
# ---------------------------------------------------------------------------

def create_workspace(run_dir: Path, bug_num: int) -> Path:
    """Create a Lean workspace for a specific bug.

    Copies SM83/Harness infrastructure and Lean project template.
    The workspace is reused across iterations for build caching.
    """
    ws = run_dir / f"workspace_bug{bug_num}"
    ws.mkdir(parents=True, exist_ok=True)

    # Copy SM83 infrastructure
    if not (ws / "SM83").exists():
        shutil.copytree(SM83_DIR, ws / "SM83")
    if not (ws / "SM83.lean").exists():
        shutil.copy2(SM83_LEAN, ws / "SM83.lean")

    # Copy Harness
    if not (ws / "Harness").exists():
        shutil.copytree(HARNESS_DIR, ws / "Harness")
    if not (ws / "Harness.lean").exists():
        shutil.copy2(HARNESS_LEAN, ws / "Harness.lean")

    # Copy Lean project template
    for f in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]:
        src = TEMPLATE_DIR / f
        if src.exists() and not (ws / f).exists():
            shutil.copy2(src, ws / f)

    return ws


def write_solution(workspace: Path, lean_code: str):
    """Write Solution.lean to the workspace."""
    (workspace / "Solution.lean").write_text(lean_code)


def run_lake_build(workspace: Path, timeout: int = 300) -> tuple[bool, str]:
    """Run ``lake build Solution`` in the workspace and return (success, output).

    We target Solution explicitly: the template lakefile has no defaultTargets,
    so a bare ``lake build`` does 0 jobs and trivially succeeds — which would
    silently masquerade as a clean compile.
    """
    try:
        result = subprocess.run(
            ["lake", "build", "Solution"],
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        success = result.returncode == 0
        # Always return combined output so the probe's `info:` lines are visible
        # on success AND error context is visible on failure.
        output = (result.stdout or "") + "\n" + (result.stderr or "")
        return success, output
    except subprocess.TimeoutExpired:
        return False, f"TIMEOUT: lake build exceeded {timeout}s"
    except FileNotFoundError:
        return False, "ERROR: lake not found in PATH"


# ---------------------------------------------------------------------------
# Lean probe — inspects elaborated theorem types for Phi' scoring.
#
# Appended to Solution.lean along with `import Lean`. After `lake build`, each
# `logInfo` call emits a line prefixed `info: Solution.lean:L:C: PROBE_...`
# which Python parses. Gives us AST-level facts that source regex cannot:
#   - a theorem uses a NON-vacuous `∀` (Expr.forallE over a non-trivial type)
#   - a theorem's TYPE references `AutoResearch.impl` / `AutoResearch.spec`
# ---------------------------------------------------------------------------

PROBE_CODE = '''\
-- === AUTORESEARCH Φ' PROBE (appended by run_inner.py) ===
section AutoResearchProbeSection
open Lean

private def _autoresearchProbeIsVacuousType (ty : Expr) : Bool :=
  match ty.getAppFn with
  | .const n _ => n == ``Unit || n == ``PUnit || n == ``True
  | _ => false

private def _autoresearchProbeHasNonVacuousForall (e : Expr) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .forallE _ ty _ _ => !_autoresearchProbeIsVacuousType ty
    | _ => false).isSome

private def _autoresearchProbeRefersTo (target : Name) (e : Expr) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .const n _ => n == target
    | _ => false).isSome

open Lean Elab Command in
elab "#probe_autoresearch" : command => do
  let env ← getEnv
  let mut items : Array String := #[]
  for p in env.constants.toList do
    let n := p.1
    let info := p.2
    match info with
    | .thmInfo _ =>
      let nameStr := n.toString
      -- Exclude Lean-generated proof helpers (e.g. `foo._proof_1_1` emitted
      -- when a theorem uses `by native_decide; exact h`) so they don't
      -- inflate the user-written theorem count.
      let parts := nameStr.splitOn "."
      let isGenerated := parts.any (fun s => s.startsWith "_proof_" || s.startsWith "_eq_" || s.startsWith "_sunfold")
      if nameStr.startsWith "AutoResearch." && !isGenerated then
        let ty := info.type
        let nv := _autoresearchProbeHasNonVacuousForall ty
        let ri := _autoresearchProbeRefersTo `AutoResearch.impl ty
        let rs := _autoresearchProbeRefersTo `AutoResearch.spec ty
        items := items.push s!"PROBE_THM|{nameStr}|forall={nv}|impl={ri}|spec={rs}"
    | _ => pure ()
  for item in items do
    logInfo item
  logInfo s!"PROBE_END|count={items.size}"

end AutoResearchProbeSection

#probe_autoresearch
'''


def augment_with_probe(lean_code: str) -> str:
    """Prepend `import Lean` (if absent) and append the probe."""
    has_lean_import = bool(
        re.search(r"^\s*import\s+Lean\s*$", lean_code, re.MULTILINE)
    )
    prefix = "" if has_lean_import else "import Lean\n"
    return prefix + lean_code + "\n\n" + PROBE_CODE


def parse_probe_output(build_output: str) -> dict | None:
    """Parse `PROBE_*` lines from lake build output.

    Returns None if `PROBE_END` was never observed (probe didn't run — e.g. a
    compile error upstream). Otherwise returns a dict with per-theorem facts.
    """
    theorems: list[dict] = []
    probe_count: int | None = None
    for raw_line in build_output.split("\n"):
        stripped = raw_line.strip()
        # Each logInfo emits `info: <file>:L:C: <message>` on its first line.
        m = re.match(r"info:\s+\S+:\d+:\d+:\s+(.*)$", stripped)
        content = m.group(1).strip() if m else stripped

        m_thm = re.match(
            r"PROBE_THM\|([^|]+)\|forall=(true|false)\|impl=(true|false)\|spec=(true|false)$",
            content,
        )
        if m_thm:
            theorems.append({
                "name": m_thm.group(1),
                "nonvacuous_forall": m_thm.group(2) == "true",
                "refs_impl": m_thm.group(3) == "true",
                "refs_spec": m_thm.group(4) == "true",
            })
            continue

        m_end = re.match(r"PROBE_END\|count=(\d+)$", content)
        if m_end:
            probe_count = int(m_end.group(1))

    if probe_count is None:
        return None
    return {"theorems": theorems, "count": probe_count}


def run_clean_build(workspace: Path, timeout: int = 600) -> tuple[bool, str]:
    """Run `lake clean` then `lake build`. Defeats olean-cache exploits."""
    try:
        subprocess.run(
            ["lake", "clean"],
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT: lake clean exceeded 60s"
    except FileNotFoundError:
        return False, "ERROR: lake not found in PATH"
    return run_lake_build(workspace, timeout=timeout)


# ---------------------------------------------------------------------------
# Source-level helpers — scope keyword matching to theorem bodies (not names,
# not comments, not def source). Used by theme-coverage component of Phi'.
# ---------------------------------------------------------------------------

_COMMENT_BLOCK_RE = re.compile(r"/-[\s\S]*?-/")
_COMMENT_LINE_RE = re.compile(r"--[^\n]*")

_TOP_DECL_KEYWORDS = r"(?:private\s+)?(?:theorem|lemma|def|structure|inductive|class|instance|namespace|end|example)"


def _strip_comments(code: str) -> str:
    code = _COMMENT_BLOCK_RE.sub("", code)
    return _COMMENT_LINE_RE.sub("", code)


def extract_theorem_source_blocks(code: str) -> list[str]:
    """Return text of each `theorem`/`lemma` declaration (stripped of comments).

    Boundary: the block ends right before the next top-level keyword (`def`,
    `theorem`, `end`, `#...`, etc.) or EOF. Used to restrict theme-keyword
    matching to theorem bodies rather than over the whole source.
    """
    no_cmts = _strip_comments(code)
    pat = re.compile(
        r"(?:^|\n)\s*(?:private\s+)?(?:theorem|lemma)\b"
        r"[\s\S]*?"
        rf"(?=\n\s*(?:{_TOP_DECL_KEYWORDS}\b|#)|\Z)",
        re.MULTILINE,
    )
    return [m.group(0) for m in pat.finditer(no_cmts)]


def _strip_theorem_name_from_block(block: str) -> str:
    """Replace the theorem's own identifier with `_` so name-based keyword
    matches (e.g. `bug_exists` matching 'exists') are prevented."""
    return re.sub(
        r"(\s*(?:private\s+)?(?:theorem|lemma)\s+)\w+",
        r"\1_",
        block,
        count=1,
    )


def detect_theme_in_theorem_blocks(blocks: list[str]) -> set[str]:
    """Detect L1/L2/L3/L4 by keywords in theorem block text (names stripped)."""
    if not blocks:
        return set()
    cleaned = " ".join(_strip_theorem_name_from_block(b) for b in blocks).lower()
    levels: set[str] = set()
    if "\u2203" in cleaned or re.search(r"\bexists\b", cleaned):
        levels.add("L1")
    if (
        "\u2200" in cleaned
        or "\u2194" in cleaned
        or re.search(r"\bforall\b", cleaned)
        or re.search(r"\biff\b", cleaned)
    ):
        levels.add("L2")
    if re.search(r"\bfix\b", cleaned) or re.search(r"\bcorrect\b", cleaned):
        levels.add("L3")
    if any(kw in cleaned for kw in ("desync", "player", "enemy", "diverge", "link")):
        levels.add("L4")
    return levels


# ---------------------------------------------------------------------------
# Scoring functions — legacy Phi (for ablation) and hardened Phi'.
# ---------------------------------------------------------------------------

def count_theorems(lean_code: str) -> int:
    """Count theorem and lemma declarations in Lean code (source-level)."""
    return len(
        re.findall(r"(?:^|\n)\s*(?:private\s+)?(?:theorem|lemma)\s+\w+", lean_code)
    )


def score_solution_legacy(
    lean_code: str | None,
    compiles: bool,
    bug_num: int,
    ground_truth: dict,
) -> float:
    """Legacy Phi — kept for ablation vs the hardened Phi'.

    +0.10 compiles  · +0.05/thm (≤0.25)  · +0.20 sorry-free
    +0.25 theme (source-wide regex)  · +0.10 impl/spec defined  · +0.10 ∀ anywhere
    """
    if lean_code is None:
        return 0.0
    score = 0.0
    if compiles:
        score += 0.10
    score += min(count_theorems(lean_code) * 0.05, 0.25)
    if "sorry" not in lean_code:
        score += 0.20
    lower = lean_code.lower()
    legacy_levels: set[str] = set()
    if any(kw in lower for kw in ["bug_exists", "witness", "\u2203", "exists"]):
        legacy_levels.add("L1")
    if any(kw in lower for kw in ["always", "iff", "characteriz", "\u2194", "forall", "\u2200"]):
        legacy_levels.add("L2")
    if any(kw in lower for kw in ["fix", "correct"]):
        legacy_levels.add("L3")
    if any(kw in lower for kw in ["desync", "player", "enemy", "diverge", "link", "bide"]):
        legacy_levels.add("L4")
    gt = ground_truth.get(str(bug_num), {})
    gt_levels = set(gt.get("levels", []))
    if gt_levels:
        score += 0.25 * len(legacy_levels & gt_levels) / len(gt_levels)
    if re.search(r"\bdef\s+impl\b", lean_code) and re.search(r"\bdef\s+spec\b", lean_code):
        score += 0.10
    if re.search(r"(\u2200|forall)\s+\w+", lean_code):
        score += 0.10
    return round(score, 3)


def score_solution_phi_prime(
    lean_code: str | None,
    compiles: bool,
    probe: dict | None,
    bug_num: int,
    ground_truth: dict,
) -> tuple[float, dict]:
    """Hardened Phi' — one component per reviewer-identified exploit.

      +0.10  compiles (expected to be run post-`lake clean && lake build`)
      +0.25  theorem count, USAGE-BASED — only theorems whose elaborated type
             references `AutoResearch.impl` or `AutoResearch.spec` (AST check)
      +0.20  sorry-free (source)
      +0.10  structural fidelity — impl AND spec each appear in ≥1 theorem
             type (AST check, not just `def impl` / `def spec`)
      +0.10  proof depth — non-vacuous `Expr.forallE` in ≥1 theorem type;
             quantifiers over Unit / PUnit / True do NOT count
      +0.25  theme coverage — keywords in theorem-body text only, with theorem
             names stripped (so e.g. `bug_exists` no longer gifts L1)

    Returns (score, breakdown).
    """
    breakdown = {
        "compiles": 0.0,
        "theorem_count": 0.0,
        "sorry_free": 0.0,
        "structural_fidelity": 0.0,
        "proof_depth": 0.0,
        "theme_coverage": 0.0,
    }
    if lean_code is None:
        return 0.0, breakdown

    if compiles:
        breakdown["compiles"] = 0.10
    if "sorry" not in lean_code:
        breakdown["sorry_free"] = 0.20

    if probe is not None:
        thms = probe.get("theorems", [])
        usage_count = sum(1 for t in thms if t["refs_impl"] or t["refs_spec"])
        breakdown["theorem_count"] = round(min(usage_count * 0.05, 0.25), 3)
        if any(t["refs_impl"] for t in thms) and any(t["refs_spec"] for t in thms):
            breakdown["structural_fidelity"] = 0.10
        if any(t["nonvacuous_forall"] for t in thms):
            breakdown["proof_depth"] = 0.10

    gt = ground_truth.get(str(bug_num), {})
    gt_levels = set(gt.get("levels", []))
    if gt_levels:
        blocks = extract_theorem_source_blocks(lean_code)
        detected = detect_theme_in_theorem_blocks(blocks)
        coverage = len(detected & gt_levels) / len(gt_levels)
        breakdown["theme_coverage"] = round(0.25 * coverage, 3)

    total = sum(breakdown.values())
    return round(total, 3), breakdown


def score_solution(
    lean_code: str | None,
    compiles: bool,
    bug_num: int,
    ground_truth: dict,
    probe: dict | None = None,
    scoring: str = "phi_prime",
) -> float:
    """Dispatch: `phi_prime` (default) or `legacy`."""
    if scoring == "legacy":
        return score_solution_legacy(lean_code, compiles, bug_num, ground_truth)
    score, _ = score_solution_phi_prime(
        lean_code, compiles, probe, bug_num, ground_truth
    )
    return score


# ---------------------------------------------------------------------------
# Bug description loading
# ---------------------------------------------------------------------------

def load_bug_description(bug_num: int) -> str:
    """Load the minimal bug description from bugs/."""
    # Handle both single-digit (01_...) and two-digit (10_...) numbering
    pattern = f"{bug_num:02d}_*.md"
    files = list(BUGS_DIR.glob(pattern))
    if not files:
        raise FileNotFoundError(f"No bug description found for bug {bug_num}")
    return files[0].read_text()


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

def build_user_prompt(
    bug_num: int,
    bug_desc: str,
    asm_context: str,
    iteration: int,
    total_iterations: int,
    history: list[dict],
    feedback_template: str,
    helpers,
) -> str:
    """Build the user prompt for one formalizer iteration.

    - Iteration 0: bug description + assembly + fresh task
    - Iteration 1+: previous code + compilation result + feedback
    """
    parts: list[str] = []

    parts.append(f"## Bug #{bug_num}: {BUG_NAMES[bug_num]}\n")
    parts.append(bug_desc)

    if asm_context:
        parts.append("\n## Relevant Assembly Code\n")
        parts.append(asm_context)

    if iteration == 0:
        parts.append(f"\n## Task (Iteration {iteration + 1}/{total_iterations})\n")
        parts.append(
            "Write a Lean 4 file that formally verifies this bug. "
            "Your file should:\n"
            "- Import SM83 (and optionally Harness)\n"
            "- Use the `AutoResearch` namespace\n"
            "- Model the buggy behavior as `impl`\n"
            "- Model the correct behavior as `spec`\n"
            "- Prove properties at increasing difficulty levels (L1-L4)\n"
            "- Compile cleanly with `lake build`\n\n"
            "Output your complete Solution.lean inside a ```lean code block."
        )
    else:
        prev = history[-1] if history else None
        parts.append(f"\n## Task (Iteration {iteration + 1}/{total_iterations})\n")

        if prev and not prev.get("compiles", False):
            parts.append("Your previous attempt failed to compile.\n")
            parts.append("### Previous Code\n```lean\n")
            parts.append(prev.get("code", ""))
            parts.append("\n```\n")

            # Format errors using feedback template
            build_output = prev.get("build_output", "")
            parsed = helpers.parse_lean_errors(build_output)

            # Use simple replacement to avoid issues with curly braces in Lean errors
            feedback = feedback_template
            feedback = feedback.replace(
                "{errors}",
                build_output[-2000:] if len(build_output) > 2000 else build_output,
            )
            feedback = feedback.replace("{parsed_issues}", parsed)
            feedback = feedback.replace("{iteration}", str(iteration + 1))
            feedback = feedback.replace("{total}", str(total_iterations))
            parts.append(feedback)

        elif prev and prev.get("compiles", False):
            parts.append(
                "Your previous attempt compiled successfully! "
                f"Score: {prev.get('score', 0):.3f}, "
                f"Theorems: {prev.get('theorems', 0)}.\n"
            )
            parts.append("### Previous Code\n```lean\n")
            parts.append(prev.get("code", ""))
            parts.append("\n```\n")
            parts.append(
                "Try to improve by:\n"
                "- Adding more theorems at higher difficulty levels (L2, L3, L4)\n"
                "- Removing any `sorry` placeholders with real proofs\n"
                "- Keeping compilation clean\n"
            )

        parts.append(
            "\nOutput your complete, improved Solution.lean inside a ```lean code block."
        )

    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Inner loop
# ---------------------------------------------------------------------------

async def run_inner_loop(
    model: str | None = None,
    output_dir: Path | None = None,
    include_asm: bool = True,
    scoring: str = "phi_prime",
) -> dict:
    """Run the inner formalization loop across all 5 bugs.

    `scoring="phi_prime"` (default) runs the hardened scorer: augments each
    Solution.lean with a Lean probe, tracks iteration-best by Phi', and
    confirms the best via `lake clean && lake build`.  `scoring="legacy"`
    restores the original source-regex scorer (for ablation).

    Returns a dict with aggregate score, per-bug results, and metadata.
    """
    # Load pipeline configuration
    config = load_config()
    system_prompt = load_system_prompt()
    feedback_template = load_feedback_template()
    helpers = import_pipeline_module("helpers")
    iteration_logic = import_pipeline_module("iteration_logic")

    K = config.get("iterations_per_bug", 5)
    build_timeout = config.get("build_timeout", 300)
    effective_model = model or config.get("model", "claude-sonnet-4-6")
    use_phi_prime = scoring == "phi_prime"

    # Load ground truth for scoring (NOT shared with formalizer)
    ground_truth: dict = {}
    if GROUND_TRUTH_FILE.exists():
        with open(GROUND_TRUTH_FILE) as f:
            ground_truth = json.load(f)

    # Create run directory
    if output_dir is None:
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        output_dir = SCRIPT_DIR / "runs" / timestamp
    output_dir.mkdir(parents=True, exist_ok=True)

    log(f"\n{'=' * 60}")
    log(f"  INNER LOOP: model={effective_model}, K={K}, include_asm={include_asm}")
    log(f"  Scoring:  {'Φ′ (hardened, probe + clean rebuild)' if use_phi_prime else 'Φ (legacy, source regex)'}")
    log(f"  Output:   {output_dir}")
    log(f"{'=' * 60}")

    t_start = time.time()
    per_bug_results: dict[int, dict] = {}

    for bug_num in range(1, 11):
        bug_name = BUG_NAMES[bug_num]
        log(f"\n{'=' * 60}")
        log(f"  BUG {bug_num}: {bug_name}")
        log(f"{'=' * 60}")

        bug_desc = load_bug_description(bug_num)
        asm_context = helpers.extract_relevant_asm(bug_num, POKERED_PATH) if include_asm else ""

        # Create workspace (reused across iterations for build caching)
        workspace = create_workspace(output_dir, bug_num)

        # Pre-build SM83 infrastructure on the first bug
        log("  Building SM83 infrastructure...")
        t0 = time.time()
        success, build_out = run_lake_build(workspace, timeout=build_timeout)
        infra_time = time.time() - t0
        if success:
            log(f"  Infrastructure ready ({infra_time:.1f}s)")
        else:
            # The initial Solution.lean has `sorry` so build may "fail"
            # but SM83/Harness should still be compiled and cached
            if "Solution" in build_out:
                log(f"  Infrastructure built, Solution placeholder failed (expected) ({infra_time:.1f}s)")
            else:
                log(f"  WARNING: Infrastructure build issues ({infra_time:.1f}s)")

        best_code: str | None = None
        best_score: float = 0.0
        best_compiles: bool = False
        conversation_history: list[dict] = []

        for k in range(K):
            log(f"\n  --- Iteration {k + 1}/{K} ---")

            # Check iteration logic for restart
            if k > 0 and iteration_logic.should_restart(
                iteration=k,
                last_compiled=best_compiles,
                history=conversation_history,
            ):
                log("  Restarting conversation (iteration logic)")
                conversation_history = []

            # Build user prompt
            user_prompt = build_user_prompt(
                bug_num=bug_num,
                bug_desc=bug_desc,
                asm_context=asm_context,
                iteration=k,
                total_iterations=K,
                history=conversation_history,
                feedback_template=feedback_template,
                helpers=helpers,
            )

            # Information barrier check
            check_information_barrier(user_prompt)

            # Call LLM
            log(f"  Calling {effective_model}...")
            t0 = time.time()
            try:
                response_text, reasoning = await _call_llm(
                    system_prompt, user_prompt, effective_model
                )
            except Exception as e:
                log(f"  LLM call failed: {e}")
                conversation_history.append(
                    {"iteration": k, "error": str(e)}
                )
                continue
            gen_time = time.time() - t0
            log(f"  Generated in {gen_time:.1f}s")

            # Extract Lean code
            lean_code = extract_lean_code(response_text)
            if lean_code is None:
                log("  Could not extract Lean code from response")
                conversation_history.append({
                    "iteration": k,
                    "response": response_text[:500],
                    "error": "no_code_extracted",
                })
                continue

            # Write (augmented with probe, for Phi') and compile
            to_write = augment_with_probe(lean_code) if use_phi_prime else lean_code
            write_solution(workspace, to_write)
            log("  Compiling...")
            t0 = time.time()
            compiles, build_output = run_lake_build(workspace, timeout=build_timeout)
            build_time = time.time() - t0
            log(f"  Build: {'OK' if compiles else 'FAIL'} ({build_time:.1f}s)")

            if not compiles:
                parsed_errors = helpers.parse_lean_errors(build_output)
                log(f"  Errors: {parsed_errors[:200]}")

            # Score this attempt (probe parsed when compile succeeds)
            probe = parse_probe_output(build_output) if (use_phi_prime and compiles) else None
            if use_phi_prime:
                attempt_score, attempt_breakdown = score_solution_phi_prime(
                    lean_code, compiles, probe, bug_num, ground_truth
                )
                log(f"  Score(Φ′): {attempt_score:.3f}  breakdown={attempt_breakdown}")
            else:
                attempt_score = score_solution_legacy(
                    lean_code, compiles, bug_num, ground_truth
                )
                log(f"  Score(Φ): {attempt_score:.3f} (best so far: {best_score:.3f})")

            if attempt_score > best_score:
                best_score = attempt_score
                best_code = lean_code
                best_compiles = compiles

            # Record in history for feedback (store ORIGINAL code, not augmented)
            conversation_history.append({
                "iteration": k,
                "code": lean_code,
                "compiles": compiles,
                "build_output": build_output if not compiles else "",
                "score": attempt_score,
                "theorems": count_theorems(lean_code),
            })

        # Final Phi' verification: clean rebuild + probe on the iteration-best.
        # Defeats any olean-cache luck and grounds the reported score in an
        # artifact that builds from scratch.
        final_score = best_score
        final_breakdown: dict = {}
        final_probe: dict | None = None
        final_compiles_clean = best_compiles
        if use_phi_prime and best_code is not None:
            log("\n  Final clean rebuild + probe on iteration-best...")
            write_solution(workspace, augment_with_probe(best_code))
            t0 = time.time()
            final_compiles_clean, clean_output = run_clean_build(
                workspace, timeout=build_timeout * 2
            )
            log(
                f"  Clean rebuild: {'OK' if final_compiles_clean else 'FAIL'} "
                f"({time.time() - t0:.1f}s)"
            )
            final_probe = parse_probe_output(clean_output) if final_compiles_clean else None
            final_score, final_breakdown = score_solution_phi_prime(
                best_code, final_compiles_clean, final_probe, bug_num, ground_truth
            )
            log(f"  Final Φ′: {final_score:.3f}  breakdown={final_breakdown}")

        # Save best solution for this bug (original, not augmented).
        if best_code is not None:
            solutions_dir = output_dir / "solutions"
            solutions_dir.mkdir(exist_ok=True)
            (solutions_dir / f"bug{bug_num}_{bug_name}.lean").write_text(best_code)

        per_bug_results[bug_num] = {
            "bug_name": bug_name,
            "score": final_score,
            "score_iter_best": best_score,
            "compiles_clean": final_compiles_clean,
            "compiles_iter": best_compiles,
            "breakdown": final_breakdown,
            "probe_theorem_count": (
                len(final_probe["theorems"]) if final_probe else 0
            ),
            "theorems": count_theorems(best_code) if best_code else 0,
            "sorry_free": ("sorry" not in best_code) if best_code else False,
            "iterations_used": len(
                [h for h in conversation_history if "code" in h]
            ),
        }

        log(
            f"\n  Bug {bug_num} final: score={final_score:.3f} "
            f"compiles_clean={final_compiles_clean} "
            f"theorems={per_bug_results[bug_num]['theorems']}"
        )

    # Aggregate score
    wall_time = time.time() - t_start
    aggregate_score = sum(r["score"] for r in per_bug_results.values())

    result = {
        "score": round(aggregate_score, 3),
        "scoring": "phi_prime" if use_phi_prime else "legacy",
        "per_bug": {str(k): v for k, v in per_bug_results.items()},
        "model": effective_model,
        "iterations_per_bug": K,
        "include_asm": include_asm,
        "wall_time_s": round(wall_time, 1),
    }

    # Save results
    (output_dir / "results.json").write_text(json.dumps(result, indent=2))

    # Print machine-readable output to stdout
    print("\n=== INNER LOOP COMPLETE ===")
    print(json.dumps(result, indent=2))

    return result


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args():
    parser = argparse.ArgumentParser(
        description="Run inner formalization loop with pipeline configuration"
    )
    parser.add_argument(
        "--model",
        default=None,
        help="Model override (default: from pipeline/config.yaml)",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Directory to save results",
    )
    parser.add_argument(
        "--no-asm",
        action="store_true",
        default=False,
        help="Exclude assembly context from formalizer prompt (ablation mode)",
    )
    parser.add_argument(
        "--scoring",
        choices=["phi_prime", "legacy"],
        default="phi_prime",
        help="phi_prime (default): hardened Phi' with probe + clean rebuild. "
             "legacy: original source-regex Phi (for ablation comparison).",
    )
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    output_dir = Path(args.output_dir) if args.output_dir else None
    asyncio.run(run_inner_loop(
        model=args.model,
        output_dir=output_dir,
        include_asm=not args.no_asm,
        scoring=args.scoring,
    ))
