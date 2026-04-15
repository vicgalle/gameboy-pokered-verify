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
    """Run ``lake build`` in the workspace and return (success, output)."""
    try:
        result = subprocess.run(
            ["lake", "build"],
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        success = result.returncode == 0
        output = result.stderr if not success else result.stdout
        return success, output
    except subprocess.TimeoutExpired:
        return False, f"TIMEOUT: lake build exceeded {timeout}s"
    except FileNotFoundError:
        return False, "ERROR: lake not found in PATH"


# ---------------------------------------------------------------------------
# Scoring function Phi(c)
# ---------------------------------------------------------------------------

def count_theorems(lean_code: str) -> int:
    """Count theorem and lemma declarations in Lean code."""
    return len(
        re.findall(r"(?:^|\n)\s*(?:private\s+)?(?:theorem|lemma)\s+\w+", lean_code)
    )


def detect_theme_coverage(lean_code: str) -> set[str]:
    """Detect which proof levels are achieved based on keyword matching.

    Uses the same categories as ground_truth.json for consistent scoring.
    """
    levels: set[str] = set()
    lower = lean_code.lower()

    # L1: existential witness
    if any(kw in lower for kw in ["bug_exists", "witness", "\u2203", "exists"]):
        levels.add("L1")

    # L2: universal characterization
    if any(kw in lower for kw in ["always", "iff", "characteriz", "\u2194", "forall", "\u2200"]):
        levels.add("L2")

    # L3: fix correctness
    if any(kw in lower for kw in ["fix", "correct"]):
        levels.add("L3")

    # L4: relational / desync / link battle
    if any(kw in lower for kw in ["desync", "player", "enemy", "diverge", "link", "bide"]):
        levels.add("L4")

    return levels


def score_solution(
    lean_code: str | None,
    compiles: bool,
    bug_num: int,
    ground_truth: dict,
) -> float:
    """Score a single bug's formalization on [0.0, 1.0].

    Scoring:
      +0.2  if the Lean file compiles
      +0.1  per theorem (up to +0.3 for 3+ theorems)
      +0.3  if completely sorry-free
      +0.2  scaled by ground truth theme coverage
    """
    if lean_code is None:
        return 0.0

    score = 0.0

    # +0.2 if compiles
    if compiles:
        score += 0.2

    # +0.1 per theorem (up to +0.3 for 3+ theorems)
    thm_count = count_theorems(lean_code)
    score += min(thm_count * 0.1, 0.3)

    # +0.3 if completely sorry-free
    if "sorry" not in lean_code:
        score += 0.3

    # +0.2 scaled by theme coverage vs ground truth
    gt = ground_truth.get(str(bug_num), {})
    gt_levels = set(gt.get("levels", []))
    detected_levels = detect_theme_coverage(lean_code)
    if gt_levels:
        coverage = len(detected_levels & gt_levels) / len(gt_levels)
        score += 0.2 * coverage

    return round(score, 3)


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
) -> dict:
    """Run the inner formalization loop across all 5 bugs.

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
    log(f"  INNER LOOP: model={effective_model}, K={K}")
    log(f"  Output: {output_dir}")
    log(f"{'=' * 60}")

    t_start = time.time()
    per_bug_results: dict[int, dict] = {}

    for bug_num in range(1, 11):
        bug_name = BUG_NAMES[bug_num]
        log(f"\n{'=' * 60}")
        log(f"  BUG {bug_num}: {bug_name}")
        log(f"{'=' * 60}")

        bug_desc = load_bug_description(bug_num)
        asm_context = helpers.extract_relevant_asm(bug_num, POKERED_PATH)

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

            # Write and compile
            write_solution(workspace, lean_code)
            log("  Compiling...")
            t0 = time.time()
            compiles, build_output = run_lake_build(workspace, timeout=build_timeout)
            build_time = time.time() - t0
            log(f"  Build: {'OK' if compiles else 'FAIL'} ({build_time:.1f}s)")

            if not compiles:
                parsed_errors = helpers.parse_lean_errors(build_output)
                log(f"  Errors: {parsed_errors[:200]}")

            # Score this attempt
            attempt_score = score_solution(
                lean_code, compiles, bug_num, ground_truth
            )
            log(f"  Score: {attempt_score:.3f} (best so far: {best_score:.3f})")

            if attempt_score > best_score:
                best_score = attempt_score
                best_code = lean_code
                best_compiles = compiles

            # Record in history for feedback
            conversation_history.append({
                "iteration": k,
                "code": lean_code,
                "compiles": compiles,
                "build_output": build_output if not compiles else "",
                "score": attempt_score,
                "theorems": count_theorems(lean_code),
            })

        # Save best solution for this bug
        if best_code is not None:
            solutions_dir = output_dir / "solutions"
            solutions_dir.mkdir(exist_ok=True)
            (solutions_dir / f"bug{bug_num}_{bug_name}.lean").write_text(best_code)

        per_bug_results[bug_num] = {
            "bug_name": bug_name,
            "score": best_score,
            "compiles": best_compiles,
            "theorems": count_theorems(best_code) if best_code else 0,
            "sorry_free": ("sorry" not in best_code) if best_code else False,
            "iterations_used": len(
                [h for h in conversation_history if "code" in h]
            ),
        }

        log(
            f"\n  Bug {bug_num} final: score={best_score:.3f} "
            f"compiles={best_compiles} "
            f"theorems={per_bug_results[bug_num]['theorems']}"
        )

    # Aggregate score
    wall_time = time.time() - t_start
    aggregate_score = sum(r["score"] for r in per_bug_results.values())

    result = {
        "score": round(aggregate_score, 3),
        "per_bug": {str(k): v for k, v in per_bug_results.items()},
        "model": effective_model,
        "iterations_per_bug": K,
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
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    output_dir = Path(args.output_dir) if args.output_dir else None
    asyncio.run(run_inner_loop(model=args.model, output_dir=output_dir))
