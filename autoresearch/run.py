"""
run.py — Inner loop orchestrator for the autoresearch bug formalization pipeline.

DO NOT MODIFY. This file is read-only for the researcher agent.

Orchestrates:
  1. Loads pipeline configuration from pipeline/
  2. For each of 5 bugs: invokes Claude API as formalizer for K iterations
  3. Evaluates all generated Lean files using prepare.py
  4. Prints scores in a grep-able format

Usage:
  python3 run.py > run.log 2>&1
  grep "^SCORE:" run.log
"""

import os
import sys
import json
import time
import uuid
import importlib.util
from pathlib import Path

import yaml
import anthropic

import prepare

# ──────────────────────────────────────────────────────────────────────
# Constants
# ──────────────────────────────────────────────────────────────────────

AUTORESEARCH_DIR = Path(__file__).parent.resolve()
PIPELINE_DIR = AUTORESEARCH_DIR / "pipeline"
BUGS_DIR = AUTORESEARCH_DIR / "bugs"
WORKSPACE_DIR = AUTORESEARCH_DIR / "workspace"
POKERED_DIR = Path("/Users/victorgallego/pokered")

TOTAL_TIMEOUT = 1800  # 30 minutes max for full run

# Paths that must NEVER appear in messages to the formalizer
FORBIDDEN_PATHS = [
    AUTORESEARCH_DIR / "ground_truth",
    AUTORESEARCH_DIR.parent / "PokeredBugs",
    AUTORESEARCH_DIR.parent / "Harness",
    AUTORESEARCH_DIR.parent / "README.md",
]

# Maps bug name -> list of relevant assembly files in pokered
BUG_ASM_FILES = {
    "focus_energy": [
        "engine/battle/core.asm",
    ],
    "one_in_256": [
        "engine/battle/core.asm",
    ],
    "blaine_ai": [
        "engine/battle/trainer_ai.asm",
    ],
    "heal_overflow": [
        "engine/battle/move_effects/heal.asm",
    ],
    "psywave_desync": [
        "engine/battle/core.asm",
    ],
}

# Line ranges to extract from assembly files (approximate, generous)
BUG_ASM_RANGES = {
    "focus_energy": {"engine/battle/core.asm": (4470, 4550)},
    "one_in_256": {"engine/battle/core.asm": (5310, 5340)},
    "blaine_ai": {"engine/battle/trainer_ai.asm": (370, 400)},
    "heal_overflow": {"engine/battle/move_effects/heal.asm": (1, 100)},
    "psywave_desync": {"engine/battle/core.asm": (4650, 4800)},
}


# ──────────────────────────────────────────────────────────────────────
# Information isolation enforcement
# ──────────────────────────────────────────────────────────────────────

def check_no_forbidden_content(text: str) -> bool:
    """Verify that no forbidden file content appears in the text."""
    for fpath in FORBIDDEN_PATHS:
        if fpath.is_file():
            content = fpath.read_text()
            # Check for any 80+ char substring match
            for i in range(0, len(content) - 80):
                chunk = content[i:i+80]
                if chunk in text:
                    print(f"ISOLATION VIOLATION: content from {fpath} found in message",
                          file=sys.stderr)
                    return False
        elif fpath.is_dir():
            for f in fpath.rglob("*.lean"):
                content = f.read_text()
                for i in range(0, max(0, len(content) - 80)):
                    chunk = content[i:i+80]
                    if chunk in text:
                        print(f"ISOLATION VIOLATION: content from {f} found in message",
                              file=sys.stderr)
                        return False
    return True


# ──────────────────────────────────────────────────────────────────────
# Assembly extraction
# ──────────────────────────────────────────────────────────────────────

def extract_assembly(bug_name: str, config: dict) -> str:
    """Extract relevant assembly code from the pokered codebase."""
    max_lines = config.get("max_asm_lines", 200)
    asm_ranges = BUG_ASM_RANGES.get(bug_name, {})
    parts = []

    for rel_path, (start, end) in asm_ranges.items():
        full_path = POKERED_DIR / rel_path
        if not full_path.exists():
            parts.append(f"; File not found: {rel_path}")
            continue

        lines = full_path.read_text().split('\n')
        # Clamp to file length
        start = max(1, start)
        end = min(len(lines), end)
        excerpt = lines[start-1:end]

        if len(excerpt) > max_lines:
            excerpt = excerpt[:max_lines]

        parts.append(f"; === {rel_path} (lines {start}-{start+len(excerpt)-1}) ===")
        for i, line in enumerate(excerpt, start=start):
            parts.append(f"{i:5d}  {line}")

    return '\n'.join(parts)


# ──────────────────────────────────────────────────────────────────────
# Pipeline loading
# ──────────────────────────────────────────────────────────────────────

def load_config() -> dict:
    """Load pipeline/config.yaml."""
    config_path = PIPELINE_DIR / "config.yaml"
    with open(config_path) as f:
        return yaml.safe_load(f)


def load_system_prompt() -> str:
    """Load pipeline/system_prompt.md."""
    return (PIPELINE_DIR / "system_prompt.md").read_text()


def load_feedback_template() -> str:
    """Load pipeline/feedback_template.md."""
    return (PIPELINE_DIR / "feedback_template.md").read_text()


def load_helpers():
    """Dynamically import pipeline/helpers.py."""
    spec = importlib.util.spec_from_file_location(
        "pipeline_helpers", PIPELINE_DIR / "helpers.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def load_iteration_logic():
    """Dynamically import pipeline/iteration_logic.py."""
    spec = importlib.util.spec_from_file_location(
        "pipeline_iteration", PIPELINE_DIR / "iteration_logic.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ──────────────────────────────────────────────────────────────────────
# Lean compilation (used during inner loop for feedback)
# ──────────────────────────────────────────────────────────────────────

def try_compile(eval_dir: Path, bug_name: str, lean_content: str) -> dict:
    """Try to compile a Lean file, return build result."""
    return prepare.build_lean_file(eval_dir, bug_name, lean_content)


# ──────────────────────────────────────────────────────────────────────
# Inner loop: formalizer invocation
# ──────────────────────────────────────────────────────────────────────

def extract_lean_code(response_text: str) -> str:
    """Extract Lean code from a Claude response (may be in a code block)."""
    # Try to find ```lean ... ``` block
    lean_blocks = []
    in_block = False
    current_block = []

    for line in response_text.split('\n'):
        if line.strip().startswith('```lean'):
            in_block = True
            current_block = []
        elif line.strip() == '```' and in_block:
            in_block = False
            lean_blocks.append('\n'.join(current_block))
        elif in_block:
            current_block.append(line)

    if lean_blocks:
        return '\n'.join(lean_blocks)

    # Fallback: try ``` ... ``` without language tag
    in_block = False
    current_block = []
    for line in response_text.split('\n'):
        if line.strip().startswith('```') and not in_block:
            in_block = True
            current_block = []
        elif line.strip() == '```' and in_block:
            in_block = False
            lean_blocks.append('\n'.join(current_block))
        elif in_block:
            current_block.append(line)

    if lean_blocks:
        # Return the longest block (most likely the full file)
        return max(lean_blocks, key=len)

    # Last resort: return the entire response (it might be raw Lean code)
    return response_text


def format_feedback(template: str, build_result: dict, helpers_mod) -> str:
    """Format compilation feedback using the template."""
    error_output = build_result.get("error_output", "")

    # Use helpers to parse errors if available
    parsed_issues = ""
    if hasattr(helpers_mod, 'parse_lean_errors'):
        issues = helpers_mod.parse_lean_errors(error_output)
        if issues:
            parsed_issues = '\n'.join(f"- {issue}" for issue in issues)

    feedback = template.replace("{errors}", error_output[:2000])
    feedback = feedback.replace("{parsed_issues}", parsed_issues or "See raw errors above.")
    return feedback


def run_formalizer_for_bug(
    bug_name: str,
    config: dict,
    system_prompt: str,
    feedback_template: str,
    helpers_mod,
    iteration_mod,
    eval_dir: Path,
    workspace_bug_dir: Path,
    client: anthropic.Anthropic,
) -> str:
    """Run the inner loop for a single bug. Returns the best Lean code."""
    K = config.get("iterations_per_bug", 5)
    model = config.get("model", "claude-sonnet-4-6-20250514")
    max_tokens = config.get("max_tokens", 8192)
    temperature = config.get("temperature", 0.3)

    # Load bug description
    bug_desc_path = BUGS_DIR / f"{bug_name}.md"
    bug_desc = bug_desc_path.read_text()

    # Extract relevant assembly
    asm_context = extract_assembly(bug_name, config)

    # Generate initial scaffold if helpers provide one
    scaffold = ""
    if hasattr(helpers_mod, 'generate_lean_scaffold'):
        scaffold = helpers_mod.generate_lean_scaffold(bug_name)

    # Build the initial user message
    lean_name = prepare.BUG_TO_LEAN_NAME[bug_name]
    initial_message = f"""## Bug to Formalize: {bug_name}

{bug_desc}

## Relevant Assembly Code

{asm_context}

## Task

Produce a complete Lean 4 file that:
1. Models the buggy behavior (impl) and intended behavior (spec)
2. Proves the bug exists (at least one concrete witness)
3. Characterizes when the bug triggers
4. Optionally proves a fix is correct

The file should start with `import SM83` and use `namespace PokeredBugs`.
Use `BitVec 8` for 8-bit values. Key tactics: `native_decide` for exhaustive
8-bit proofs, `omega` for arithmetic, `simp` for simplification, `rfl` for
definitional equality.

Output a single complete Lean 4 file."""

    if scaffold:
        initial_message += f"\n\n## Starting scaffold\n\n```lean\n{scaffold}\n```"

    # Information isolation check
    full_prompt = system_prompt + initial_message
    assert check_no_forbidden_content(full_prompt), \
        "ISOLATION VIOLATION in initial prompt!"

    messages = [{"role": "user", "content": initial_message}]
    best_code = ""
    best_compiles = False
    best_theorems = 0

    for k in range(K):
        print(f"  [{bug_name}] Iteration {k+1}/{K}...", file=sys.stderr)

        # Check if we should restart (fresh conversation)
        if k > 0 and hasattr(iteration_mod, 'should_restart'):
            prev_errors = []  # could track errors across iterations
            if iteration_mod.should_restart(k, prev_errors):
                messages = [{"role": "user", "content": initial_message}]
                print(f"  [{bug_name}] Restarting conversation", file=sys.stderr)

        try:
            response = client.messages.create(
                model=model,
                max_tokens=max_tokens,
                temperature=temperature,
                system=system_prompt,
                messages=messages,
            )
            response_text = response.content[0].text
        except Exception as e:
            print(f"  [{bug_name}] API error at iteration {k+1}: {e}", file=sys.stderr)
            continue

        # Extract Lean code from response
        lean_code = extract_lean_code(response_text)

        # Save attempt
        attempt_path = workspace_bug_dir / f"attempt_{k+1}.lean"
        attempt_path.write_text(lean_code)

        # Try to compile
        build_result = try_compile(eval_dir, bug_name, lean_code)

        # Save build log
        log_path = workspace_bug_dir / f"build_log_{k+1}.txt"
        log_path.write_text(build_result.get("error_output", ""))

        # Track best result
        theorems = prepare.count_theorems(lean_code)
        num_sorry = prepare.count_sorry(lean_code)

        is_better = False
        if build_result["compiles"] and not best_compiles:
            is_better = True
        elif build_result["compiles"] == best_compiles:
            # Prefer more theorems, then fewer sorries
            effective = len(theorems) - num_sorry
            best_effective = best_theorems
            if effective > best_effective:
                is_better = True

        if is_better:
            best_code = lean_code
            best_compiles = build_result["compiles"]
            best_theorems = len(theorems) - num_sorry

        # If it compiles and is sorry-free, we're done with this bug
        if build_result["compiles"] and num_sorry == 0 and len(theorems) >= 3:
            print(f"  [{bug_name}] Success at iteration {k+1} "
                  f"({len(theorems)} theorems, sorry-free)", file=sys.stderr)
            break

        # Build feedback for next iteration
        if k < K - 1:
            feedback = format_feedback(feedback_template, build_result, helpers_mod)

            if build_result["compiles"]:
                status = f"Compiled successfully with {len(theorems)} theorems"
                if num_sorry > 0:
                    status += f" but {num_sorry} sorry remaining"
                feedback = f"## Status: {status}\n\n" + feedback
            else:
                feedback = f"## Status: Compilation FAILED\n\n" + feedback

            feedback += "\n\nPlease provide an updated complete Lean 4 file."

            # Add to conversation
            messages.append({"role": "assistant", "content": response_text})
            messages.append({"role": "user", "content": feedback})

            # Isolation check on feedback
            assert check_no_forbidden_content(feedback), \
                "ISOLATION VIOLATION in feedback!"

    # Save best result
    if best_code:
        (workspace_bug_dir / "final.lean").write_text(best_code)

    return best_code


# ──────────────────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────────────────

def main():
    start_time = time.time()
    run_id = str(uuid.uuid4())[:8]

    print(f"=== Autoresearch Inner Loop — Run {run_id} ===", file=sys.stderr)
    print(f"Start time: {time.strftime('%Y-%m-%d %H:%M:%S')}", file=sys.stderr)

    # Load pipeline configuration
    config = load_config()
    system_prompt = load_system_prompt()
    feedback_template = load_feedback_template()
    helpers_mod = load_helpers()
    iteration_mod = load_iteration_logic()

    print(f"Model: {config.get('model', 'claude-sonnet-4-6-20250514')}", file=sys.stderr)
    print(f"Iterations per bug: {config.get('iterations_per_bug', 5)}", file=sys.stderr)

    # Set up workspace
    workspace_run = WORKSPACE_DIR / run_id
    workspace_run.mkdir(parents=True, exist_ok=True)

    # Set up evaluation project (shared across bugs for efficiency)
    eval_dir = prepare.create_eval_project(run_id)

    # Initialize Claude API client
    client = anthropic.Anthropic()

    # Run formalizer for each bug
    generated_files = {}
    api_calls = 0

    for bug_name in prepare.BUGS:
        elapsed = time.time() - start_time
        if elapsed > TOTAL_TIMEOUT:
            print(f"TIMEOUT: {elapsed:.0f}s elapsed, skipping {bug_name}", file=sys.stderr)
            break

        print(f"\n--- Bug: {bug_name} ---", file=sys.stderr)
        bug_dir = workspace_run / bug_name
        bug_dir.mkdir(exist_ok=True)

        lean_code = run_formalizer_for_bug(
            bug_name=bug_name,
            config=config,
            system_prompt=system_prompt,
            feedback_template=feedback_template,
            helpers_mod=helpers_mod,
            iteration_mod=iteration_mod,
            eval_dir=eval_dir,
            workspace_bug_dir=bug_dir,
            client=client,
        )
        generated_files[bug_name] = lean_code

    # Clean up shared eval dir before final evaluation
    import shutil
    shutil.rmtree(eval_dir, ignore_errors=True)

    # Evaluate all results
    print(f"\n--- Evaluation ---", file=sys.stderr)
    results = prepare.evaluate_all(run_id, generated_files)

    total_time = time.time() - start_time

    # Print grep-able results
    print("---")
    print(f"SCORE:            {results['score']:.3f}")
    for bs in results["bug_scores"]:
        detail = (f"compiles={bs['compiles']}, theorems={bs['num_theorems']}, "
                  f"sorry={bs['num_sorry']}, coverage={bs['coverage']:.2f}")
        if bs.get("leak_detected"):
            detail += ", LEAK_DETECTED"
        print(f"{bs['bug']:20s} {bs['score']:.3f}  ({detail})")
    print(f"total_time_sec:   {total_time:.1f}")
    print(f"workspace:        {workspace_run}")

    # Save full results as JSON
    results["total_time_sec"] = round(total_time, 1)
    results_path = workspace_run / "scores.json"
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nFull results: {results_path}", file=sys.stderr)
    return results["score"]


if __name__ == "__main__":
    score = main()
    sys.exit(0 if score > 0 else 1)
