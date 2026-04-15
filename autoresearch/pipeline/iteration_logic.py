"""
Pipeline configuration -- iteration logic.

Controls the multi-turn strategy for the formalizer:
- When to restart the conversation vs continue iterating
- How to handle repeated failures

The researcher can modify this to experiment with different strategies.
"""


def should_restart(
    iteration: int,
    last_compiled: bool,
    history: list[dict],
) -> bool:
    """Decide whether to restart the conversation from scratch.

    Returns True to discard conversation history and start fresh.
    Returns False to continue with accumulated context (previous code + errors).

    Args:
        iteration: Current iteration index (0-based).
        last_compiled: Whether the best attempt so far compiles.
        history: List of dicts with keys: iteration, code, compiles, build_output, score.
    """
    if not history:
        return False

    # Count consecutive compilation failures
    consecutive_failures = 0
    for entry in reversed(history):
        if not entry.get("compiles", False):
            consecutive_failures += 1
        else:
            break

    # Restart after 3 consecutive compilation failures
    if consecutive_failures >= 3:
        return True

    return False
