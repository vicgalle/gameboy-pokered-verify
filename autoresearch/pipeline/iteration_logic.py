"""
pipeline/iteration_logic.py — Controls the multi-turn formalizer strategy.

The researcher CAN modify this file to improve:
  - When to restart from scratch vs continue iterating
  - How to structure the conversation across iterations
"""


def should_restart(attempt_num: int, prev_errors: list) -> bool:
    """Decide whether to restart the conversation from scratch.

    Args:
        attempt_num: Current iteration number (0-indexed, so 1 = second attempt)
        prev_errors: List of error strings from previous attempts

    Returns:
        True to restart with a fresh conversation, False to continue iterating.
    """
    # Default strategy: never restart, always iterate.
    # The formalizer benefits from seeing its previous attempts and the
    # specific Lean errors they produced.
    return False
