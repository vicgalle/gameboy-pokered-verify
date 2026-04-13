# Bug: Healing Moves Fail at Certain HP Gaps

## Gameplay Description

Recovery moves like Recover, Softboiled, and Rest are supposed to restore a
Pokemon's HP. However, under specific conditions, these moves incorrectly report
that the Pokemon is already at full HP and fail to heal, even though the Pokemon
has taken damage and genuinely needs healing.

This happens when the difference between the Pokemon's current HP and maximum HP
falls at certain specific values. The move's "are you already at full HP?" check
produces a false positive, blocking the heal.
