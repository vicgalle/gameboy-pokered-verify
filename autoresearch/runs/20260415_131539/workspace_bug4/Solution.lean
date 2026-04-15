import SM83

namespace AutoResearch

/-!
# Bug: heal_overflow

## Description
In Pokémon Red/Blue, healing moves like Recover, Softboiled, and Rest perform a
16-bit comparison to check if the Pokémon's current HP is already at its maximum.
However, the assembly implementation incorrectly propagates a carry flag from a
high-byte comparison into a low-byte subtraction. This causes the move to
incorrectly fail (reporting "Already at full HP") when the gap between current
and maximum HP is specific values, such as 255 or 511.

## Assembly Analysis
The buggy code in `HealEffect_` (engine/battle/move_effects/heal.asm):
