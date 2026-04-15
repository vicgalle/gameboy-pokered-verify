import SM83

namespace AutoResearch

/-!
# Bug #4: heal_overflow

## Description
In Pokémon Red/Blue, the healing moves `Recover`, `Softboiled`, and `Rest` check if 
the user's HP is already at its maximum before proceeding. Due to a bug in the 
16-bit comparison logic within `HealEffect_`, the game incorrectly determines 
that the Pokémon is at full HP when the difference between the maximum HP and 
current HP is exactly 255, 511, or any value where `(maxHP - currHP) % 256 == 255` 
(provided `currHP < maxHP`).

## Assembly Analysis
The buggy code snippet from `engine/battle/move_effects/heal.asm`:
