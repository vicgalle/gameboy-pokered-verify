import SM83

namespace AutoResearch

/-!
# Bug #4: Heal Overflow (HealEffect_ Bug)

## Description
In Pokémon Red/Blue, healing moves like Recover, Softboiled, and Rest are 
supposed to fail if the Pokémon is already at full HP. However, a bug in the 
comparison logic causes the game to incorrectly determine that the Pokémon is 
at full HP when the difference between its current HP and maximum HP is exactly 
255, 511, or other specific values.

## Assembly Analysis
The buggy routine in `engine/battle/move_effects/heal.asm` compares the 16-bit 
HP values (High byte then Low byte) incorrectly:

