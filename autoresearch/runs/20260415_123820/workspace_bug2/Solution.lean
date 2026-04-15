import SM83

namespace AutoResearch

/-!
# Bug #2: one_in_256 - 1/256 Miss Chance on 100% Accuracy Moves

In Pokémon Red and Blue, moves intended to have 100% accuracy (like most moves at full
accuracy) or 100% critical hit rates still fail with a 1/256 probability.

## Root Cause
The SM83 `cp b` instruction sets the Carry Flag if `A < B`. The battle engine
interprets a set Carry Flag as a "success" (hit or critical hit). If the threshold
`B` is at its maximum value of 255 (0xFF), and the random roll `A` is also 255,
the comparison `255 < 255` is false (no carry). Consequently, the "guaranteed"
event fails.

## Assembly Evidence
1. `MoveHitTest`: Eventually calls `calcHitChance` (not shown but follows this pattern).
2. `CriticalHitTest`:
   