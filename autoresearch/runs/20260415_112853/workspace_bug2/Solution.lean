import SM83

namespace AutoResearch

/-!
# Bug #2: one_in_256 (The 1/256 Miss Chance)

## Gameplay Description
In Pokémon Red/Blue, moves that are intended to have 100% accuracy (like Swift or 
Normal-type moves with no accuracy/evasion modifiers) can still miss with a 
probability of 1 in 256. This also affects the critical hit system, where 
even the maximum possible crit rate still fails to crit 1/256th of the time.

## Technical Root Cause
The bug stems from the use of the `cp` (compare) instruction followed by `nc` (no carry) 
conditional returns or jumps.

In the SM83 CPU:
1. `cp b` calculates `A - B` and sets the Carry flag (C) if a borrow is required.
   Specifically, C is set if `A < B` (unsigned).
2. `ret nc` (Return if No Carry) exits the subroutine if `C = 0`, which means `A >= B`.

For hit/crit tests:
- The game generates a random byte `A` (0-255).
- It compares it to a threshold `B` (accuracy or crit rate).
- If `A < B`, the move hits/crits.
- If `A >= B`, it fails.

When the game intends for a 100% success rate, it uses the maximum 8-bit value, 255.
However, if the random byte `A` also happens to be 255, the comparison `255 < 255` 
is false. Thus, the Carry flag is NOT set, the `nc` condition is met, and the 
game returns a failure.

## Relevant Assembly
From `CriticalHitTest`:
