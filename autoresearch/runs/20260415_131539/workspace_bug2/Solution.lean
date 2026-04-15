import SM83

namespace AutoResearch

/-!
# Bug: 1/256 Miss Chance (The "one_in_256" Bug)

In Pokémon Red, Blue, and Yellow, moves with 100% accuracy and critical hit checks
with maximum probability are capped at a threshold of 255. 

The CPU uses the `cp` (compare) instruction to compare a random byte `A` with 
this threshold `B`. The `cp` instruction sets the Carry Flag if and only if `A < B`.
The code then branches based on the Carry Flag:
- If `Carry` is set (`A < B`): Success (Hit/Crit).
- If `Carry` is clear (`A >= B`): Failure (Miss/No Crit).

Because the random number generator produces values in the range [0, 255], 
and the maximum threshold is 255, the case where the RNG produces 255 results 
in `255 < 255` being false. Thus, the Carry Flag is not set, and a 100% 
guaranteed event fails with a probability of 1/256.
-/

/-- 
Models the comparison logic found in both `MoveHitTest` and `CriticalHitTest`.
The assembly sequence is:
