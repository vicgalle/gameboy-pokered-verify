import SM83

namespace AutoResearch

/-!
# Bug: heal_overflow

In Pokémon Red and Blue, healing moves like `Recover`, `Softboiled`, and `Rest`
contain a logic error in their "already at full HP" check. This check determines
whether the move should fail because the Pokémon's current HP is already equal
to its maximum HP.

### The Logic Error
The check is implemented using 16-bit big-endian values for HP. The code
compares the high bytes first using `cp`, then subtracts the low bytes using `sbc`
(subtract with carry). In the SM83 (Game Boy) CPU, `sbc` incorporates the carry 
flag set by the previous operation. 

Because the comparison is done high-to-low instead of low-to-high, the carry 
(acting as a borrow) from the high-byte comparison incorrectly modifies the 
low-byte comparison. This causes the move to "miss" (fail) if the gap between 
Max HP and Current HP is exactly 255, 511, or any value `256k - 1` where 
the carry bit from the high bytes cancels out the difference in the low bytes.

### Reference Assembly
