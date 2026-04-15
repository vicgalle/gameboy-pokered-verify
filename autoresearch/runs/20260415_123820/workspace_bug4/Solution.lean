import SM83

namespace AutoResearch

/-!
# Bug #4: heal_overflow (Pokémon Red/Blue)

In Pokémon Red and Blue, the check for whether a Pokémon is already at full HP
before using a healing move (Recover, Softboiled, or Rest) is flawed.

The engine uses a 16-bit comparison across two 8-bit operations. However, it
performs an `SBC` (subtract with carry) on the low byte using the carry from
the high byte comparison, but then only checks the Zero flag of that *second*
subtraction.

This means that if the current HP is lower than the Max HP, but the difference
between them is exactly 255 (or 511, etc.), the `SBC` operation results in zero
and sets the Zero flag, causing the move to fail.

## Assembly Reference (engine/battle/move_effects/heal.asm)

