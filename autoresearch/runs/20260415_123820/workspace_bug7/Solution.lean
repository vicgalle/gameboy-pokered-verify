import SM83

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Description
In Pokémon Red/Blue, the move Bide stores damage taken over 2-3 turns and then
deals double that amount back. This value is stored as a 16-bit big-endian
integer in WRAM (`wPlayerBideAccumulatedDamage`).

When a Pokémon faints, the game should reset this counter to zero. However, the
routine `FaintEnemyPokemon` (called when the player's opponent faints) only
clears the high byte of the 16-bit counter. Its counterpart,
`RemoveFaintedPlayerMon` (called when the player's own Pokémon faints),
correctly clears both bytes.

In a link battle, when a Pokémon faints, one Game Boy (the one whose Pokémon
fainted) executes the correct clear, while the other Game Boy (the one who
defeated the Pokémon) executes the incomplete clear. This results in the
Bide damage counter desynchronizing between the two consoles if the
accumulated damage was not a multiple of 256.

## Formalization
We model the 16-bit accumulated damage and the two competing faint routines.
-/

namespace AutoResearch

open BitVec

/--
  Model of the buggy routine `FaintEnemyPokemon`.
  The assembly code is:
  