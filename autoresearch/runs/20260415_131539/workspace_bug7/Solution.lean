import SM83

namespace AutoResearch

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Description
Bide stores damage taken over 2-3 turns and then deals double that amount back. 
When a Pokémon faints, Bide's accumulated damage should be reset to zero to prevent 
leftover damage from affecting future moves.

In Pokémon Red/Blue, the routine `FaintEnemyPokemon` (called when the enemy faints) 
contains a coding error where it only clears the high byte of the player's 
16-bit Bide damage counter:
