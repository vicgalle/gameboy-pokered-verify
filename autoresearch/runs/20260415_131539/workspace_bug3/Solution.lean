import SM83

namespace AutoResearch

/-!
# Bug #3: Blaine's AI Uses Super Potion Regardless of HP

## Description
In Pokémon Red/Blue, Blaine (the Cinnabar Island Gym Leader) has a custom AI 
routine to use Super Potions. Unlike other trainer AI routines (like the 
standard "Heal AI" used by Juggler or Lorelei), Blaine's routine only checks 
a random probability roll. It fails to call `AICheckIfHPBelowFraction`, 
meaning Blaine will attempt to heal his Pokémon even if they are at full HP.

## Formalization
We model the battle state including the enemy Pokémon's HP and the 8-bit 
random roll used by the AI engine.
-/

/-- The state of the enemy Pokémon relevant to the AI decision. -/
structure BattleState where
  currentHP : BitVec 16
  maxHP     : BitVec 16
  aiRoll    : BitVec 8
deriving DecidableEq, Repr

/-- 
Implementation of Blaine's AI routine as found in `engine/battle/trainer_ai.asm`.
