import BitVec

namespace AutoResearch

/-!
# Bug #3: Blaine's AI Uses Super Potion Regardless of HP

## Description
In Pokémon Red/Blue, trainer AI routines generally follow a "roll then check" pattern:
1. A random roll determines if the AI *intends* to use an item (e.g., 25% chance).
2. A subsequent check (`AICheckIfHPBelowFraction`) determines if the Pokémon's 
   current HP is low enough to justify using the item.

Blaine's AI (`BlaineAI`) in `engine/battle/trainer_ai.asm` contains a logic bug. 
It performs the probability roll (`cp 25 percent + 1`) but jumps directly to 
`AIUseSuperPotion` without calling the HP check. As a result, Blaine will 
consume his Super Potions even if his Pokémon is at full health, granting the 
player a free turn.

## Formalization
We model the probability roll and the HP check logic as defined in the SM83 
assembly and prove that Blaine's implementation deviates from the intended 
"Heal if Low" specification.
-/

/-- 
The Pokémon Red `percent` macro: `x * 255 / 100`.
Used in `cp 25 percent + 1`.
-/
def gamePercent (p : Nat) : Nat := (p * 255) / 100

/--
The roll threshold used by Blaine: `25 percent + 1`.
25 * 255 / 100 = 63.
63 + 1 = 64.
A random roll < 64 (0-63) triggers the action (25% of 0-255).
-/
def BLAINE_THRESHOLD : Nat := (gamePercent 25) + 1

/--
State representing the AI's environment during its turn.
-/
structure BattleState where
  roll  : BitVec 8   -- Random value 0-255
  curHP : BitVec 16  -- Current HP
  maxHP : BitVec 16  -- Max HP
deriving DecidableEq, Repr

/-- 
Model of the `AICheckIfHPBelowFraction` assembly routine.
In assembly, this routine sets the Carry flag if `current HP < max HP / divisor`.
We use `divisor = 2` for Super Potions (the 50% HP threshold).
-/
def AICheckIfHPBelowFraction (curHP maxHP : BitVec 16) (divisor : Nat) : Bool :=
  divisor > 0 && curHP.toNat < (maxHP.toNat / divisor)

/-- 
Blaine's actual buggy AI logic.
Matches the assembly:
