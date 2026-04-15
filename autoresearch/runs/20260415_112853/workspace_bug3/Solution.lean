import Mathlib.Data.BitVec.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

/-!
# Bug #3: Blaine's AI Uses Super Potion Regardless of HP

## Description
In Pokémon Red/Blue, Blaine is the Cinnabar Island Gym Leader. His AI is programmed
to use Super Potions during battle. However, unlike other trainers who check if 
their Pokémon's HP is low before using a healing item, Blaine's AI routine 
(`BlaineAI`) omits this check entirely.

Consequently, Blaine has a 25% chance each turn to use a Super Potion, even if his 
Pokémon is at 100% health, effectively wasting his turn and the item.

## Formalization
1. We model the HP state and the AI's decision process.
2. We implement `AICheckIfHPBelowFraction` based on the provided assembly logic.
3. We model the buggy `BlaineAI` (impl) and the intended `BlaineAI` (spec).
4. We prove the existence of the bug (L1).
5. We characterize exactly when the bug triggers (L2).
6. We provide a verified fix that incorporates the HP check (L3).
-/

namespace AutoResearch

/-- 
HP state of a Pokémon in battle.
Current and Max HP are 16-bit values in the SM83 engine.
-/
structure HPState where
  cur : BitVec 16
  max : BitVec 16
deriving DecidableEq, Repr

/-- 
Standard Pokémon Red/Blue macro for percentages.
Defined in the engine as `floor(p * 255 / 100)`.
-/
def percent (p : Nat) : Nat := (p * 255) / 100

/--
Model of the `AICheckIfHPBelowFraction` assembly routine.
Assembly Logic:
1. Divide MaxHP by divisor `a`.
2. Compare CurrentHP with the resulting Quotient.
3. Return Carry (True) if CurrentHP < Quotient.
-/
def aiCheckIfHPBelowFraction (hp : HPState) (divisor : Nat) : Bool :=
  if divisor = 0 then false
  else hp.cur.toNat < (hp.max.toNat / divisor)

/-- 
The threshold used in Blaine's AI: `cp 25 percent + 1`.
`25 percent` is 63.
`63 + 1 = 64`.
If the random roll (0-255) is less than 64, the AI proceeds.
-/
def blaineThreshold : Nat := percent 25 + 1

/-- 
The buggy implementation of Blaine's AI.
As seen in the assembly:
