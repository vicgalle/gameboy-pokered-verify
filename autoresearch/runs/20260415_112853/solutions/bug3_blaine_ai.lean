import SM83

/-!
# Bug #3: Blaine's AI Uses Super Potion Regardless of HP

## Description
In Pokémon Red/Blue, Blaine is the Cinnabar Island Gym Leader. His AI is programmed
to use Super Potions. However, while other trainers (like Jugglers or Lorelei)
check if their Pokémon's HP is low (typically < 1/2 or < 1/5 of max) before using
a healing item, Blaine's AI routine omits this check. 

Consequently, Blaine has a 25% chance each turn to use a Super Potion, even if his 
Pokémon is at 100% health, effectively wasting his turn and the item.

## Formalization
1. We model the HP state and the AI's decision process.
2. We implement `AICheckIfHPBelowFraction` based on the provided assembly.
3. We model `BlaineAI` (buggy) and a `spec` (corrected version).
4. We prove the existence of the bug and characterize the conditions under which it occurs.
-/

namespace AutoResearch

open BitVec

/-- 
HP state of a Pokémon in battle.
Current and Max HP are 16-bit values in the SM83 engine.
-/
structure HPState where
  cur : BitVec 16
  max : BitVec 16
deriving DecidableEq, Repr

/--
Action chosen by the Trainer AI.
-/
inductive AIAction
  | UseSuperPotion
  | NoAction
deriving DecidableEq, Repr

/-- 
Standard Pokémon Red/Blue macro for percentages.
Defined as `floor(p * 255 / 100)`.
-/
def percent (p : Nat) : BitVec 8 := 
  BitVec.ofNat 8 ((p * 255) / 100)

/--
Model of the `AICheckIfHPBelowFraction` assembly routine.
Assembly logic:
1. Divide MaxHP by divisor `a`.
2. Compare CurrentHP with Quotient.
3. Set carry if CurrentHP < Quotient.
-/
def aiCheckIfHPBelowFraction (hp : HPState) (divisor : Nat) : Bool :=
  if h : divisor = 0 then false
  else 
    let quotient := hp.max.toNat / divisor
    hp.cur.toNat < quotient

/-- 
The threshold used in the assembly: `cp 25 percent + 1`.
`25 percent` is 63. `63 + 1 = 64`.
If the random roll is less than 64, the AI proceeds.
-/
def blaineThreshold : BitVec 8 := 
  (percent 25) + (BitVec.ofNat 8 1)

/-- 
The buggy implementation of Blaine's AI.
Assembly:
