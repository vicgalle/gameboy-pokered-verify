import SM83
import Harness

namespace AutoResearch

/-!
## Bug: Blaine's AI Uses Super Potion Without Checking HP

In Pokemon Red, BlaineAI:
    cp 25percent+1       ; compare random A register with threshold
    ret nc               ; return if A >= threshold (no carry, no potion)
    jp AIUseSuperPotion  ; use potion -- NO HP CHECK performed!

Every other trainer AI calls AICheckIfHPBelowFraction before healing.
Blaine skips this, wasting Super Potions even when his Pokémon is at full HP.
-/

-- Random trigger threshold: 25% + 1 ≈ 65 out of 256
abbrev THRESHOLD : BitVec 8 := 65

-- impl (buggy BlaineAI): uses Super Potion based on random chance alone
-- Models: cp 25percent+1 / ret nc / jp AIUseSuperPotion
def impl (randomA : BitVec 8) (currentHP maxHP : BitVec 16) : Bool :=
  decide (randomA.toNat < THRESHOLD.toNat)

-- spec (correct behavior): use Super Potion only if chance triggers
-- AND Pokémon actually needs healing (currentHP < maxHP)
def spec (randomA : BitVec 8) (currentHP maxHP : BitVec 16) : Bool :=
  decide (randomA.toNat < THRESHOLD.toNat) &&
  decide (currentHP.toNat < maxHP.toNat)

-- L1: Concrete witness of the bug
-- randomA = 0 (triggers, 0 < 65), HP at full health (currentHP = maxHP = 100)
-- impl = true  (Blaine wastes the Super Potion)
-- spec = false (correct AI would withhold the potion)
theorem l1_bug_witness :
    impl 0 100 100 = true ∧ spec 0 100 100 = false := by
  native_decide

-- L2: The bug is real — there exist inputs where impl and spec disagree
-- Whenever random triggers but HP is full, impl ≠ spec
theorem l2_impl_ne_spec :
    ∃ (r : BitVec 8) (hp : BitVec 16), impl r hp hp ≠ spec r hp hp := by
  exact ⟨0, 100, by native_decide⟩

-- L3: Fix — add the missing HP check before using Super Potion
def implFixed (randomA : BitVec 8) (currentHP maxHP : BitVec 16) : Bool :=
  decide (randomA.toNat < THRESHOLD.toNat) &&
  decide (currentHP.toNat < maxHP.toNat)

-- Fixed implementation matches spec for all inputs
theorem l3_fixed_matches_spec :
    ∀ (r : BitVec 8) (hp maxHP : BitVec 16),
    implFixed r hp maxHP = spec r hp maxHP := by
  intros r hp maxHP
  simp [implFixed, spec]

end AutoResearch
