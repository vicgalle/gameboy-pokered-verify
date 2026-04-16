import SM83

namespace AutoResearch

-- "25 percent + 1" threshold from BlaineAI.
-- BlaineAI fires ~25.4% of the time (random < 65 out of 256).
-- cp 25 percent + 1 ; ret nc ; jp AIUseSuperPotion
def HEAL_THRESHOLD : Nat := 65

-- Buggy Blaine AI: decides to use Super Potion based only on random check.
-- BUG: AICheckIfHPBelowFraction is never called — HP is completely ignored.
def impl (randomVal : BitVec 8) : Bool :=
  decide (randomVal.toNat < HEAL_THRESHOLD)

-- Correct specification: Super Potion should only be used when BOTH:
--   (1) random check passes (< ~25%), AND
--   (2) current HP is below 50% of maximum (HP actually needs healing)
def spec (randomVal : BitVec 8) (currentHP maxHP : BitVec 8) : Bool :=
  decide (randomVal.toNat < HEAL_THRESHOLD ∧ currentHP.toNat * 2 < maxHP.toNat)

-- L1: Concrete witness — bug fires at full HP.
-- randomVal=0 triggers Blaine's buggy AI (0 < 65), but spec correctly refuses
-- because HP is full (200/200 = 100%, not below 50%).
theorem l1_witness : impl 0 = true ∧ spec 0 200 200 = false := by
  native_decide

-- L1b: Another concrete case — random value 50 also triggers the bug at full HP.
theorem l1_another_witness : impl 50 = true ∧ spec 50 255 255 = false := by
  native_decide

-- L2: For ALL triggering random values, impl fires at full HP but spec does not.
-- This universally characterizes the bug: any random value below the threshold
-- will waste the Super Potion if HP happens to be full.
theorem l2_full_hp_bug : ∀ r hp : BitVec 8,
    r.toNat < HEAL_THRESHOLD →
    impl r = true ∧ spec r hp hp = false := by
  native_decide

-- L2b: Spec never wastes Super Potion when currentHP equals maxHP (any random value).
-- hp.toNat * 2 < hp.toNat is always false for Nat, so the conjunction is always false.
theorem l2_spec_no_waste_at_full_hp : ∀ r hp : BitVec 8,
    spec r hp hp = false := by
  native_decide

-- L2c: impl's decision is purely random — it fires if and only if random is low,
-- with no dependence on HP state whatsoever.
theorem l2_impl_triggers_iff_random_low : ∀ r : BitVec 8,
    impl r = true ↔ r.toNat < HEAL_THRESHOLD := by
  native_decide

-- L2d: The bug causes divergence exactly in the ~25% triggering window.
-- When impl says "heal," spec at full HP always disagrees.
theorem l2_divergence_at_full_hp : ∀ r : BitVec 8,
    r.toNat < HEAL_THRESHOLD → impl r ≠ spec r 255 255 := by
  native_decide

-- L3: Fixed implementation adds the HP check that BlaineAI was missing.
-- Models the correct behavior that AICheckIfHPBelowFraction would provide.
def implFixed (randomVal : BitVec 8) (currentHP maxHP : BitVec 8) : Bool :=
  decide (randomVal.toNat < HEAL_THRESHOLD ∧ currentHP.toNat * 2 < maxHP.toNat)

-- L3: The fix is definitionally equal to the spec — rfl suffices.
theorem l3_fix_correct : ∀ r hp maxHp : BitVec 8,
    implFixed r hp maxHp = spec r hp maxHp :=
  fun _ _ _ => rfl

-- L3b: Fixed version never wastes Super Potion when HP is at maximum.
theorem l3_fix_no_waste : ∀ r hp : BitVec 8,
    implFixed r hp hp = false := by
  native_decide

-- L3c: Fixed version correctly uses Super Potion when HP is genuinely low.
-- Example: randomVal=0 (triggers), currentHP=50, maxHP=200 → HP at 25% → heal.
theorem l3_fix_heals_when_needed : implFixed 0 50 200 = true := by
  native_decide

-- L3d: Fixed version never heals a Pokemon that has more than half its HP.
-- For any random trigger, if currentHP ≥ maxHP/2, no potion is used.
theorem l3_fix_respects_hp_threshold : ∀ r hp maxHp : BitVec 8,
    hp.toNat * 2 ≥ maxHp.toNat → implFixed r hp maxHp = false := by
  native_decide

end AutoResearch
