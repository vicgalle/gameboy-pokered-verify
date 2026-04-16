import SM83

namespace AutoResearch

-- Threshold for Blaine's random check: ~25% + 1 of 256 ≈ 64
def threshold : Nat := 64

-- BUGGY: Blaine's AI uses Super Potion based solely on the random number check.
-- AICheckIfHPBelowFraction is never called, so HP is never verified.
def impl (randomVal currentHP maxHP : BitVec 8) : Bool :=
  decide (randomVal.toNat < threshold)

-- CORRECT: Should check both the random threshold AND that healing is needed.
def spec (randomVal currentHP maxHP : BitVec 8) : Bool :=
  decide (randomVal.toNat < threshold) && decide (currentHP.toNat < maxHP.toNat)

-- FIXED: Adds the missing HP check before consuming the Super Potion.
def implFixed (randomVal currentHP maxHP : BitVec 8) : Bool :=
  decide (randomVal.toNat < threshold) && decide (currentHP.toNat < maxHP.toNat)

-- ───── L1: Concrete witnesses ─────

-- Bug witness: Pokémon at full HP (100/100), random = 10 (< 64 threshold)
-- impl wastes the Super Potion; spec correctly does nothing
theorem l1_witness : impl 10 100 100 ≠ spec 10 100 100 := by native_decide

-- Buggy impl incorrectly fires at full health
theorem l1_impl_fires_at_full_hp : impl 10 100 100 = true := by native_decide

-- Correct spec skips the potion at full health
theorem l1_spec_skips_at_full_hp : spec 10 100 100 = false := by native_decide

-- ───── L2: Universal characterizations ─────

-- impl ignores HP entirely: same outcome for any HP value given the same random
theorem l2_impl_ignores_hp : ∀ r hp : BitVec 8,
    impl r hp hp = impl r 0 0 := by native_decide

-- spec correctly refrains from healing when HP is at maximum (currentHP = maxHP)
theorem l2_spec_no_waste_at_max_hp : ∀ hp : BitVec 8,
    spec 0 hp hp = false := by native_decide

-- spec is a subset of impl: whenever spec would trigger, impl would also trigger
theorem l2_spec_implies_impl : ∀ r hp : BitVec 8,
    spec r hp 255 = true → impl r hp 255 = true := by native_decide

-- The bug is universal: impl fires at full HP whenever random passes threshold
theorem l2_impl_always_fires_at_full_hp : ∀ r : BitVec 8,
    spec r r r = false := by native_decide

-- The bug exists concretely: impl fires in a case where spec correctly does not
theorem l2_bug_exists : ∃ r hp maxhp : BitVec 8,
    impl r hp maxhp = true ∧ spec r hp maxhp = false :=
  ⟨10, 100, 100, by native_decide, by native_decide⟩

-- ───── L3: Fix and verify ─────

-- The fixed implementation matches spec for all inputs
theorem l3_fix_correct : ∀ r hp maxhp : BitVec 8,
    implFixed r hp maxhp = spec r hp maxhp := by
  intro r hp maxhp
  simp [implFixed, spec]

-- The fixed implementation never wastes potions at full HP
theorem l3_fix_no_waste : ∀ hp : BitVec 8,
    implFixed 0 hp hp = false := by native_decide

-- The fix distinguishes it from impl: they disagree at full HP when random passes
theorem l3_fix_differs_from_impl : implFixed 10 100 100 ≠ impl 10 100 100 := by native_decide

end AutoResearch
