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

-- impl's result depends only on random value; HP doesn't affect the outcome at all
theorem l2_impl_ignores_hp : ∀ r hp : BitVec 8,
    impl r hp hp = impl r 0 0 := by native_decide

-- impl fires exactly when random < threshold — no other condition matters
theorem l2_impl_iff_threshold : ∀ r : BitVec 8,
    impl r 255 255 = decide (r.toNat < threshold) := by native_decide

-- spec correctly returns false when HP is at maximum (no healing needed)
theorem l2_spec_requires_damage : ∀ r hp : BitVec 8,
    spec r hp hp = false := by native_decide

-- Whenever random passes threshold, impl fires even at full HP
theorem l2_impl_fires_when_full : ∀ r hp : BitVec 8,
    r.toNat < threshold → impl r hp hp = true := by native_decide

-- spec is subsumed by impl: spec firing implies impl would also fire
theorem l2_spec_implies_impl : ∀ r hp : BitVec 8,
    spec r hp 255 = true → impl r hp 255 = true := by native_decide

-- impl and spec agree only when the random check fails (threshold not crossed)
theorem l2_impl_spec_agree_iff_random_fails : ∀ r : BitVec 8,
    (impl r 200 200 = spec r 200 200) ↔ ¬(r.toNat < threshold) := by native_decide

-- The bug is existentially witnessed: impl fires when spec correctly does not
theorem l2_bug_exists : ∃ r hp maxhp : BitVec 8,
    impl r hp maxhp = true ∧ spec r hp maxhp = false :=
  ⟨10, 100, 100, by native_decide, by native_decide⟩

-- Full-HP waste scenario: impl always fires but spec always correctly skips
theorem l2_waste_at_full_hp : ∀ r : BitVec 8,
    r.toNat < threshold →
    impl r 200 200 = true ∧ spec r 200 200 = false := by native_decide

-- impl is completely blind to maxHP: injured and full-health Pokémon treated identically
theorem l2_impl_blind_to_max_hp : ∀ r : BitVec 8,
    impl r 200 255 = impl r 200 200 := by native_decide

-- spec is strictly monotone: more damage → more likely to trigger
-- (if spec fires at high HP, it fires at lower HP too)
theorem l2_spec_monotone_in_damage : ∀ r hp1 hp2 : BitVec 8,
    hp1.toNat ≤ hp2.toNat → spec r hp2 255 = true → spec r hp1 255 = true := by native_decide

-- ───── L3: Fix and verify ─────

-- The fixed implementation matches spec for all inputs
theorem l3_fix_correct : ∀ r hp maxhp : BitVec 8,
    implFixed r hp maxhp = spec r hp maxhp := by
  intro r hp maxhp; simp [implFixed, spec]

-- Fixed implementation never wastes potions at full HP, for any random value
theorem l3_fix_never_fires_at_full : ∀ r hp : BitVec 8,
    implFixed r hp hp = false := by native_decide

-- Fixed implementation is strictly more conservative than buggy impl
theorem l3_fix_more_conservative : ∀ r hp : BitVec 8,
    implFixed r hp 255 = true → impl r hp 255 = true := by native_decide

-- The fix and buggy impl disagree at the canonical full-HP bug case
theorem l3_fix_differs_from_impl : implFixed 10 100 100 ≠ impl 10 100 100 := by native_decide

-- Fixed implementation agrees with buggy impl exactly when HP genuinely needs healing
theorem l3_fix_agrees_when_hurt : ∀ r : BitVec 8,
    implFixed r 50 255 = impl r 50 255 := by native_decide

-- Fixed implementation fires iff random passes threshold (when Pokemon is visibly hurt)
theorem l3_fix_fires_iff_both_conditions : ∀ r : BitVec 8,
    implFixed r 100 200 = decide (r.toNat < threshold) := by native_decide

-- ───── L4: Relational divergence ─────

-- Buggy Blaine and a correct AI always disagree on full-HP Pokémon when random passes:
-- same battle state, different action — a universal relational split
theorem l4_blaine_vs_correct_ai_diverge : ∀ r hp : BitVec 8,
    r.toNat < threshold →
    impl r hp hp ≠ implFixed r hp hp := by native_decide

-- The two AIs agree precisely on clearly damaged Pokémon (100/200 HP)
theorem l4_agree_on_damaged_pokemon : ∀ r : BitVec 8,
    impl r 100 200 = implFixed r 100 200 := by native_decide

-- Divergence is asymmetric: impl strictly dominates implFixed in trigger frequency
-- impl fires in every case implFixed fires, plus additional wasteful cases
theorem l4_impl_strictly_dominates : ∀ r hp : BitVec 8,
    implFixed r hp 200 = true → impl r hp 200 = true := by native_decide

-- The relational gap: impl fires on full-HP Pokemon across the entire threshold range
theorem l4_full_divergence_below_threshold : ∀ r : BitVec 8,
    r.toNat < threshold →
    impl r 200 200 = true ∧ implFixed r 200 200 = false := by native_decide

end AutoResearch
