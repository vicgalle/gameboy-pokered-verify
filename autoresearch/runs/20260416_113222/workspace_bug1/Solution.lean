import SM83

namespace AutoResearch

/-- Buggy Focus Energy critical hit threshold calculation from Pokemon Red.
    CriticalHitTest: computes b = base_speed >> 1, then for Focus Energy:
    - BUG: SRL B (right shift, ÷2, giving base_speed/4)
    - Correct would be: SLA B (left shift, ×2, giving ≈base_speed)
    Without Focus Energy: SLA B with carry cap (≈base_speed). -/
def impl (base_speed : BitVec 8) (focus_energy : Bool) : BitVec 8 :=
  let b := base_speed >>> 1   -- SRL B: b = base_speed / 2
  if focus_energy then
    b >>> 1                   -- BUG: SRL B again → base_speed / 4
  else
    if b.toNat >= 128 then (255 : BitVec 8) else b <<< 1  -- SLA B with carry cap

/-- Correct Focus Energy critical hit threshold: FE should SLA (not SRL). -/
def spec (base_speed : BitVec 8) (focus_energy : Bool) : BitVec 8 :=
  let b := base_speed >>> 1   -- SRL B: b = base_speed / 2
  if focus_energy then
    if b.toNat >= 128 then (255 : BitVec 8) else b <<< 1  -- CORRECT: SLA B
  else
    if b.toNat >= 128 then (255 : BitVec 8) else b <<< 1  -- SLA B

-- L1: Concrete witness (speed=200): buggy FE gives 50, correct gives 200.
theorem l1_witness : impl 200 true ≠ spec 200 true := by native_decide

-- L1b: Concrete witness (speed=64): buggy FE gives 16, correct gives 64.
theorem l1_witness_64 : impl 64 true ≠ spec 64 true := by native_decide

-- L2a: Focus Energy REDUCES crit threshold (opposite of intent).
theorem l2_fe_reduces_crit : ∀ x : BitVec 8,
    (impl x true).toNat ≤ (impl x false).toNat := by native_decide

-- L2b: For base_speed ≥ 2, Focus Energy STRICTLY reduces crit threshold.
theorem l2_fe_strictly_reduces : ∀ x : BitVec 8,
    x.toNat ≥ 2 → (impl x true).toNat < (impl x false).toNat := by native_decide

-- L2c: Buggy threshold ≤ correct threshold for all speeds with FE active.
theorem l2_impl_leq_spec_fe : ∀ x : BitVec 8,
    (impl x true).toNat ≤ (spec x true).toNat := by native_decide

-- L2d: Without Focus Energy, buggy and correct implementations agree.
theorem l2_no_fe_agrees : ∀ x : BitVec 8,
    impl x false = spec x false := by native_decide

-- L2e: Correct spec gives identical threshold whether or not FE is active
-- (base_speed/2 always has bit 7 clear, so SLA never overflows to 255).
theorem l2_spec_fe_irrelevant : ∀ x : BitVec 8,
    spec x true = spec x false := by native_decide

-- L2f: Exact formula — buggy FE threshold is exactly floor(base_speed / 4).
theorem l2_impl_fe_exact : ∀ x : BitVec 8,
    (impl x true).toNat = x.toNat / 4 := by native_decide

-- L2g: Exact formula — correct FE threshold equals base_speed rounded down to even.
theorem l2_spec_fe_exact : ∀ x : BitVec 8,
    (spec x true).toNat = x.toNat - x.toNat % 2 := by native_decide

-- L2h: Correct threshold ≥ 4× buggy threshold for every speed.
-- Precisely quantifies the "quartering" effect of the bug.
theorem l2_spec_at_least_4x_impl : ∀ x : BitVec 8,
    (spec x true).toNat ≥ 4 * (impl x true).toNat := by native_decide

-- L2i: The buggy FE threshold is strictly below the no-FE threshold for all typical
-- Pokemon speeds: the "buff" is actually a substantial nerf.
theorem l2_fe_is_nerf_not_buff : ∀ x : BitVec 8,
    x.toNat ≥ 4 →
    (impl x true).toNat * 4 ≤ (impl x false).toNat := by native_decide

-- L3: Fixed implementation — use SLA in the Focus Energy branch.
def implFixed (base_speed : BitVec 8) (focus_energy : Bool) : BitVec 8 :=
  let b := base_speed >>> 1
  if focus_energy then
    if b.toNat >= 128 then (255 : BitVec 8) else b <<< 1  -- FIXED: SLA B
  else
    if b.toNat >= 128 then (255 : BitVec 8) else b <<< 1

-- L3a: Fix matches spec for all inputs with Focus Energy active.
theorem l3_fix_correct_fe : ∀ x : BitVec 8,
    implFixed x true = spec x true := by native_decide

-- L3b: Fix matches spec for all inputs without Focus Energy.
theorem l3_fix_correct_no_fe : ∀ x : BitVec 8,
    implFixed x false = spec x false := by native_decide

-- L3c: Fix is FE-neutral (both branches identical — FE has no effect at this stage).
theorem l3_fix_fe_neutral : ∀ x : BitVec 8,
    implFixed x true = implFixed x false := by native_decide

-- L3d: Fix is strictly better than buggy impl for all speeds ≥ 2 with FE active.
theorem l3_fix_strictly_better : ∀ x : BitVec 8,
    x.toNat ≥ 2 → (implFixed x true).toNat > (impl x true).toNat := by native_decide

-- L3e: Fix always gives at least as high a crit threshold as buggy impl (all speeds).
theorem l3_fix_dominates_impl_fe : ∀ x : BitVec 8,
    (implFixed x true).toNat ≥ (impl x true).toNat := by native_decide

-- L3f: Unified fix: implFixed matches spec for ALL inputs regardless of FE state.
theorem l3_fix_correct_universal : ∀ x : BitVec 8, ∀ fe : Bool,
    implFixed x fe = spec x fe := by native_decide

-- L4: Link battle desync — existential witness.
-- Player A uses buggy Focus Energy; Player B does not.
-- A synchronized roll of 100 gives Player B (no FE, threshold=200) a critical hit
-- but denies it to Player A (buggy FE, threshold=50), reversing the intended advantage.
theorem l4_desync_witness : ∃ speed : BitVec 8, ∃ roll : BitVec 8,
    roll.toNat < (impl speed false).toNat ∧
    ¬(roll.toNat < (impl speed true).toNat) := by native_decide

-- L4b: Universal desync: for EVERY base speed ≥ 4, there exists a synchronized roll
-- that gives the non-FE player a critical hit but not the FE player.
-- This means the bug creates adversarial outcomes for EVERY viable Pokemon speed.
theorem l4_universal_desync : ∀ x : BitVec 8,
    x.toNat ≥ 4 →
    ∃ roll : BitVec 8, roll.toNat < (impl x false).toNat ∧
    ¬(roll.toNat < (impl x true).toNat) := by native_decide

-- L4c: Under the correct spec, the FE player always has ≥ the non-FE threshold,
-- so no analogous desync exists in the intended game logic.
theorem l4_spec_no_fe_desync : ∀ x : BitVec 8,
    (spec x true).toNat ≥ (spec x false).toNat := by native_decide

end AutoResearch
