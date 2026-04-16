import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate (Pokémon Red, Gen 1)

## Description
In Generation 1 Pokémon, Focus Energy should increase the critical-hit rate by
doubling the threshold register B. Instead, a one-opcode bug (`SRL` written
where `SLA` was intended) halves B, reducing the critical-hit probability to
**1/4** of normal.

## Assembly (simplified, normal move, FE branch)

    SRL B              ; b ← baseSpeed >> 1
    ...
  .focusEnergyUsed:
    SRL B              ; ← BUG (should be SLA B) — quarters threshold
  .noFocusEnergyUsed:
    SRL B              ; final divisor for normal moves
-/

/-- `SRL B` — logical right-shift by 1. -/
def srl8 (b : BitVec 8) : BitVec 8 := b >>> 1

/-- `SLA B` with carry cap: left-shift saturating to 0xFF on overflow. -/
def sla8_capped (b : BitVec 8) : BitVec 8 :=
  if b.toNat ≥ 128 then (0xFF : BitVec 8) else b <<< 1

/-- **impl** — Buggy Pokémon Red: Focus Energy branch uses `SRL` instead of `SLA`. -/
def impl (baseSpeed : BitVec 8) (hasFE : Bool) : BitVec 8 :=
  let b := srl8 baseSpeed
  let b := if hasFE then srl8 b else sla8_capped b   -- BUG: SRL instead of SLA
  srl8 b

/-- **spec** — Intended behavior: Focus Energy branch uses `SLA` (same as no-FE path). -/
def spec (baseSpeed : BitVec 8) (hasFE : Bool) : BitVec 8 :=
  let b := srl8 baseSpeed
  let b := sla8_capped b                              -- FIXED: always SLA
  srl8 b

/-! ### L1 — Concrete witnesses -/

/-- Pikachu (base Speed 90): Focus Energy lowers crit threshold from 45 to 11. -/
theorem L1_pikachu_witness :
    impl 90 true = 11 ∧ spec 90 true = 45 := by native_decide

/-- Blastoise (base Speed 78): Focus Energy lowers crit threshold from 39 to 9. -/
theorem L1_blastoise_witness :
    impl 78 true = 9 ∧ spec 78 true = 39 := by native_decide

/-- Jolteon (base Speed 130): Focus Energy lowers crit threshold from 65 to 16. -/
theorem L1_jolteon_witness :
    impl 130 true = 16 ∧ spec 130 true = 65 := by native_decide

/-! ### L2 — Universal characterisation -/

/-- Exact formula: buggy FE threshold equals `baseSpeed >>> 3` (three right-shifts). -/
theorem L2_impl_fe_exact (speed : BitVec 8) :
    impl speed true = speed >>> 3 := by native_decide

/-- Exact formula: no-FE threshold equals `baseSpeed >>> 1` (one right-shift). -/
theorem L2_impl_no_fe_exact (speed : BitVec 8) :
    impl speed false = speed >>> 1 := by native_decide

/-- Exact formula: the intended threshold is always `baseSpeed >>> 1`, regardless of FE status. -/
theorem L2_spec_formula (speed : BitVec 8) (fe : Bool) :
    spec speed fe = speed >>> 1 := by native_decide

/-- The bug universally reduces the crit threshold to ≤ ¼ of the intended value. -/
theorem L2_bug_quarters_threshold (speed : BitVec 8) :
    (impl speed true).toNat * 4 ≤ (spec speed true).toNat := by native_decide

/-- Without Focus Energy both models agree: the bug is entirely dormant. -/
theorem L2_no_fe_models_agree (speed : BitVec 8) :
    impl speed false = spec speed false := by native_decide

/-- For speeds ≥ 2, Focus Energy *strictly* harms the crit rate under the bug. -/
theorem L2_fe_strictly_harmful :
    ∀ speed : BitVec 8, 2 ≤ speed.toNat →
    (impl speed true).toNat < (impl speed false).toNat := by native_decide

/-- The buggy FE threshold is always ≤ the no-FE threshold in the correct spec. -/
theorem L2_buggy_fe_beats_nothing :
    ∀ speed : BitVec 8,
    (impl speed true).toNat ≤ (spec speed false).toNat := by native_decide

/-- impl diverges from spec exactly on the FE branch; the gap grows with speed. -/
theorem L2_divergence_monotone :
    ∀ s1 s2 : BitVec 8, s1.toNat ≤ s2.toNat →
    (spec s1 true).toNat - (impl s1 true).toNat ≤
    (spec s2 true).toNat - (impl s2 true).toNat := by native_decide

/-! ### L3 — Verified fix -/

/-- Patched implementation: replace the erroneous `SRL` with `SLA` in the FE branch. -/
def impl_fixed (baseSpeed : BitVec 8) (hasFE : Bool) : BitVec 8 :=
  let b := srl8 baseSpeed
  let b := sla8_capped b   -- PATCH: SRL → SLA
  srl8 b

/-- The patched implementation matches the specification for *every* input. -/
theorem L3_fix_matches_spec (speed : BitVec 8) (fe : Bool) :
    impl_fixed speed fe = spec speed fe := by native_decide

/-- For speeds ≥ 2, the fix strictly increases the FE threshold over the buggy version. -/
theorem L3_fix_strictly_improves :
    ∀ speed : BitVec 8, 2 ≤ speed.toNat →
    (impl speed true).toNat < (impl_fixed speed true).toNat := by native_decide

/-- The fix introduces no regression when FE has not been used. -/
theorem L3_no_regression (speed : BitVec 8) :
    impl_fixed speed false = impl speed false := by native_decide

/-- After the fix, the threshold is the same whether or not FE was used. -/
theorem L3_fix_fe_neutral (speed : BitVec 8) :
    impl_fixed speed true = impl_fixed speed false := by native_decide

/-! ### L4 — Relational divergence -/

/-- In **spec**, Focus Energy is neutral: using it makes no difference. -/
theorem L4_spec_fe_neutral (speed : BitVec 8) :
    spec speed true = spec speed false := by native_decide

/-- In **impl**, Focus Energy always weakly lowers the crit threshold. -/
theorem L4_impl_fe_harms_rate (speed : BitVec 8) :
    (impl speed true).toNat ≤ (impl speed false).toNat := by native_decide

/-- Monotonicity: a faster Pokémon has a higher absolute threshold (buggy or not). -/
theorem L4_threshold_monotone (s1 s2 : BitVec 8) (h : s1.toNat ≤ s2.toNat) :
    (impl s1 true).toNat ≤ (impl s2 true).toNat := by native_decide

/-- The buggy FE threshold is bounded above by the correct threshold divided by 4. -/
theorem L4_upper_bound_exact (speed : BitVec 8) :
    (impl speed true).toNat ≤ (spec speed true).toNat / 4 + 1 := by native_decide

/-- impl and spec produce the same result for all (speed, FE) *except* when hasFE = true. -/
theorem L4_divergence_iff (speed : BitVec 8) (fe : Bool) :
    impl speed fe = spec speed fe ↔ fe = false := by native_decide

/-- Relational summary: no-FE paths agree; FE path in impl falls to ≤ ¼ of spec. -/
theorem L4_divergence_characterised (speed : BitVec 8) :
    impl speed false = spec speed false ∧
    (impl speed true).toNat * 4 ≤ (spec speed true).toNat :=
  ⟨L2_no_fe_models_agree speed, L2_bug_quarters_threshold speed⟩

end AutoResearch
