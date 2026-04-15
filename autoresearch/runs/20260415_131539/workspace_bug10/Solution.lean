import SM83

namespace AutoResearch

/-- 
Models the 'ApplyBadgeStatBoosts' logic in engine/battle/core.asm.
It multiplies a stat by 9/8 (stat + stat/8) and caps the result at 999.
-/
def applyBadgeBoost (stat : BitVec 16) : BitVec 16 :=
  let boost := stat >>> 3
  let res := stat + boost
  -- MAX_STAT_VALUE in Pokemon Red/Blue is 999 (0x03E7)
  if res.toNat > 999 then BitVec.ofNat 16 999 else res

/-- 
Models the recursive nature of the Badge Stacking bug. 
Every time a stat is modified, all badge boosts are reapplied.
-/
def badgeStacking (baseStat : BitVec 16) : Nat → BitVec 16
  | 0 => baseStat
  | n + 1 => applyBadgeBoost (badgeStacking baseStat n)

/-- 
The buggy Damage Scaling logic from Gen 1.
If the stat (possibly doubled by Reflect) is >= 256, the game divides it by 4
using two 16-bit right shifts. It then loads the low byte into the 8-bit register A.
The bug: if (stat/4) >= 256, the high byte is discarded, causing a wrap-around.
-/
def impl (statInRam : BitVec 16) (reflectActive : Bool) : BitVec 8 :=
  -- Reflect doubles the defense stat before scaling
  let d : BitVec 16 := if reflectActive then statInRam <<< 1 else statInRam
  -- The game checks if the high byte is non-zero (i.e., stat >= 256)
  if d >= 256 then
    -- It shifts the 16-bit value twice and then takes the low byte
    BitVec.ofNat 8 (d.toNat / 4)
  else
    -- If < 256, it uses the value as-is
    BitVec.ofNat 8 d.toNat

/-- 
The intended Damage Scaling logic.
Scales values >= 256 by dividing by 4, but clamps the result at 255 
instead of allowing 8-bit overflow.
-/
def spec (statInRam : BitVec 16) (reflectActive : Bool) : BitVec 8 :=
  let d : Nat := if reflectActive then statInRam.toNat * 2 else statInRam.toNat
  let scaled := if d >= 256 then d / 4 else d
  BitVec.ofNat 8 (if scaled > 255 then 255 else scaled)

/- 
  L1: Bug Existence (Witness) 
  Verify the Cloyster case: 458 base defense.
  One badge boost (e.g. from an opponent's Growl) pushes defense to 515.
  Using Reflect on 515 defense (effectively 1030) results in effective defense 1.
-/
theorem bug_exists : 
  let cloyster_base := BitVec.ofNat 16 458
  let boosted := applyBadgeBoost cloyster_base
  -- Boosted value is 515 (458 + 57)
  boosted.toNat = 515 ∧
  -- Without Reflect: (515 / 4) = 128
  impl boosted false = BitVec.ofNat 8 128 ∧
  -- With Reflect: (1030 / 4) = 257. Wrapped: 257 % 256 = 1
  impl boosted true = BitVec.ofNat 8 1 := by
  native_decide

/- 
  L2: Characterization of the Catastrophe
  Prove that a single 'beneficial' badge boost triggered by an opponent's move 
  can reduce effective defense by more than 99% when Reflect is active.
-/
theorem boost_can_be_catastrophic :
  ∃ (s : BitVec 16),
    let before := (impl s true).toNat
    let after := (impl (applyBadgeBoost s) true).toNat
    before > 200 ∧ after < 5 := by
  -- Witness: Cloyster base (458)
  use BitVec.ofNat 16 458
  native_decide

/-
  L3: Monotonicity and Correctness
  The intended logic (spec) is monotonic: higher stats always result in higher
  or equal effective defense. The buggy logic (impl) fails this property.
-/
theorem spec_is_monotonic (s1 s2 : BitVec 16) (r : Bool) :
  s1.toNat <= s2.toNat → (spec s1 r).toNat <= (spec s2 r).toNat := by
  unfold spec
  intro h
  -- Use omega to handle the arithmetic branching logic
  split <;> split <;> split <;> split <;> try split <;> try split <;>
  simp [BitVec.toNat_ofNat] <;>
  -- Handle modulo 256 logic implicitly defined by the clamping
  (repeat (case _ => 
    intro
    try have := Nat.mod_eq_of_lt (by omega : _ < 256)
    try rw [this]
    omega))

theorem impl_is_not_monotonic :
  ¬ ∀ (s1 s2 : BitVec 16) (r : Bool),
    s1.toNat <= s2.toNat → (impl s1 r).toNat <= (impl s2 r).toNat := by
  intro h
  -- 511 * 2 = 1022. 1022 / 4 = 255.
  -- 512 * 2 = 1024. 1024 / 4 = 256 -> 0.
  let s1 := BitVec.ofNat 16 511
  let s2 := BitVec.ofNat 16 512
  have h_le : s1.toNat <= s2.toNat := by native_decide
  have h_bug : (impl s1 true).toNat > (impl s2 true).toNat := by native_decide
  have := h s1 s2 true h_le
  omega

/-
  L4: Trigger Condition Proof
  Prove that for any valid battle stat (capped at 999), the bug triggers 
  if and only if the (doubled) stat reaches the overflow threshold of 1024.
-/
theorem bug_trigger_condition (s : BitVec 16) (r : Bool) :
  s.toNat <= 999 →
  (impl s r != spec s r ↔ (if r then s.toNat * 2 else s.toNat) >= 1024) := by
  intro h_cap
  unfold impl spec
  split <;> split <;> split <;> try split <;> try split
  -- Case: r=true, s*2 >= 256, (s*2/4) > 255
  case isTrue.isTrue.isTrue.isTrue r_act d_ge_256 d_ge_256_spec scaled_gt_255 =>
    simp at *
    constructor
    · intro _; omega
    · intro h_trigger
      -- We must show that (d/4 % 256) != 255
      -- Since d <= 999 * 2 = 1998, d/4 is at most 499.
      -- In the range [256, 499], x % 256 can only be 255 if x = 511.
      -- But x is at most 499.
      intro h_eq
      have h_d : (s.toNat * 2) / 4 <= 499 := by omega
      have h_val : (s.toNat * 2) / 4 = 255 + 256 * 0 ∨ (s.toNat * 2) / 4 = 255 + 256 * 1 := by
        have := BitVec.toNat_ofNat 8 ((s.toNat * 2) / 4)
        rw [h_eq] at this
        simp at this
        omega
      omega
  -- Simplify and solve all other non-triggering cases
  all_goals (simp; intro; try solve | contradiction | omega)

end AutoResearch
