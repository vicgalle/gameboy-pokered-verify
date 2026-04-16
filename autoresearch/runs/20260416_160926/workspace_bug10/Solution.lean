import SM83

/-!
# Bug #10: Badge Boost Stacking Enables Catastrophic Reflect Overflow

## Gameplay Description
Three mechanics interact to create this bug:
1. **Badge Boost Bug**: Badge stat multipliers (9/8x) are incorrectly reapplied to all stats 
   whenever *any* stat change occurs in battle (e.g., an opponent using Growl).
2. **Reflect**: This move doubles the Pokemon's Defense stat during damage calculation 
   without checking for a 16-bit overflow or scaling bounds.
3. **Stat Scaling Flaw**: To prevent overflow in the damage formula, stats > 255 are 
   divided by 4. However, the game only uses the low byte of the result. 
   If `(Stat / 4) >= 256`, the resulting effective defense wraps around.

## Impact
A Cloyster with a high defense stat (e.g., 458) can have its Defense pushed above the 
critical threshold (512) by a badge boost. When Reflect is then applied, the stat 
exceeds 1024. After the faulty scaling, the defense wraps around, dropping from a 
intended high value to nearly zero (e.g., 1030 becomes 1).
-/

namespace AutoResearch

/-- 
Multiplies a Pokemon's stat by the badge boost multiplier (9/8). 
In Gen 1, this is implemented as `stat + floor(stat/8)`.
-/
def applyBadgeBoost (d : Nat) : Nat :=
  (d * 9) / 8

/-- Doubles the Defense stat as per the Reflect mechanic. -/
def applyReflect (d : Nat) : Nat :=
  d * 2

/-- 
The buggy Gen 1 stat scaling logic. 
If the stat is > 255, it is divided by 4, but only the low byte (modulo 256) 
is used for the final damage calculation.
-/
def impl_scale (d : Nat) : Nat :=
  if d > 255 then (d / 4) % 256 else d

/-- 
The intended scaling logic. 
Stats exceeding 255 should be scaled down and capped at 255 to prevent wrapping.
-/
def spec_scale (d : Nat) : Nat :=
  if d > 255 then Nat.min 255 (d / 4) else d

/-! ### L1: Concrete Witness -/

/-- 
Verifies the Cloyster case: Defense 458 + Badge Boost + Reflect.
The effective defense becomes 1 (catastrophic failure), while the spec expects 255.
-/
theorem l1_cloyster_overflow_witness :
  let d_initial := 458
  let d_boosted := applyBadgeBoost d_initial
  let d_final   := applyReflect d_boosted
  impl_scale d_final = 1 ∧ spec_scale d_final = 255 :=
by
  -- d_boosted = 515
  -- d_final = 1030
  -- impl_scale = (1030 / 4) % 256 = 257 % 256 = 1
  -- spec_scale = min 255 (1030 / 4) = min 255 257 = 255
  rfl

/-! ### L2: Universal Characterization -/

/-- 
The scaling logic is periodic for stats > 255, wrapping every 1024 units. 
This confirms that the bug is systemic and occurs at regular intervals.
-/
theorem l2_periodicity : 
  ∀ d, d > 255 → impl_scale (d + 1024) = impl_scale d :=
by
  intro d h
  unfold impl_scale
  have h_big : d + 1024 > 255 := by omega
  simp [h, h_big]
  have h_div : (d + 1024) / 4 = d / 4 + 256 := by omega
  rw [h_div, Nat.add_mod, Nat.mod_self]
  simp

/-- 
High defense values can result in an effective defense of exactly 0,
making the Pokemon infinitely more vulnerable than intended.
-/
theorem l2_catastrophic_zero :
  ∀ d, (∃ k : Nat, k > 0 ∧ d = 1024 * k) → impl_scale d = 0 :=
by
  intro d h
  match h with
  | ⟨k, hk, rfl⟩ =>
    unfold impl_scale
    have h_gt : 1024 * k > 255 := by
      have h_min : 1024 * k ≥ 1024 := by
        apply Nat.le_mul_of_pos_right
        exact hk
      omega
    simp [h_gt]
    have h_div : 1024 * k / 4 = 256 * k := by omega
    rw [h_div, Nat.mul_mod, Nat.mod_self]
    simp

/-! ### L3: Fix Verification -/

/-- A fixed scaling implementation that correctly caps the value at 255. -/
def fixed_scale (d : Nat) : Nat :=
  if d > 255 then
    let scaled := d / 4
    if scaled > 255 then 255 else scaled
  else
    d

/-- The fixed implementation matches the specification for all possible stats. -/
theorem l3_fix_is_correct :
  ∀ d, fixed_scale d = spec_scale d :=
by
  intro d
  unfold fixed_scale spec_scale
  split <;> split <;> simp [Nat.min] <;> omega

/-! ### L4: Relational Divergence -/

/-- 
The "Badge Boost Paradox": Applying the badge boost (intended as a 12.5% buff) 
can paradoxically reduce the effective defense by over 99%.
-/
theorem l4_detrimental_badge_boost :
  let d_base := 458
  let eff_def_normal := impl_scale (applyReflect d_base)
  let eff_def_buggy  := impl_scale (applyReflect (applyBadgeBoost d_base))
  eff_def_buggy < (eff_def_normal / 100) :=
by 
  -- eff_def_normal = 229
  -- eff_def_buggy = 1
  -- 1 < 2
  decide

/-- 
The buggy implementation is non-monotonic: increasing your raw defense 
can actually decrease your effective defense.
In contrast, the specification is monotonic.
-/
theorem l4_non_monotonicity :
  ∃ d1 d2, d1 < d2 ∧ impl_scale d1 > impl_scale d2 :=
by
  -- d1 = 1023 (scaled to 255)
  -- d2 = 1024 (scaled to 0)
  use 1023, 1024
  constructor
  . omega
  . decide

/-- Proves the specification is correctly monotonic, unlike the implementation. -/
theorem l4_spec_is_monotonic :
  ∀ d1 d2, d1 ≤ d2 → spec_scale d1 ≤ spec_scale d2 :=
by
  intro d1 d2 h
  unfold spec_scale
  split <;> split <;> simp [Nat.min] <;> omega

end AutoResearch
