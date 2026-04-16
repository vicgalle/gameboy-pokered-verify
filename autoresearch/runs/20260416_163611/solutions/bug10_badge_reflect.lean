import SM83

namespace AutoResearch

/-!
# Bug #10: Badge Boost Stacking Enables Catastrophic Reflect Overflow

The interaction between three mechanics causes this bug:
1. Badge boosts (1.125x) are reapplied to stats on any stat change (like Growl).
2. Reflect doubles the defense stat (2x) without an upper-bound check.
3. The damage formula scaling logic (stat / 4) wraps values at 1024 (modulo 256).

A Cloyster with high defense that gets boosted and then uses Reflect can cross 
the 1024 threshold, causing its effective defense to drop to near zero.
-/

/-- The 1.125x (9/8) multiplier applied by badges like the Thunder Badge. -/
def badge_boost (d : BitVec 16) : BitVec 16 :=
  (d * 9) / 8

/-- The doubling effect of the move Reflect. -/
def apply_reflect (d : BitVec 16) : BitVec 16 :=
  d * 2

/-- 
Buggy defense scaling used in the damage formula:
Divides by 4 and keeps only the low byte (modulo 256).
-/
def buggy_scale (d : BitVec 16) : BitVec 8 :=
  SM83.lo (d / 4)

/-- 
The intended defense scaling:
Divides by 4 and caps the result at 255.
-/
def spec_scale (d : BitVec 16) : BitVec 8 :=
  let s := d.toNat / 4
  if s > 255 then BitVec.ofNat 8 255
  else SM83.lo (d / 4)

/-! ## L1: Concrete Witness -/

/-- 
L1: Verifies the Cloyster example from the bug description.
A Cloyster with 458 defense gets boosted to 515, then Reflect doubles it to 1030.
The final scaled defense becomes 1.
-/
theorem bug_exists_cloyster_witness :
  let base_def : BitVec 16 := BitVec.ofNat 16 458
  let boosted_def := badge_boost base_def
  let reflected_def := apply_reflect boosted_def
  boosted_def = BitVec.ofNat 16 515 ∧ 
  reflected_def = BitVec.ofNat 16 1030 ∧ 
  buggy_scale reflected_def = BitVec.ofNat 8 1 := by
  simp [badge_boost, apply_reflect, buggy_scale, SM83.lo]
  decide

/-! ## L2: Universal Characterization -/

/--
L2: Characterizes the overflow threshold. 
Whenever a defense stat (after Reflect) is in the range [1024, 1280),
the buggy scale result will be smaller than the result without Reflect.
-/
theorem reflect_overflow_characterization (d : BitVec 16) :
  (d.toNat ≥ 512 ∧ d.toNat < 640) →
  (buggy_scale (apply_reflect d)).toNat < (buggy_scale d).toNat := by
  intro h
  have := (by native_decide : ∀ v : BitVec 16, (v.toNat ≥ 512 ∧ v.toNat < 640) → 
    (buggy_scale (apply_reflect v)).toNat < (buggy_scale v).toNat)
  apply this d h

/-! ## L3: Fix Verification -/

def fix (d : BitVec 16) : BitVec 8 := spec_scale d

/-- L3: The fix ensures that the scaled defense never wraps around zero. -/
theorem fix_is_monotonic (d1 d2 : BitVec 16) :
  d1.toNat ≤ d2.toNat → (fix d1).toNat ≤ (fix d2).toNat := by
  intro h
  simp [fix, spec_scale]
  split <;> split
  · simp
  · next h1 h2 => 
    have : (d1 / 4).toNat ≤ 255 := by
      rw [BitVec.toNat_div] at h1; exact Nat.le_of_not_gt h1
    simp [SM83.lo, this]
  · next h1 h2 =>
    rw [BitVec.toNat_div] at h2
    omega
  · next h1 h2 =>
    simp [SM83.lo]
    rw [BitVec.toNat_div] at *
    apply Nat.div_le_div_right h

theorem fix_never_wraps : ∀ d : BitVec 16, (fix d).toNat ≤ 255 := by
  intro d; simp [fix, spec_scale]; split <;> simp [SM83.lo]

/-! ## L4: Relational Properties -/

/-- 
L4: The Reflect move is intended to buff defense, but because of the bug,
it can actually make the player 128x weaker than if they hadn't used it.
-/
theorem reflect_weakens_player_at_515 :
  let d := BitVec.ofNat 16 515
  (buggy_scale (apply_reflect d)).toNat = 1 ∧ (buggy_scale d).toNat = 128 := by
  simp [apply_reflect, buggy_scale, SM83.lo]
  decide

/--
L4: The opponent's move (Growl) triggering a badge re-application 
is what pushes the player over the threshold into a catastrophic state.
-/
theorem growl_triggers_catastrophe : 
  let d_base : BitVec 16 := BitVec.ofNat 16 458
  let d_no_growl := d_base -- Badge boost not reapplied
  let d_with_growl := badge_boost d_base -- Growl triggers re-application
  (buggy_scale (apply_reflect d_with_growl)).toNat < (buggy_scale (apply_reflect d_no_growl)).toNat := by
  simp [badge_boost, apply_reflect, buggy_scale, SM83.lo]
  -- reflect(458) scaled = 229
  -- reflect(515) scaled = 1
  decide

end AutoResearch
