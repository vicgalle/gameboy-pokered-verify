import SM83

namespace AutoResearch

/-!
# Bug #10: badge_reflect

The interaction between three mechanics causes a catastrophic defense overflow:
1. **Badge Boost Stacking**: Whenever any stat changes, all badge-boosted stats are 
   re-multiplied by 9/8 (1.125x).
2. **Reflect**: This move doubles the defense stat (2x) without an upper-bound check.
3. **Scaled Wrapping**: The damage formula scales defense by dividing by 4 and then
   keeping only the lower byte (modulo 256), effectively wrapping at 1024.

A Cloyster with high defense (458) can be pushed over the 512 threshold by a single
enemy "Growl" (re-applying the 1.125 boost). When Reflect is active, the defense
crosses 1024, causing the scaled defense to drop from 128 to 1.
-/

/-- 
The 1.125x (9/8) multiplier applied by badges like the Thunder Badge.
Applied to stats whenever any stat change occurs in Gen 1.
-/
def badge_boost (d : BitVec 16) : BitVec 16 :=
  (d * 9) / 8

/-- The doubling effect of the move Reflect on the defense stat. -/
def apply_reflect (d : BitVec 16) : BitVec 16 :=
  d * 2

/-- 
Buggy defense scaling used in the Gen 1 damage formula:
The game calculates (defense / 4), but then keeps only the lower byte
of the result, effectively performing a modulo 256 operation.
-/
def buggy_scale (d : BitVec 16) : BitVec 8 :=
  SM83.lo (d / 4)

/-- 
The intended defense scaling (spec):
Divides by 4 and caps the result at 255 to prevent overflow wrapping.
-/
def spec_scale (d : BitVec 16) : BitVec 8 :=
  let s := d.toNat / 4
  if s > 255 then BitVec.ofNat 8 255
  else BitVec.ofNat 8 s

/-! ## L1: Concrete Witness -/

/-- 
L1: Verifies the Cloyster example from the bug description.
Base defense 458. After a stat change triggers the badge boost, it's 515.
Reflect doubles this to 1030. The buggy scaling reduces effective defense to 1.
-/
theorem bug_exists_cloyster_witness :
  let base_def : BitVec 16 := BitVec.ofNat 16 458
  let boosted_def := badge_boost base_def
  let reflected_def := apply_reflect boosted_def
  boosted_def = BitVec.ofNat 16 515 ∧ 
  reflected_def = BitVec.ofNat 16 1030 ∧ 
  buggy_scale reflected_def = BitVec.ofNat 8 1 := by
  simp [badge_boost, apply_reflect, buggy_scale, SM83.lo]
  native_decide

/-! ## L2: Universal Characterization -/

/--
L2: Characterizes the "Danger Zone". 
If the defense stat (before Reflect) is in the range [512, 640),
applying Reflect results in a lower scaled defense than not applying Reflect 
due to the 1024 wrap-around (since 2*d >= 1024).
-/
theorem reflect_weakening_range_forall (d : BitVec 16) :
  (d.toNat ≥ 512 ∧ d.toNat < 640) →
  (buggy_scale (apply_reflect d)).toNat < (buggy_scale d).toNat := by
  intro h
  have := (by native_decide : ∀ v : BitVec 16, (v.toNat ≥ 512 ∧ v.toNat < 640) → 
    (buggy_scale (apply_reflect v)).toNat < (buggy_scale v).toNat)
  apply this d h

/--
L2: Proof of non-monotonicity. 
In a correct system, increasing a stat should never decrease its scaled value.
The buggy system fails this: a higher defense can result in lower protection.
-/
theorem buggy_scale_is_not_monotonic :
  ∃ d1 d2 : BitVec 16, d1.toNat < d2.toNat ∧ (buggy_scale d1).toNat > (buggy_scale d2).toNat := by
  -- Example: d1 = 1020 (scaled 255), d2 = 1024 (scaled 0)
  use BitVec.ofNat 16 1020, BitVec.ofNat 16 1024
  native_decide

/-! ## L3: Fix Verification -/

def fix (d : BitVec 16) : BitVec 8 := spec_scale d

/-- L3: The fix ensures that the scaled defense is monotonic. -/
theorem fix_is_monotonic (d1 d2 : BitVec 16) :
  d1.toNat ≤ d2.toNat → (fix d1).toNat ≤ (fix d2).toNat := by
  intro h
  simp [fix, spec_scale]
  split <;> split
  · simp
  · next h1 h2 => 
    have : (d1.toNat / 4) ≤ 255 := by exact Nat.le_of_not_gt h2
    simp [this]
  · next h1 h2 => omega
  · next h1 h2 => apply Nat.div_le_div_right h

/-- L3: The fix ensures Reflect always provides at least as much protection as no Reflect. -/
theorem fix_reflect_always_helps (d : BitVec 16) :
  (fix (apply_reflect d)).toNat ≥ (fix d).toNat := by
  apply fix_is_monotonic
  simp [apply_reflect]
  omega

/-! ## L4: Relational Properties -/

/-- 
L4: The core bug interaction.
An opponent using Growl is intended to make the player weaker (lowering attack).
Instead, it triggers a badge boost re-application that pushes the player's 
defense into the overflow zone, making the player significantly more vulnerable.
-/
theorem enemy_move_lowers_player_defense :
  let d_initial := BitVec.ofNat 16 458
  let d_after_reflect := apply_reflect d_initial
  let d_after_growl_and_reflect := apply_reflect (badge_boost d_initial)
  (buggy_scale d_after_growl_and_reflect).toNat < (buggy_scale d_after_reflect).toNat - 100 := by
  simp [badge_boost, apply_reflect, buggy_scale, SM83.lo]
  native_decide

/--
L4: Badge Stacking accumulation.
The bug is compounded by multiple stat changes. Repeated Growls will eventually
push even lower defense stats into the overflow cycle.
-/
theorem badge_stacking_accumulation_is_harmful :
  let d0 := BitVec.ofNat 16 458
  let d1 := badge_boost d0 -- 515
  let d2 := badge_boost d1 -- 579
  let d3 := badge_boost d2 -- 651
  -- Reflect(651) = 1302. 1302/4 = 325. 325 % 256 = 69.
  -- Compared to original d0 scaled (114), the player is much weaker despite 3 "boosts".
  (buggy_scale (apply_reflect d3)).toNat < (buggy_scale d0).toNat := by
  simp [badge_boost, apply_reflect, buggy_scale, SM83.lo]
  native_decide

end AutoResearch
