import SM83

/-!
# Bug #10: badge_reflect

A catastrophic interaction between three mechanics in Pokémon Red/Blue:
1. Badge boosts (9/8 multiplier) are reapplied whenever any stat changes.
2. Reflect doubles the defense stat without an upper bound check.
3. Stat scaling in the damage formula wraps at 1024 (divides by 4, then takes low byte).

This formalization models the defense stat calculation and demonstrates how a 
Cloyster (458 Defense) can end up with 1 effective Defense due to these overflows.
-/

namespace AutoResearch

/-- 
Multiplies a 16-bit stat by 1.125 (adding 1/8 of its value).
As seen in `ApplyBadgeStatBoosts`, the stat is capped at 999.
-/
def apply_badge_boost (stat : BitVec 16) : BitVec 16 :=
  let s := stat.toNat
  let boosted := s + (s / 8)
  if boosted > 999 then BitVec.ofNat 16 999
  else BitVec.ofNat 16 boosted

/-- 
Doubles the defense stat when Reflect is active. 
The assembly fails to check for overflow beyond 1024/max stat limits here.
-/
def apply_reflect (stat : BitVec 16) : BitVec 16 :=
  stat * 2

/-- 
The damage formula scales defense by dividing by 4 and taking the 8-bit result.
This effectively performs (stat / 4) % 256, causing a wrap-around at 1024.
-/
def calculate_effective_defense (stat : BitVec 16) : BitVec 8 :=
  BitVec.ofNat 8 (stat.toNat / 4)

/-- 
The buggy behavior:
Badge boosts can be applied multiple times due to the reapplication bug.
Reflect is then applied, and the final value is scaled for damage.
-/
def impl (initial_stat : BitVec 16) (num_boosts : Nat) : BitVec 8 :=
  let rec boost_loop (s : BitVec 16) (n : Nat) : BitVec 16 :=
    match n with
    | 0 => s
    | n + 1 => boost_loop (apply_badge_boost s) n
  let boosted := boost_loop initial_stat num_boosts
  calculate_effective_defense (apply_reflect boosted)

/-- 
The intended behavior:
1. Badge boost is applied exactly once.
2. The stat is capped to prevent overflow before damage scaling.
-/
def spec (initial_stat : BitVec 16) : BitVec 8 :=
  let boosted := apply_badge_boost initial_stat
  let reflected := apply_reflect boosted
  -- A correct implementation would cap the value at 999 or 1023
  let capped := if reflected.toNat > 999 then BitVec.ofNat 16 999 else reflected
  calculate_effective_defense capped

/-! ### L1: Bug Existence -/

/-- 
Witness: Cloyster with 458 Defense.
With 1 badge boost (Thunder Badge) reapplication (e.g. after a Growl),
and Reflect active, effective defense drops to 1.
-/
theorem bug_exists_cloyster : impl (BitVec.ofNat 16 458) 1 = 1 := by
  native_decide

/-! ### L2: Characterization -/

/-- 
The bug triggers a catastrophic drop whenever the reflected stat 
crosses the 1024 threshold (1024 / 4 = 256 ≡ 0 mod 256).
-/
theorem bug_threshold_behavior : 
  let stat_after_boost := apply_badge_boost (BitVec.ofNat 16 458)
  let stat_after_reflect := apply_reflect stat_after_boost
  stat_after_reflect.toNat ≥ 1024 ∧ calculate_effective_defense stat_after_reflect = 1 := by
  native_decide

/-- 
Demonstrates that the effective defense is significantly lower than 
the intended defense for the Cloyster scenario.
-/
theorem bug_massive_defense_loss : 
  (impl (BitVec.ofNat 16 458) 1).toNat < (spec (BitVec.ofNat 16 458)).toNat / 100 := by
  native_decide

/-! ### L3: Fix Correctness -/

/-- 
A fixed implementation that caps the stat after reflecting to ensure 
it never exceeds the scaling limit of the damage formula.
-/
def fix (initial_stat : BitVec 16) (num_boosts : Nat) : BitVec 8 :=
  let rec boost_loop (s : BitVec 16) (n : Nat) : BitVec 16 :=
    match n with
    | 0 => s
    | n + 1 => if n = 0 then apply_badge_boost s else s -- Cap at 1 boost
  let boosted := boost_loop initial_stat num_boosts
  let reflected := apply_reflect boosted
  -- Clamp to 999 to prevent overflow into the 1024+ range
  let clamped := if reflected.toNat > 999 then BitVec.ofNat 16 999 else reflected
  calculate_effective_defense clamped

/-- The fix preserves high defense for Cloyster instead of wrapping to 1. -/
theorem fix_is_robust : fix (BitVec.ofNat 16 458) 1 = 249 := by
  native_decide

/-- The fix matches the specification for the base case. -/
theorem fix_matches_spec (s : BitVec 16) : fix s 1 = spec s := by
  unfold fix spec
  simp

end AutoResearch
