import SM83

namespace AutoResearch

/-!
# Bug: Reflect and Light Screen Overflow

Reflect and Light Screen are moves that double the user's Defense and Special stats,
respectively. In Pokemon Red/Blue, the damage calculation routine has an arithmetic
overflow bug when handling high stats.

When any stat exceeds 255, the routine scales both Attacker and Defender stats down
by dividing them by 4. However, Reflect doubles the stat *before* this check.
If a stat is 512 or higher, doubling it results in 1024 or higher.
Dividing 1024 by 4 results in 256, which, when stored in an 8-bit register, 
overflows to 0. This causes a division-by-zero game freeze.

For stats slightly above 512, the result wraps around to small numbers, making
the "doubled" defense significantly lower than the original defense.
-/

/-- 
The effective defense stat as used in the damage formula denominator.
When any stat > 255, the engine scales the stats by dividing by 4.
This models the denominator without the Reflect doubling applied.
-/
def base (s : BitVec 16) : Nat :=
  if s.toNat > 255 then s.toNat / 4 else s.toNat

/-- 
Buggy implementation of Reflect doubling.
The stat is doubled, then if it exceeds 255, it is divided by 4 and 
truncated to an 8-bit value (modulo 256).
-/
def impl (s : BitVec 16) : Nat :=
  let doubled := s.toNat * 2
  if doubled > 255 then (doubled / 4) % 256 else doubled

/-- 
Specification: The doubling should behave correctly and not wrap around 
at the 8-bit boundary (256) even after the engine's scaling division.
-/
def spec (s : BitVec 16) : Nat :=
  let doubled := s.toNat * 2
  if doubled > 255 then (doubled / 4) else doubled

-- L1: Concrete witness - A stat of 512 leads to an effective defense of 0 (freeze).
theorem bug_exists_freeze : impl 512 = 0 := rfl

-- L1: Concrete witness - A stat of 128 actually decreases defense when Reflect is used.
-- base 128 = 128
-- impl 128 = (256 / 4) % 256 = 64
theorem bug_exists_reduction : impl 128 < base 128 := by
  simp [impl, base]
  native_decide

-- L2: Universal characterization - Reflect reduces defense for stats in the range [512, 1000].
-- This covers the range where the overflow significantly undermines the stat.
theorem weakening_forall_high : ∀ s : BitVec 16, s.toNat >= 512 ∧ s.toNat < 1000 → impl s < base s := by
  intro s h
  have h_univ := (by native_decide : ∀ v : BitVec 16, v.toNat >= 512 ∧ v.toNat < 1000 → 
    (let d := v.toNat * 2; if d > 255 then (d / 4) % 256 else d) < 
    (if v.toNat > 255 then v.toNat / 4 else v.toNat))
  exact h_univ s h

-- L2: Universal - Reflect also reduces defense for stats in the range [128, 255] 
-- because it triggers the engine's "divide by 4" scaling while the base stat doesn't.
theorem weakening_forall_low : ∀ s : BitVec 16, s.toNat >= 128 ∧ s.toNat < 256 → impl s < base s := by
  intro s h
  have h_univ := (by native_decide : ∀ v : BitVec 16, v.toNat >= 128 ∧ v.toNat < 256 → 
    (let d := v.toNat * 2; if d > 255 then (d / 4) % 256 else d) < 
    (if v.toNat > 255 then v.toNat / 4 else v.toNat))
  exact h_univ s h

-- L3: Fix - The corrected version should not apply the 8-bit truncation (modulo 256).
def fix (s : BitVec 16) : Nat :=
  let doubled := s.toNat * 2
  if doubled > 255 then (doubled / 4) else doubled

theorem fix_is_correct : ∀ s : BitVec 16, fix s = spec s := fun _ => rfl

-- L4: Relational - The implementation and specification diverge exactly at the overflow point (512).
-- Below 512 (where doubled < 1024), the 8-bit truncation doesn't yet wrap around.
theorem impl_spec_desync : ∀ s : BitVec 16, s.toNat >= 512 ∧ s.toNat < 1024 → impl s < spec s := by
  intro s h
  have h_univ := (by native_decide : ∀ v : BitVec 16, v.toNat >= 512 ∧ v.toNat < 1024 → 
    (let d := v.toNat * 2; if d > 255 then (d / 4) % 256 else d) < 
    (let d := v.toNat * 2; if d > 255 then (d / 4) else d))
  exact h_univ s h

end AutoResearch

