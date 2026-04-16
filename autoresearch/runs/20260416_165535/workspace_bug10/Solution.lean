import SM83

namespace AutoResearch

/-- 
Badge boost multiplier: 9/8 (11.25% increase).
In Pokemon Red, this multiplier is intended to be applied once per battle for each badge.
-/
def apply_boost (s : Nat) : Nat := (s * 9) / 8

/-- 
A recursive helper to model the badge boost restacking bug.
The bug causes the 9/8 multiplier to be reapplied to every stat whenever ANY stat change occurs.
`num_changes` represents the number of additional times a badge boost is triggered.
-/
def apply_badge_boosts : Nat → Nat → Nat
  | s, 0 => s
  | s, n + 1 => apply_boost (apply_badge_boosts s n)

/-- 
The buggy implementation found in Gen 1:
1. Re-applies the badge boost multiplier for every stat change that occurs (restacking).
2. The Reflect move doubles the current defense stat without an upper bound check.
3. The damage formula scaling wraps values at 1024. In SM83 assembly, this occurs 
   because defense is divided by 4 using bit shifts, and then only the low byte
   of the result is used for the subsequent damage calculation.
   Formula: (defense / 4) % 256.
-/
def impl (start_stat : Nat) (num_changes : Nat) (has_reflect : Bool) : Nat :=
  -- start_stat represents the stat value after the initial battle-start boost.
  let boosted := apply_badge_boosts start_stat num_changes
  -- Reflect doubles the current value.
  let reflected := if has_reflect then boosted * 2 else boosted
  -- Scaling bug: (result / 4) then keep only the low byte.
  (reflected / 4) % 256

/--
The intended behavior (specification):
1. Badge boost is applied exactly once (represented here as start_stat).
2. Reflect doubles the stat.
3. Scaling caps the result at 255 instead of wrapping (overflow protection).
-/
def spec (start_stat : Nat) (num_changes : Nat) (has_reflect : Bool) : Nat :=
  let _ignore_reapplications := num_changes
  let reflected := if has_reflect then start_stat * 2 else start_stat
  let scaled := reflected / 4
  if scaled > 255 then 255 else scaled

/- L1: Concrete witness showing the bug exists -/
theorem bug_exists : ∃ s n r, impl s n r ≠ spec s n r := 
  ⟨458, 1, true, by native_decide⟩

/- L1: The Cloyster example described in the bug report.
   A Cloyster with 458 def (already boosted once) faces a Growl (1 reapplication).
   The effective defense becomes 1 instead of its intended value. -/
theorem cloyster_catastrophe : impl 458 1 true = 1 := by rfl

/- L2: Reflect detriment - for specific high stats, Reflect makes you significantly weaker.
   Reflect is supposed to double defense, but here it causes an overflow that reduces 
   effective defense from 128 to 1. -/
theorem reflect_detriment : impl 458 1 true < impl 458 1 false := by
  -- 1 < 128
  native_decide

/- L2: Growl detriment - an opponent move (Growl) that lowers a stat actually harms the 
   player's defense by triggering the badge re-application overflow. -/
theorem growl_detriment : impl 458 1 true < impl 458 0 true := by
  -- 1 < 229
  native_decide

/- L2: The bug causes the implementation to lose monotonicity.
   In a normal system, more boosts result in higher stats. Here, more boosts lead
   to an overflow that results in a lower effective stat. -/
theorem impl_non_monotonic : ∃ s n1 n2 r, n1 < n2 ∧ impl s n1 r > impl s n2 r := 
  ⟨458, 0, 1, true, by native_decide⟩

/- L2: Universal property of the badge boost multiplier (monotonicity).
   The underlying 9/8 multiplier function itself never decreases the stat. -/
theorem badge_boost_monotonic : ∀ s : Nat, apply_boost s ≥ s := by
  intro s
  simp [apply_boost]
  omega

/- L3: A fixed implementation that matches the specification. -/
def fix (s : Nat) (n : Nat) (r : Bool) : Nat :=
  let reflected := if r then s * 2 else s
  let scaled := reflected / 4
  if scaled > 255 then 255 else scaled

theorem fix_correct : ∀ s n r, fix s n r = spec s n r := by
  intro s n r; rfl

/- L4: The catastrophic divergence between spec and impl.
   The intended defense (229) is 228 units higher than the bugged result (1). -/
theorem catastrophic_divergence : spec 458 1 true - impl 458 1 true = 228 := by
  native_decide

end AutoResearch
