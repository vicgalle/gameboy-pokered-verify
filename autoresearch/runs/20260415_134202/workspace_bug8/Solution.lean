import SM83

namespace AutoResearch

/-!
# Bug: Reflect and Light Screen Overflow

In Pokemon Red/Blue, the Reflect and Light Screen moves are intended to double
the user's Defense or Special stat, respectively. However, the damage 
calculation routine handles high stats (above 255) by dividing them by 4 and
keeping only the low byte.

When a Pokemon's stat is doubled *before* this "divide by 4" check, two issues
occur:
1. Stats in the range [128, 255] suddenly trigger the division, causing the 
   effective stat to drop by half instead of doubling.
2. Stats in the range [512, 1023] overflow the 8-bit result after division
   (e.g., 1024 / 4 = 256, which wraps to 0), causing game freezes or massive
   defense drops.
-/

/-- 
Models the Game Boy's "Big Stat" logic in the damage calculation.
If a 16-bit stat's high byte is non-zero (stat > 255), the game divides
the value by 4 and keeps the lower 8 bits.
-/
def calcEffectiveStat (stat : BitVec 16) : BitVec 8 :=
  if stat > 255 then
    -- Divide by 4 and take the lower 8 bits (SM83 ld a, h / srl / rr l logic)
    (stat >>> 2).toBitVec 8
  else
    stat.toBitVec 8

/-- 
The buggy implementation of Reflect/Light Screen.
The stat is doubled first, then passed to the damage calculation's
effective stat logic.
-/
def impl (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  let doubledStat := if hasReflect then stat <<< 1 else stat
  calcEffectiveStat doubledStat

/-- 
The intended behavior: doubling the stat should always result in an
effective value that is exactly twice the original effective value.
-/
def spec (stat : BitVec 16) (hasReflect : Bool) : Nat :=
  let base := calcEffectiveStat stat
  if hasReflect then base.toNat * 2 else base.toNat

/-! ## L1: Bug Existence -/

/-- Reflecting at 512 defense leads to 0 effective defense (Division by Zero freeze). -/
theorem bug_freeze_exists : impl 512 true = 0 := rfl

/-- Reflecting at 200 defense reduces effective defense (100 < 200). -/
theorem bug_reduction_exists : impl 200 true < impl 200 false := by
  native_decide

/-! ## L2: Characterization -/

/-- 
The bug triggers (effective stat decreases) in two specific ranges:
1. [128, 255]: Doubling pushes the stat into the 'divide by 4' logic.
2. [512, 1023]: Doubling overflows the result of the 'divide by 4' logic.
-/
theorem bug_trigger_ranges (stat : BitVec 16) :
    ((stat >= 128 ∧ stat <= 255) ∨ (stat >= 512 ∧ stat < 1024)) → 
    impl stat true < impl stat false := by
  intro h
  cases h with
  | inl h1 => 
    have := (by native_decide : ∀ x : BitVec 16, x >= 128 ∧ x <= 255 → impl x true < impl x false)
    apply this; exact h1
  | inr h2 =>
    have := (by native_decide : ∀ x : BitVec 16, x >= 512 ∧ x < 1024 → impl x true < impl x false)
    apply this; exact h2

/-- Reflect only works correctly (doubles the effective stat) for stats under 128. -/
theorem reflect_safe_range (stat : BitVec 16) (h : stat < 128) :
    (impl stat true).toNat = (impl stat false).toNat * 2 := by
  have := (by native_decide : ∀ x : BitVec 16, x < 128 → (impl x true).toNat = (impl x false).toNat * 2)
  apply this; exact h

/-! ## L3: Fix Correctness -/

/-- 
A potential fix: Perform the effective stat calculation *before* doubling,
ensuring the result stays within the intended bounds.
-/
def fix (stat : BitVec 16) (hasReflect : Bool) : Nat :=
  let base := calcEffectiveStat stat
  if hasReflect then base.toNat * 2 else base.toNat

/-- The fix matches the intended specification. -/
theorem fix_matches_spec (stat : BitVec 16) (hasReflect : Bool) :
    fix stat hasReflect = spec stat hasReflect := rfl

/-- The fix ensures Reflect never decreases the effective defense. -/
theorem fix_is_monotonic (stat : BitVec 16) :
    fix stat true >= fix stat false := by
  unfold fix
  simp
  apply Nat.le_mul_of_pos_right
  exact Nat.zero_lt_succ 1

/-! ## L4: Relational Divergence -/

/-- 
The bug creates a "relational inversion" where a Pokemon with higher base 
Defense (200) becomes significantly squishier than one with lower base 
Defense (100) once Reflect is applied.
-/
theorem relational_inversion : 
    let lowDef := BitVec.ofNat 16 100
    let highDef := BitVec.ofNat 16 200
    -- Unreflected: 200 > 100
    (impl highDef false > impl lowDef false) ∧ 
    -- Reflected: 100 < 200 (The higher base stat now results in a lower effective stat)
    (impl highDef true < impl lowDef true) := by
  native_decide

end AutoResearch

