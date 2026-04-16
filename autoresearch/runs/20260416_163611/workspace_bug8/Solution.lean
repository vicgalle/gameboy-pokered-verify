import SM83

namespace AutoResearch

/-!
# Bug #8: reflect_overflow

## Description
In Pokemon Red, Blue, and Yellow, the moves **Reflect** and **Light Screen** double the 
user's Defense and Special stats, respectively. During damage calculation, the engine 
contains logic to prevent 16-bit overflows: if either the attacker's or defender's 
stat exceeds 255, both stats are divided by 4 before multiplication.

The bug occurs because the result of this division is truncated to 8 bits (`% 256`) 
during the calculation. If a Pokemon's stat is high enough (512 or above), doubling 
it and then dividing by 4 results in a value of 256 or higher, which wraps around 
to 0 or a very small number when truncated. 

This causes two catastrophic effects:
1.  **Division by zero**: If the effective defense wraps to exactly 0 (e.g., at 512 
    or 513), the game freezes during the damage calculation division.
2.  **Stat Reduction**: If the stat wraps to a small non-zero value, Reflect actually 
    increases the damage taken instead of halving it.
-/

/-- 
Implementation of effective stat calculation in Gen 1.
Stat scaling: if a stat (after doubling) > 255, it is divided by 4.
The BUG: the result is truncated to 8 bits (`% 256`).
-/
def get_eff_stat_impl (s : Nat) : Nat :=
  if s > 255 then (s / 4) % 256 else s

/-- 
The intended behavior: Stats > 255 are divided by 4, but the full 
integer result is preserved without truncation.
-/
def get_eff_stat_spec (s : Nat) : Nat :=
  if s > 255 then (s / 4) else s

/-- Effective defense with Reflect applied (stat is doubled). -/
def apply_reflect_impl (d : Nat) : Nat := get_eff_stat_impl (d * 2)

/-- Intended effective defense with Reflect applied. -/
def apply_reflect_spec (d : Nat) : Nat := get_eff_stat_spec (d * 2)

/-- Defense without Reflect (baseline). -/
def no_reflect (d : Nat) : Nat := get_eff_stat_impl d

/-- 
Simplified damage model. 
Damage is inversely proportional to the defense stat.
Defense = 0 results in a high constant to model the game freeze/crash.
-/
def damage (def_stat : Nat) : Nat :=
  if def_stat = 0 then 100000 else 10000 / def_stat

-- L1: Concrete witness of the bug existing
theorem exists_overflow_bug : ∃ d, apply_reflect_impl d ≠ apply_reflect_spec d :=
  ⟨512, by rfl⟩

-- L1: The division-by-zero crash witness (at the critical value 512)
theorem reflect_freeze_at_512 : apply_reflect_impl 512 = 0 :=
  by rfl

-- L2: Characterization of the crash condition for standard stats.
-- Within the 0-999 stat range, exactly 512 and 513 cause a crash.
theorem reflect_crash_range_forall (d : Fin 1000) : 
  apply_reflect_impl d.val = 0 ↔ d.val = 512 ∨ d.val = 513 := by
  have h := (by native_decide : ∀ v : Fin 1000, 
    apply_reflect_impl v.val = 0 ↔ v.val = 512 ∨ v.val = 513)
  exact h d

-- L2: Characterization of the harmful range.
-- Reflect is detrimental for all stats from 512 up to the engine cap (999).
theorem reflect_is_detrimental_forall (d : Fin 1000) :
  d.val >= 512 → apply_reflect_impl d.val < no_reflect d.val := by
  have h := (by native_decide : ∀ v : Fin 1000, v.val >= 512 → 
    apply_reflect_impl v.val < no_reflect v.val)
  intro h_ge; exact h d h_ge

-- L2: Specification behavior is never detrimental for high stats.
theorem reflect_spec_is_beneficial_high_stats (d : Fin 1000) :
  d.val >= 256 → apply_reflect_spec d.val >= no_reflect d.val := by
  have h := (by native_decide : ∀ v : Fin 1000, v.val >= 256 → 
    apply_reflect_spec v.val >= no_reflect v.val)
  intro h_ge; exact h d h_ge

-- L3: Verification of a fix that preserves the division logic but removes truncation.
def fix_get_eff_stat (s : Nat) : Nat :=
  if s > 255 then (s / 4) else s

def apply_reflect_fix (d : Nat) : Nat := fix_get_eff_stat (d * 2)

theorem fix_matches_spec : ∀ d, apply_reflect_fix d = apply_reflect_spec d := by
  intro d; rfl

theorem fix_prevents_crash : ∀ d : Fin 1000, d.val > 0 → apply_reflect_fix d.val > 0 := by
  have h := (by native_decide : ∀ v : Fin 1000, v.val > 0 → apply_reflect_fix v.val > 0)
  intro d_pos; exact h d d_pos

-- L4: Relational divergence (Damage)
-- Comparison of the buggy implementation vs baseline vs intended spec.
-- At 512, Reflect increases damage (bug) whereas it should halve it (spec).
theorem damage_comparison_at_512 : 
  damage (apply_reflect_impl 512) > damage (no_reflect 512) ∧ 
  damage (apply_reflect_spec 512) < damage (no_reflect 512) := by
  native_decide

-- L2: Characterization of the wrap-around period.
-- Every 512 units of Defense (which becomes 1024 doubled), the bug repeats.
theorem reflect_bug_periodicity (d : Nat) : 
  d >= 256 → apply_reflect_impl (d + 512) = apply_reflect_impl d := by
  intro h_ge
  simp [apply_reflect_impl, get_eff_stat_impl]
  have h1 : (d + 512) * 2 > 255 := by omega
  have h2 : d * 2 > 255 := by omega
  simp [h1, h2]
  have h3 : (d * 2 + 1024) / 4 = (d * 2) / 4 + 256 := by omega
  rw [h3]
  omega

end AutoResearch

