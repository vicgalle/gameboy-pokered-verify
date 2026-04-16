import SM83

namespace AutoResearch

/-!
# Bug #8: reflect_overflow

## Description
In Pokemon Red, Blue, and Yellow, the moves **Reflect** and **Light Screen** double the 
user's Defense and Special stats, respectively. During damage calculation, if either 
the attacker's or defender's stat exceeds 255, both stats are divided by 4 to keep 
the intermediate multiplication within 16-bit limits.

The bug occurs because the result of this division is stored in an 8-bit register, 
effectively taking the value **modulo 256**. If a Pokemon's stat is high enough 
(512 or above), doubling it and then dividing by 4 results in a value of 256 or higher, 
which wraps around to 0 or a very small number when truncated. 

This causes two catastrophic effects:
1.  **Division by zero**: If the effective defense wraps to exactly 0 (e.g., at 512), 
    the game freezes during the damage calculation division.
2.  **Stat Reduction**: If the stat wraps to a small value, Reflect actually 
    increases the damage taken instead of halving it.
-/

/-- 
Effective stat calculation in Gen 1.
If a stat (after modifications like Reflect) is > 255, it is divided by 4.
The BUG is that the result is truncated to 8 bits (`% 256`).
-/
def get_eff_stat_impl (s : Nat) : Nat :=
  if s > 255 then (s / 4) % 256 else s

/-- 
The intended behavior: Stats > 255 are divided by 4, but the full result
is preserved (no truncation to 8 bits).
-/
def get_eff_stat_spec (s : Nat) : Nat :=
  if s > 255 then (s / 4) else s

/-- Effective defense with Reflect applied (doubled). -/
def apply_reflect_impl (d : Nat) : Nat := get_eff_stat_impl (d * 2)

/-- Intended effective defense with Reflect applied. -/
def apply_reflect_spec (d : Nat) : Nat := get_eff_stat_spec (d * 2)

/-- Defense without Reflect (baseline). -/
def no_reflect (d : Nat) : Nat := get_eff_stat_impl d

/-- 
Simplified damage model. 
Damage is inversely proportional to the defense stat.
Defense = 0 results in extreme damage (modeling the division-by-zero freeze).
-/
def damage (def_stat : Nat) : Nat :=
  if def_stat = 0 then 100000 else 10000 / def_stat

-- L1: Concrete witness of the bug
theorem exists_overflow_bug : ∃ d, apply_reflect_impl d ≠ apply_reflect_spec d :=
  ⟨512, by rfl⟩

-- L1: The division-by-zero crash witness
theorem reflect_freeze_at_512 : apply_reflect_impl 512 = 0 :=
  by rfl

-- L2: Characterization of the harmful range
-- For defense stats between 512 and 999 (the Gen 1 cap), 
-- Reflect makes the effective defense lower than it was without Reflect.
theorem reflect_is_detrimental_forall (d : Fin 1000) :
  d.val >= 512 → apply_reflect_impl d.val < no_reflect d.val := by
  -- Using the native_decide universal pattern for the finite stat range 0-999
  have h := (by native_decide : ∀ v : Fin 1000, v.val >= 512 → 
    apply_reflect_impl v.val < no_reflect v.val)
  intro h_ge; exact h d h_ge

-- L3: Verification of a fix
def fix_get_eff_stat (s : Nat) : Nat :=
  if s > 255 then (s / 4) else s

def apply_reflect_fix (d : Nat) : Nat := fix_get_eff_stat (d * 2)

theorem fix_matches_spec : ∀ d, apply_reflect_fix d = apply_reflect_spec d := by
  intro d; rfl

-- L4: Relational divergence (Damage)
-- We show that the bug causes Reflect to increase damage taken (detrimental),
-- whereas it should have decreased damage taken (beneficial).
theorem damage_bug_increases_damage_taken :
  damage (apply_reflect_impl 512) > damage (no_reflect 512) := by
  native_decide

theorem damage_spec_decreases_damage_taken :
  damage (apply_reflect_spec 512) < damage (no_reflect 512) := by
  native_decide

-- L2: The bug wraps values around every 1024 units (stat * 2 / 4 % 256)
theorem reflect_wraps_at_1024 : apply_reflect_impl 512 = apply_reflect_impl 0 := by
  rfl

end AutoResearch
