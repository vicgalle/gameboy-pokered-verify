import SM83

/-!
# Bug #10: badge_reflect

A catastrophic interaction between three Game Boy mechanics:
1. Badge stat boosts are reapplied to ALL stats whenever any stat changes.
2. Reflect doubles the current defense stat with no upper bound check.
3. The damage formula scales stats by dividing by 4 and taking the low byte, 
   causing values ≥ 1024 to wrap around.

This results in a Pokémon's effective defense dropping to near zero if a stat 
modifier (like Growl) is used while Reflect is active.
-/

namespace AutoResearch

/-- 
Models the `applyBoostToStat` function in `engine/battle/core.asm`.
Multiplies the stat by 9/8 (stat + stat/8) and caps it at 999.
-/
def badgeBoost (stat : Nat) : Nat :=
  let boost := stat / 8
  let res := stat + boost
  if res > 999 then 999 else res

/-- 
Models the Reflect move. 
In the SM83 implementation, it doubles the stat but crucially lacks 
the 999 cap check found in badge boost functions.
-/
def applyReflect (stat : Nat) : Nat :=
  stat * 2

/-- 
Models the scaling in the damage formula.
The stat is divided by 4 and then cast to an 8-bit register.
This is mathematically equivalent to (stat / 4) % 256.
-/
def getEffectiveDefenseBuggy (stat : Nat) : Nat :=
  (stat / 4) % 256

/-- 
The intended behavior for damage scaling.
Stat should be capped at 255 after division to prevent wrapping.
-/
def getEffectiveDefenseSpec (stat : Nat) : Nat :=
  let s := stat / 4
  if s > 255 then 255 else s

/-- 
Models the buggy sequence:
1. A Pokémon has a current defense stat.
2. A stat change (like Growl) incorrectly triggers a badge re-application.
3. Reflect is applied (doubling the already high stat).
4. Damage formula scales the stat using the wrapping-bugged logic.
-/
def impl (currentDef : Nat) : Nat :=
  let s1 := badgeBoost currentDef -- Re-applied boost
  let s2 := applyReflect s1       -- Doubled by reflect
  getEffectiveDefenseBuggy s2     -- Wrapped result

/-- 
Correct behavior: stats do not re-apply and Reflect/Scaling are capped.
-/
def spec (currentDef : Nat) : Nat :=
  let s1 := applyReflect currentDef
  getEffectiveDefenseSpec s1

/-- 
L1: Bug Existence Witness
A Cloyster with 458 defense perfectly demonstrates the bug.
1. Badge boost: 458 + (458/8) = 458 + 57 = 515.
2. Reflect: 515 * 2 = 1030.
3. Scaling: (1030 / 4) % 256 = 257 % 256 = 1.
-/
theorem bug_exists : ∃ d, impl d ≠ spec d := by
  exists 458
  native_decide

/--
L2: The Reflect Paradox.
Because of the overflow, having Reflect active actually makes the Pokémon
significantly weaker (lower effective defense) than if Reflect were not active.
-/
theorem reflect_paradox :
  let base_defense := 458
  let def_with_reflect := impl base_defense
  let def_without_reflect := getEffectiveDefenseBuggy (badgeBoost base_defense)
  def_with_reflect < def_without_reflect := by
  -- 1 < 128
  native_decide

/-- 
L2: Characterization of the catastrophic wrap-around.
When the internal stat hits 1024, the effective defense becomes 0.
-/
theorem wrap_around_point : getEffectiveDefenseBuggy 1024 = 0 := by
  simp [getEffectiveDefenseBuggy]

/--
L3: Fix Correctness.
A proper implementation caps the stat both during reflect and during scaling.
-/
def fix (currentDef : Nat) : Nat :=
  let s1 := applyReflect currentDef
  let s1_capped := if s1 > 999 then 999 else s1
  getEffectiveDefenseSpec s1_capped

theorem fix_prevents_wrap (d : Nat) : fix d ≤ 255 := by
  simp [fix, getEffectiveDefenseSpec]
  split <;> omega

/--
L3: Fix vs Spec.
Show that for a valid range of stats, the fix matches the intended behavior.
-/
theorem fix_matches_spec (d : Nat) : d ≤ 500 → fix d = getEffectiveDefenseSpec (applyReflect d) := by
  intro h
  simp [fix, applyReflect, getEffectiveDefenseSpec]
  have : d * 2 ≤ 1000 := by omega
  split
  · next h_big => 
    -- if d*2 > 999 and d*2 <= 1000, then d*2 must be 1000
    have : d * 2 = 1000 := by omega
    simp [this]
  · next h_small => 
    simp

end AutoResearch
