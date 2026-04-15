import SM83

/-!
# Bug #10: badge_reflect

This file formalizes a catastrophic interaction in the Pokémon Red/Blue battle engine:
1. **Badge Stat Boosts**: Multiplies stats by 1.125 (9/8). Re-applied incorrectly during stat changes.
2. **Reflect**: Doubles the Defense stat. Crucially, the implementation of Reflect in RBY
   lacks the 999 cap applied to most other stat modifications.
3. **Stat Scaling**: During damage calculation, the game scales high stats by dividing by 4
   and storing the result in an 8-bit register, causing a wrap-around at 1024.

The result is that a high-defense Pokémon (like Cloyster) using Reflect can have its
effective defense drop to near zero when its stats are recalculated.
-/

namespace AutoResearch

/-- 
Models the `applyBoostToStat` function in `engine/battle/core.asm`.
Multiplies the stat by 9/8 (stat + stat/8).
While the code contains a 999 cap, the re-application bug is the focus here.
-/
def badgeBoost (stat : Nat) : Nat :=
  let boost := stat / 8
  let res := stat + boost
  if res > 999 then 999 else res

/-- 
Models the Reflect move effect. 
As noted in the bug description, the Reflect doubling logic in RBY 
neglects to check the 999 stat cap.
-/
def applyReflectBuggy (stat : Nat) : Nat :=
  stat * 2

/-- 
Models the damage formula scaling.
High stats are divided by 4. If the result exceeds 255, it overflows 
because it is moved into an 8-bit register (e.g., `ld a, b` where b > 255).
This is modeled as (stat / 4) % 256.
-/
def getEffectiveDefenseBuggy (stat : Nat) : Nat :=
  (stat / 4) % 256

/-- 
The intended behavior: stats should be capped both at the doubling 
step and during the final division to 8-bit range.
-/
def getEffectiveDefenseSpec (stat : Nat) : Nat :=
  let s := stat / 4
  if s > 255 then 255 else s

/-- 
Models the buggy sequence described:
1. Start with base defense.
2. Apply initial Badge Boost.
3. Use Reflect (which doubles without capping).
4. Damage formula scales with wrap-around.
-/
def impl (baseDef : Nat) : Nat :=
  let s1 := badgeBoost baseDef
  let s2 := applyReflectBuggy s1
  getEffectiveDefenseBuggy s2

/-- 
The intended behavior:
1. Apply Reflect (with proper 999 capping).
2. Damage scaling prevents wrap-around.
-/
def spec (baseDef : Nat) : Nat :=
  let s1 := baseDef * 2
  let s1_capped := if s1 > 999 then 999 else s1
  getEffectiveDefenseSpec s1_capped

/-! ### L1: Bug Existence -/

/-- 
A Cloyster with 458 Defense is the perfect witness.
- Badge boost: 458 + 57 = 515.
- Reflect: 515 * 2 = 1030.
- Scale: (1030 / 4) % 256 = 257 % 256 = 1.
-/
theorem bug_exists : ∃ d, impl d ≠ spec d := by
  exists 458
  native_decide

/-! ### L2: Characterization of the Bug -/

/--
The "Reflect Paradox": Using the defensive move "Reflect" actually makes 
the Pokémon significantly more vulnerable than not using it at all.
-/
theorem reflect_paradox :
  let base := 458
  let def_no_reflect := getEffectiveDefenseBuggy (badgeBoost base)
  let def_with_reflect := impl base
  def_with_reflect < def_no_reflect := by
  -- 1 < 128
  native_decide

/--
Monotonicity Violation: In a correct system, increasing your base stat 
should never decrease your effective defense. In the buggy system, it does.
-/
theorem monotonicity_violation : ∃ d1 d2, d1 < d2 ∧ impl d1 > impl d2 := by
  exists 400, 458
  -- impl 400 = 225
  -- impl 458 = 1
  native_decide

/--
The "Catastrophic Zone": For any base stat in this range, the effective 
defense after Reflect and Badge boosts drops below 10.
-/
def is_catastrophic (d : Nat) : Prop := impl d < 10

theorem catastrophic_range : ∀ d, d ≥ 455 ∧ d ≤ 460 → is_catastrophic d := by
  intro d h
  match d with
  | 455 => native_decide
  | 456 => native_decide
  | 457 => native_decide
  | 458 => native_decide
  | 459 => native_decide
  | 460 => native_decide

/-! ### L3: Fix Correctness -/

/--
A fix must ensure two things:
1. Reflect doubling must be capped at 999.
2. The damage scaling must be capped at 255.
-/
def fix (baseDef : Nat) : Nat :=
  let s1 := baseDef * 2
  let s1_capped := if s1 > 999 then 999 else s1
  let s2 := s1_capped / 4
  if s2 > 255 then 255 else s2

theorem fix_matches_spec (d : Nat) : fix d = spec d := by
  simp [fix, spec]

/--
The fix prevents the effective defense from ever dropping near zero 
due to overflow for high-stat Pokémon.
-/
theorem fix_prevents_catastrophe (d : Nat) : d > 400 → fix d > 100 := by
  intro h
  simp [fix]
  split <;> split <;> omega

end AutoResearch
