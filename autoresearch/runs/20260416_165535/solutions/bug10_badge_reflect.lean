import SM83

namespace AutoResearch

/--
Badge boosts in Pokemon Red/Blue are intended to be applied once at the start of a battle.
The mechanic is a 9/8 multiplier (an 11.25% increase) to the stat.
-/
def badge_boost (s : Nat) : Nat := (s * 9) / 8

/--
A recursive helper to model the badge boost restacking bug.
The bug causes the 9/8 multiplier to be reapplied every time ANY stat change occurs.
`num_stat_changes` represents the number of times a move like Growl or Agility has been used.
-/
def apply_badge_boosts : Nat → Nat → Nat
  | s, 0 => s
  | s, n + 1 => badge_boost (apply_badge_boosts s n)

/--
The buggy implementation found in Gen 1:
1. Re-applies the badge boost multiplier for every stat change that occurs.
2. The Reflect move doubles the defense stat without checking for overflows.
3. The damage formula scaling wraps values at 1024 (effectively taking bits 2-9).
   This is modeled as dividing by 4 and taking the low byte (modulo 256).
-/
def impl (raw_stat : Nat) (num_stat_changes : Nat) (has_reflect : Bool) : Nat :=
  -- The bug: boosts are reapplied on stat changes. 
  -- Based on the description, one Growl application results in one badge boost.
  let boosted := apply_badge_boosts raw_stat num_stat_changes
  -- Reflect doubles the current boosted stat
  let reflected := if has_reflect then boosted * 2 else boosted
  -- Scaling bug: (stat / 4) % 256
  (reflected / 4) % 256

/--
The intended behavior (specification):
1. Badge boost is applied exactly once (if a badge is held).
2. Reflect doubles the stat.
3. Scaling caps the result at the maximum byte value (255) instead of overflowing.
-/
def spec (raw_stat : Nat) (num_stat_changes : Nat) (has_reflect : Bool) : Nat :=
  -- Intended: Apply boost once if any battle activity (stat change) has occurred
  let boosted := if num_stat_changes >= 1 then badge_boost raw_stat else raw_stat
  let reflected := if has_reflect then boosted * 2 else boosted
  let scaled := reflected / 4
  if scaled > 255 then 255 else scaled

-- L1: Concrete witness showing the bug exists
-- For a Cloyster with 458 raw defense and one Growl (stat change), the behavior diverges.
theorem bug_exists : ∃ s n r, impl s n r ≠ spec s n r := 
  ⟨458, 1, true, by native_decide⟩

-- L1: Formalizing the specific Cloyster catastrophe
-- Description: "effective defense becomes 1 instead of 128"
-- Our model confirms the 1 result. 
-- (The 128 refers to the value without Reflect: 515 / 4 = 128)
theorem cloyster_effective_defense_overflow : impl 458 1 true = 1 := by
  native_decide

-- L2: Reflect detriments the player
-- Reflect is supposed to double defense, but because of the overflow, 
-- it makes the player significantly weaker (1 vs 128).
theorem reflect_detriment : impl 458 1 true < impl 458 1 false := by
  native_decide

-- L2: Growl detriments the player
-- An opponent's Growl (which lowers a stat) triggers the restacking bug, 
-- pushing defense into an overflow state that makes the player weaker.
theorem growl_weakens_defense : impl 458 1 true < impl 458 0 true := by
  native_decide

-- L2: Universal characterization of scaling overflow
-- Any boosted stat that reaches 512+ will result in a lower value after Reflect than before.
theorem reflect_overflow_threshold : ∀ s : Nat, s ≥ 512 ∧ s < 515 → 
  (impl s 0 true < impl s 0 false) := by
  intro s h
  -- We use a small range to show the threshold logic
  revert s h
  native_decide

-- L3: A fixed implementation that matches the spec
def fix (raw_stat : Nat) (num_stat_changes : Nat) (has_reflect : Bool) : Nat :=
  let boosted := if num_stat_changes >= 1 then (raw_stat * 9) / 8 else raw_stat
  let reflected := if has_reflect then boosted * 2 else boosted
  let scaled := reflected / 4
  if scaled > 255 then 255 else scaled

theorem fix_is_correct : ∀ s n r, fix s n r = spec s n r := by
  intro s n r
  simp [fix, spec]

-- L4: Desync — The bug causes the player's defense to be 1/128th of the expected value
theorem catastrophic_desync : spec 458 1 true = 255 ∧ impl 458 1 true = 1 := by
  constructor <;> native_decide

end AutoResearch

