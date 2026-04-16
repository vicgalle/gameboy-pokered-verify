import SM83

namespace AutoResearch

/-
  Bug: Psywave Link Battle Desynchronization
  
  In Pokemon Red/Blue, the move Psywave deals random damage between 1 and 1.5 times 
  the user's level. In a link battle, the random number generator (RNG) used for 
  Psywave's damage is not synchronized between the two Game Boys. This results in 
  one player seeing one damage value while the other player's Game Boy calculates 
  a different value, leading to a game state desynchronization.
-/

/--
  Model of Psywave damage: random value from 1 to floor(1.5 * Level).
  The game generates a random index in [0, floor(1.5 * level) - 1] and adds 1.
-/
def psywave_dmg (level : Nat) (rng : BitVec 8) : Nat :=
  let max_range := level + (level / 2)
  if max_range == 0 then 1
  else (rng.toNat % max_range) + 1

/--
  Buggy implementation (impl):
  In a link battle, both Game Boys run the code locally.
  Machine 1 uses its local RNG state (rng1), and Machine 2 uses its local RNG state (rng2).
  Since the RNG result is not transmitted, the damage values diverge.
-/
def impl (level : Nat) (rng1 rng2 : BitVec 8) : (Nat × Nat) :=
  (psywave_dmg level rng1, psywave_dmg level rng2)

/--
  Correct implementation (spec):
  In a synchronized link battle, the damage value calculated by the attacker 
  (Machine 1) is transmitted to the opponent (Machine 2), ensuring both see 
  the same damage value.
-/
def spec (level : Nat) (rng1 rng2 : BitVec 8) : (Nat × Nat) :=
  let dmg := psywave_dmg level rng1
  (dmg, dmg)

-- L1: Prove that a desynchronization exists (Machine 1 and 2 disagree)
-- Witness: Level 50, Machine 1 rolls a 0 index, Machine 2 rolls a 1 index.
theorem bug_exists : ∃ lv r1 r2, impl lv r1 r2 ≠ spec lv r1 r2 := by
  -- Use level 50, Machine 1 rolls index 0, Machine 2 rolls index 1
  use 50, 0, 1
  native_decide

-- L2: Universal characterization — if level > 1, different RNG inputs can cause desync.
-- This shows the bug is possible for any level above 1.
theorem desync_possible_for_valid_levels (lv : Nat) (h : lv > 1) : 
    ∃ r1 r2, (impl lv r1 r2).1 ≠ (impl lv r1 r2).2 := by
  use 0, 1
  simp [impl, psywave_dmg]
  -- For lv > 1, level + level/2 is at least 3.
  have h_range : lv + lv / 2 > 1 := by omega
  -- 0 % X = 0
  have h_mod0 : 0 % (lv + lv / 2) = 0 := Nat.zero_mod _
  -- 1 % X = 1 when X > 1
  have h_mod1 : 1 % (lv + lv / 2) = 1 := Nat.mod_eq_of_lt h_range
  simp [h_mod0, h_mod1]

-- L3: Fix ensures the two machines are always synchronized regardless of local RNG state
theorem fix_is_always_consistent (lv : Nat) (r1 r2 : BitVec 8) : 
    (spec lv r1 r2).1 = (spec lv r1 r2).2 := by
  simp [spec]

-- L3: The fix still preserves the damage value from the attacker's perspective
theorem fix_matches_attacker_view (lv : Nat) (r1 r2 : BitVec 8) :
    (spec lv r1 r2).1 = (impl lv r1 r2).1 := by
  simp [spec, impl]

-- L4: Relational — The bug causes desynchronization (divergence) while the spec does not.
def is_desynced (outcome : Nat × Nat) : Prop := outcome.1 ≠ outcome.2

theorem impl_allows_desync : ∃ lv r1 r2, is_desynced (impl lv r1 r2) := by
  use 10, 0, 1
  native_decide

theorem spec_prevents_desync : ∀ lv r1 r2, ¬ is_desynced (spec lv r1 r2) := by
  intro lv r1 r2
  simp [is_desynced, spec]

-- L4: At Level 1, the bug does not trigger because the random range is size 1.
theorem level_1_is_safe : ∀ r1 r2, ¬ is_desynced (impl 1 r1 r2) := by
  intro r1 r2
  simp [is_desynced, impl, psywave_dmg]
  -- level 1 + 1/2 = 1. Anything % 1 is 0.
  have h_mod (r : BitVec 8) : r.toNat % 1 = 0 := Nat.mod_one _
  simp [h_mod]

end AutoResearch
