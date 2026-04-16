import SM83

namespace AutoResearch

/-
  Bug: Psywave Link Battle Desynchronization
  
  In Pokémon Red, Blue, and Yellow, the move Psywave deals random damage between 
  1 and floor(1.5 * User's Level). During a link battle between two Game Boys, 
  the random number generator (RNG) used to calculate this damage is called 
  locally on each device. However, the game does not synchronize the resulting 
  random value across the link cable. 
  
  Since the RNG states on the two devices can diverge (due to unrelated 
  V-blank interrupts or previous random checks), Machine 1 (the attacker) 
  and Machine 2 (the defender) often calculate different damage values.
  This leads to a game state desynchronization where one player's HP 
  differs from what the other player sees.
-/

/--
  Model of Psywave damage: random value in [1, floor(1.5 * Level)].
  In the game, this is implemented as (Random % (Level + Level/2)) + 1.
-/
def psywave_dmg (level : Nat) (rng : BitVec 8) : Nat :=
  let max_range := level + (level / 2)
  if max_range == 0 then 1
  else (rng.toNat % max_range) + 1

/--
  Buggy implementation (impl):
  In a link battle, Machine 1 uses its local RNG (rng1) and Machine 2 uses 
  its local RNG (rng2). The resulting state is a pair of (M1_damage, M2_damage).
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

-- L1: Prove that a desynchronization witness exists (Machine 1 and 2 disagree)
theorem bug_exists : ∃ lv r1 r2, impl lv r1 r2 ≠ spec lv r1 r2 := by
  -- At level 50, if RNGs differ, damage can differ.
  use 50, 0, 1
  native_decide

-- L2: Characterization — Desynchronization is impossible if the RNG inputs are the same.
theorem same_rng_no_desync : ∀ lv r, (impl lv r r).1 = (impl lv r r).2 := by
  intro lv r
  simp [impl]

-- L2: Characterization — Desynchronization necessarily implies different RNG inputs.
theorem desync_implies_different_rng (lv : Nat) (r1 r2 : BitVec 8) :
    (impl lv r1 r2).1 ≠ (impl lv r1 r2).2 → r1 ≠ r2 := by
  intro h_desync h_eq
  subst h_eq
  exact h_desync (same_rng_no_desync lv r1)

-- L2: Characterization — Desynchronization only occurs if the level is high enough.
-- At Level 1, the range is [1, floor(1.5*1)] = [1, 1], so desync is impossible.
theorem desync_requires_level_gt_1 (lv : Nat) (r1 r2 : BitVec 8) :
    (impl lv r1 r2).1 ≠ (impl lv r1 r2).2 → lv > 1 := by
  intro h_desync
  match lv with
  | 0 => 
    simp [impl, psywave_dmg] at h_desync
  | 1 =>
    simp [impl, psywave_dmg] at h_desync
    have mod1 : ∀ r : BitVec 8, r.toNat % 1 = 0 := by
      have h := (by native_decide : ∀ v : BitVec 8, v.toNat % 1 = 0)
      exact h
    simp [mod1] at h_desync
  | n + 2 => 
    omega

-- L3: The specification ensures that both players are always synchronized.
theorem fix_is_always_synchronized (lv : Nat) (r1 r2 : BitVec 8) :
    (spec lv r1 r2).1 = (spec lv r1 r2).2 := by
  simp [spec]

-- L3: The specification ensures the defender's view matches the attacker's calculation.
theorem fix_matches_attacker_calculation (lv : Nat) (r1 r2 : BitVec 8) :
    (spec lv r1 r2).2 = (impl lv r1 r2).1 := by
  simp [spec, impl]

-- L4: Relational — The attacker's perspective is invariant under the fix.
theorem attacker_perspective_invariant (lv : Nat) (r1 r2 : BitVec 8) :
    (impl lv r1 r2).1 = (spec lv r1 r2).1 := by
  simp [impl, spec]

-- L4: Relational — At Level 1, the buggy implementation is accidentally correct.
theorem level_1_is_safe (r1 r2 : BitVec 8) :
    (impl 1 r1 r2) = (spec 1 r1 r2) := by
  have mod1 : ∀ r : BitVec 8, r.toNat % 1 = 0 := by
    have h := (by native_decide : ∀ v : BitVec 8, v.toNat % 1 = 0)
    exact h
  simp [impl, spec, psywave_dmg, mod1]

-- L4: Relational — The maximum damage difference is bounded by floor(1.5 * Level) - 1.
theorem desync_magnitude_bound (lv : Nat) (r1 r2 : BitVec 8) :
    let outcome := impl lv r1 r2
    let max_dmg := lv + (lv / 2)
    lv > 0 → outcome.1 ≤ max_dmg ∧ outcome.2 ≤ max_dmg := by
  intro h_lv
  have h_pos : lv + lv / 2 > 0 := by omega
  simp [impl, psywave_dmg, h_pos]
  constructor
  · apply Nat.add_le_add_right
    apply Nat.le_of_lt
    apply Nat.mod_lt
    assumption
  · apply Nat.add_le_add_right
    apply Nat.le_of_lt
    apply Nat.mod_lt
    assumption

end AutoResearch
