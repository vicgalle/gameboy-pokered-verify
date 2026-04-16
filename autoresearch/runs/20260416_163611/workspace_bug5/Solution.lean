import SM83

namespace AutoResearch

/--
Psywave Damage Calculation:
In Pokémon Gen 1, Psywave damage is a random value between 1 and floor(1.5 * Level).
Mathematically, the upper limit is `Level + floor(Level / 2)`.
-/
def psywave_limit (level : BitVec 8) : Nat :=
  let l := level.toNat
  l + (l / 2)

def psywave_damage (level : BitVec 8) (rng_val : BitVec 8) : Nat :=
  let limit := psywave_limit level
  if limit = 0 then 1
  else (rng_val.toNat % limit) + 1

/--
A Game Boy's local view of a battle state.
During a link battle, both Game Boys (connected via link cable) run their own
simulations. In Gen 1, RNG seeds often drift due to VBlank timing differences
and memory noise, though the game tries to keep them somewhat aligned.
-/
structure GameBoyState where
  enemy_hp : Nat
  rng_seed : BitVec 8
  deriving DecidableEq

/--
The buggy link battle implementation for Psywave.
The Game Boy's code for Psywave performs a local damage roll on each machine 
independently. If internal RNG seeds have drifted, the damage differs,
leading to desynchronization.
-/
def buggy_step (level : BitVec 8) (s1 s2 : GameBoyState) : (GameBoyState × GameBoyState) :=
  let d1 := psywave_damage level s1.rng_seed
  let d2 := psywave_damage level s2.rng_seed
  ( { enemy_hp := s1.enemy_hp - d1, rng_seed := s1.rng_seed + 1 },
    { enemy_hp := s2.enemy_hp - d2, rng_seed := s2.rng_seed + 1 } )

/--
The specification for a link battle move:
The random value should be synchronized across the cable. 
Both machines must apply the exact same damage value calculated by the 'master'.
-/
def spec_step (level : BitVec 8) (s1 s2 : GameBoyState) : (GameBoyState × GameBoyState) :=
  let shared_rng := s1.rng_seed -- Assuming s1 is the master
  let d := psywave_damage level shared_rng
  ( { enemy_hp := s1.enemy_hp - d, rng_seed := s1.rng_seed + 1 },
    { enemy_hp := s2.enemy_hp - d, rng_seed := s1.rng_seed + 1 } )

-- L1: Prove that the bug causes desynchronization (Witness).
theorem exists_psywave_desync : ∃ (lvl : BitVec 8) (s1 s2 : GameBoyState),
  s1.enemy_hp = s2.enemy_hp ∧ 
  (buggy_step lvl s1 s2).1.enemy_hp ≠ (buggy_step lvl s1 s2).2.enemy_hp := by
  let lvl := BitVec.ofNat 8 50
  let s1 := GameBoyState.mk 100 (BitVec.ofNat 8 10)
  let s2 := GameBoyState.mk 100 (BitVec.ofNat 8 20)
  use lvl, s1, s2
  -- limit = 50 + 25 = 75. 
  -- d1 = (10 % 75) + 1 = 11. hp1 = 100 - 11 = 89.
  -- d2 = (20 % 75) + 1 = 21. hp2 = 100 - 21 = 79.
  simp [buggy_step, psywave_damage, psywave_limit]
  native_decide

-- L2: Universal characterization: Level 1 always syncs because variance is zero.
-- At Level 1, limit is 1 + 0 = 1. (rng % 1) is always 0.
theorem level_one_always_syncs (s1 s2 : GameBoyState) :
  s1.enemy_hp = s2.enemy_hp →
  (buggy_step (BitVec.ofNat 8 1) s1 s2).1.enemy_hp = (buggy_step (BitVec.ofNat 8 1) s1 s2).2.enemy_hp := by
  intro h
  have : ∀ r1 r2 : BitVec 8, psywave_damage (BitVec.ofNat 8 1) r1 = psywave_damage (BitVec.ofNat 8 1) r2 := by
    intro r1 r2
    simp [psywave_damage, psywave_limit]
  simp [buggy_step, h, this]

-- L2: Characterization: The desync happens if and only if the RNG results differ modulo the level limit.
theorem desync_iff_rng_mod_limit_differs (lvl : BitVec 8) (s1 s2 : GameBoyState) :
  s1.enemy_hp = s2.enemy_hp →
  ((buggy_step lvl s1 s2).1.enemy_hp ≠ (buggy_step lvl s1 s2).2.enemy_hp ↔ 
   psywave_damage lvl s1.rng_seed ≠ psywave_damage lvl s2.rng_seed) := by
  intro h
  simp [buggy_step, h]

-- L3: The specification (the fix) prevents desynchronization for all possible levels and seeds.
theorem spec_guarantees_sync (lvl : BitVec 8) (s1 s2 : GameBoyState) :
  s1.enemy_hp = s2.enemy_hp →
  (spec_step lvl s1 s2).1.enemy_hp = (spec_step lvl s1 s2).2.enemy_hp := by
  intro h_hp
  simp [spec_step, h_hp]

-- L4: Relational divergence: Desync causes one player to win while the other continues.
-- In Pokemon Gen 1, if HP reaches 0, the Pokemon faints.
theorem battle_outcome_desync_witness : ∃ (lvl : BitVec 8) (s1 s2 : GameBoyState),
  s1.enemy_hp = s2.enemy_hp ∧
  (buggy_step lvl s1 s2).1.enemy_hp = 0 ∧
  (buggy_step lvl s1 s2).2.enemy_hp > 0 := by
  let lvl := BitVec.ofNat 8 20 -- limit = 20 + 10 = 30
  -- s1: dmg = (24 % 30) + 1 = 25. hp = 20 - 25 = 0 (Nat subtraction)
  -- s2: dmg = (4 % 30) + 1 = 5. hp = 20 - 5 = 15
  let s1 := GameBoyState.mk 20 (BitVec.ofNat 8 24)
  let s2 := GameBoyState.mk 20 (BitVec.ofNat 8 4)
  use lvl, s1, s2
  simp [buggy_step, psywave_damage, psywave_limit]
  native_decide

-- L4: HP Divergence is bounded by the max possible Psywave damage (approx 1.5 * Level).
theorem divergence_upper_bound (lvl : BitVec 8) (s1 s2 : GameBoyState) :
  s1.enemy_hp = s2.enemy_hp →
  let s1' := (buggy_step lvl s1 s2).1
  let s2' := (buggy_step lvl s1 s2).2
  (s1'.enemy_hp > s2'.enemy_hp → s1'.enemy_hp - s2'.enemy_hp < psywave_limit lvl) ∧
  (s2'.enemy_hp > s1'.enemy_hp → s2'.enemy_hp - s1'.enemy_hp < psywave_limit lvl) := by
  intro h_hp
  simp only [buggy_step, h_hp]
  constructor
  · intro _
    let d1 := psywave_damage lvl s1.rng_seed
    let d2 := psywave_damage lvl s2.rng_seed
    have h1 : d1 ≥ 1 := by simp [psywave_damage]; split <;> omega
    have h2 : d2 ≥ 1 := by simp [psywave_damage]; split <;> omega
    have h1_lim : d1 ≤ psywave_limit lvl := by
      simp [psywave_damage]
      split
      · omega
      · apply Nat.mod_lt_of_pos; omega
    -- If HP1 > HP2, then Damage2 > Damage1.
    -- The difference is (HP - D1) - (HP - D2) = D2 - D1.
    -- Since D2 <= limit and D1 >= 1, D2 - D1 <= limit - 1 < limit.
    omega
  · intro _
    let d1 := psywave_damage lvl s1.rng_seed
    let d2 := psywave_damage lvl s2.rng_seed
    have h1 : d1 ≥ 1 := by simp [psywave_damage]; split <;> omega
    have h2 : d2 ≥ 1 := by simp [psywave_damage]; split <;> omega
    have h2_lim : d2 ≤ psywave_limit lvl := by
      simp [psywave_damage]
      split
      · omega
      · apply Nat.mod_lt_of_pos; omega
    omega

end AutoResearch

