import SM83

namespace PsywaveDesync

open BitVec

/-- 
  Psywave damage bound calculation: level + floor(level / 2).
  Matches the Game Boy SM83 assembly in Pokémon Red:
  4658-	ld a, [hl]  ; Load attacker level
  4659-	ld b, a     ; b = level
  4660-	srl a       ; a = level / 2
  4661-	add b       ; a = level + level / 2
  4662-	ld b, a     ; b = level * 1.5
-/
def getBound (level : BitVec 8) : BitVec 8 :=
  level + (level.ushiftRight 1)

/-- 
  The Player's Psywave damage calculation (local routine).
  The code erroneously rejects a random value of 0 (`jr z, .loop`) and
  rejects values greater than or equal to the calculated bound.
  This enforces a damage range of [1, b).
-/
def playerStep : (level : BitVec 8) → (rng : List (BitVec 8)) → Option (BitVec 8 × List (BitVec 8))
  | _, [] => none
  | level, r :: rs =>
    let b := getBound level
    if r == 0 || r >= b then
      playerStep level rs
    else
      some (r, rs)

/-- 
  The Enemy's Psywave damage calculation (remote routine).
  The code correctly checks only if the random value is less than the bound.
  It does NOT reject 0, meaning it can result in 0 damage.
  This enforces a damage range of [0, b).
-/
def enemyStep : (level : BitVec 8) → (rng : List (BitVec 8)) → Option (BitVec 8 × List (BitVec 8))
  | _, [] => none
  | level, r :: rs =>
    let b := getBound level
    if r >= b then
      enemyStep level rs
    else
      some (r, rs)

/-- 
  L1: Bug Witness.
  At level 10, if the first random number is 0, the results diverge.
  The Enemy machine accepts 0 damage and consumes one RNG value.
  The Player machine rejects 0, rerolls, and consumes a second RNG value.
-/
theorem bug_exists : ∃ (level : BitVec 8) (rng : List (BitVec 8)),
    (playerStep level rng).isSome ∧ 
    (enemyStep level rng).isSome ∧ 
    (playerStep level rng) ≠ (enemyStep level rng) := by
  -- Let level = 10, and RNG sequence = [0, 5]
  let level : BitVec 8 := BitVec.ofNat 8 10
  let rng : List (BitVec 8) := [BitVec.ofNat 8 0, BitVec.ofNat 8 5]
  use level, rng
  native_decide

/--
  L2: Core Property of the Bug.
  The Player's Psywave routine can never result in 0 damage, 
  whereas the Enemy's routine can.
-/
theorem player_never_zero (level : BitVec 8) (rng : List (BitVec 8)) (val : BitVec 8) (rest : List (BitVec 8)) :
    playerStep level rng = some (val, rest) → val ≠ 0 := by
  induction rng with
  | nil => 
    unfold playerStep; intro h; cases h
  | cons r rs ih =>
    unfold playerStep
    intro h
    split at h
    · -- Case: r == 0 || r >= b (re-roll)
      exact ih h
    · -- Case: success
      injection h with h_res
      injection h_res with h_val _
      subst h_val
      rename_i h_cond
      simp at h_cond
      -- h_cond is (r == 0) = false ∧ (r >= b) = false
      intro h_zero
      subst h_zero
      have : (0 : BitVec 8) == 0 = true := by native_decide
      simp [this] at h_cond

/--
  L2: Level 1 Softlock (Infinite Loop).
  At level 1, the bound is 1 (1 + 1/2 = 1). The only 8-bit value < 1 is 0.
  Since the player routine rejects 0 (jr z) AND rejects values >= 1 (cp b),
  it loops forever. On a finite list, this results in `none` (exhausted RNG).
-/
theorem level_1_player_softlock (rng : List (BitVec 8)) :
    playerStep 1 rng = none := by
  induction rng with
  | nil => rfl
  | cons r rs ih =>
    unfold playerStep
    -- 1 + (1 >> 1) = 1
    have h_bound : getBound 1 = 1 := by native_decide
    rw [h_bound]
    -- Prove that (r == 0 || r >= 1) is always true for any BitVec 8
    have h_always_true : (r == 0 || r >= 1) = true := by
      by_cases hr : r = 0
      · simp [hr]
      · have : r >= 1 := by
          apply BitVec.le_of_toNat_le
          simp [BitVec.toNat_ofNat]
          match h_nat : r.toNat with
          | 0 => 
            have : r = 0 := by apply BitVec.toNat_inj; rw [h_nat]; rfl
            contradiction
          | n + 1 => omega
        simp [this]
    rw [h_always_true]
    exact ih

/--
  L3: Fix Correctness.
  Aligning the Player's logic with the Enemy's logic (removing the `jr z` check)
  ensures both Game Boys remain synchronized during the damage calculation.
-/
def playerStep_fixed := enemyStep

theorem fix_removes_desync (level : BitVec 8) (rng : List (BitVec 8)) :
    playerStep_fixed level rng = enemyStep level rng := rfl

/--
  L4: Relational Divergence (RNG Consumption).
  The bug causes the two systems to consume different numbers of values from
   the synchronized RNG stream. If the stream starts with 0, the player routine 
  "lags" behind by one random number, desynchronizing all future random events.
-/
theorem rng_consumption_desync (level : BitVec 8) (rs : List (BitVec 8)) :
    level = 10 → 
    ∃ v1 r1 v2 r2,
      playerStep level (0 :: 5 :: rs) = some (v1, r1) ∧
      enemyStep level (0 :: 5 :: rs) = some (v2, r2) ∧
      r1 ≠ r2 := by
  intro h_lev
  -- At level 10, bound is 15.
  -- Enemy takes 0, leaves [5, ...]
  -- Player rejects 0, takes 5, leaves [...]
  use 5, rs, 0, (5 :: rs)
  subst h_lev
  constructor
  · native_decide
  · constructor
    · native_decide
    · simp

end PsywaveDesync
