/-
  PokeredBugs/Proofs/PsywaveDesync.lean — Formal verification of the Psywave link desync.

  ## The Bug
  In link battles, both Game Boys share a synchronized list of random numbers.
  Psywave's damage calculation has TWO different implementations:

  Player Psywave (core.asm 4664-4670):
    .loop
      call BattleRandom
      and a             ; test if 0
      jr z, .loop       ; REJECT 0 → range [1, b)
      cp b
      jr nc, .loop      ; reject >= b

  Enemy Psywave (core.asm 4785-4789):
    .loop
      call BattleRandom
      cp b
      jr nc, .loop      ; reject >= b → range [0, b)
                         ; NO zero check!

  The player's loop rejects 0, consuming an extra random number from the shared
  list. The enemy's loop accepts 0. When a 0 appears in the random list, the
  two sides consume different numbers of random values, causing the shared RNG
  index to desynchronize. All subsequent random draws diverge.

  ## What We Prove
  1. The damage ranges differ (player: [1,b), enemy: [0,b))
  2. When the RNG produces 0, the player consumes more random numbers
  3. This causes the shared RNG index to desync (concrete examples)
  4. The desync propagates — subsequent draws give different values
  5. The fix (making both loops identical) preserves sync
-/
import SM83

namespace PokeredBugs

/-! ### Model: Shared RNG State -/

/-- A shared random number list used in link battles.
    Both Game Boys index into this list sequentially. -/
structure LinkRNG where
  list : List (BitVec 8)
  index : Nat
  deriving Repr, DecidableEq

/-- Draw the next random number, advancing the index. -/
def LinkRNG.next (rng : LinkRNG) : BitVec 8 × LinkRNG :=
  let val := rng.list.getD rng.index 0
  (val, { rng with index := rng.index + 1 })

/-! ### Model: Psywave Damage Loops -/

/-- Player's Psywave loop: reject 0 and values >= b.
    Accepted range: [1, b). May consume multiple random numbers.
    Returns (damage, updated RNG state).
    Fuel bounds the recursion (10 matches the link battle list size). -/
def psywavePlayer (b : BitVec 8) (rng : LinkRNG) (fuel : Nat := 10) :
    BitVec 8 × LinkRNG :=
  match fuel with
  | 0 => (1, rng)
  | fuel + 1 =>
    let (val, rng') := rng.next
    if val == 0 then
      psywavePlayer b rng' fuel       -- reject 0, draw again
    else if val.toNat ≥ b.toNat then
      psywavePlayer b rng' fuel       -- reject >= b, draw again
    else
      (val, rng')                      -- accept: val ∈ [1, b)

/-- Enemy's Psywave loop: reject only values >= b.
    Accepted range: [0, b). Accepts 0 as valid damage. -/
def psywaveEnemy (b : BitVec 8) (rng : LinkRNG) (fuel : Nat := 10) :
    BitVec 8 × LinkRNG :=
  match fuel with
  | 0 => (0, rng)
  | fuel + 1 =>
    let (val, rng') := rng.next
    if val.toNat ≥ b.toNat then
      psywaveEnemy b rng' fuel         -- reject >= b, draw again
    else
      (val, rng')                      -- accept: val ∈ [0, b)

/-! ### Proof 1: Different Damage Ranges -/

/-- The player can never deal 0 damage with Psywave. -/
theorem player_never_zero (b : BitVec 8) (rng : LinkRNG) (fuel : Nat)
    (_hb : b.toNat ≥ 2) :
    (psywavePlayer b rng fuel).1 ≠ 0 := by
  induction fuel generalizing rng with
  | zero => simp [psywavePlayer]
  | succ n ih =>
    simp only [psywavePlayer]
    split
    · exact ih _
    · split
      · exact ih _
      · rename_i h1 _
        simp at h1
        exact h1

/-- The enemy CAN deal 0 damage — when the first random value is 0. -/
theorem enemy_can_deal_zero :
    let b : BitVec 8 := 75
    let rng : LinkRNG := ⟨[0], 0⟩
    (psywaveEnemy b rng).1 = 0 := by
  native_decide

/-! ### Proof 2: RNG Index Divergence -/

/-- Core desync theorem: when the first random value is 0 and the second
    is in [1, b), player consumes 2 values but enemy consumes only 1.
    Level 50 example: b = 75, RNG list = [0, 5]. -/
theorem desync_level50 :
    let b : BitVec 8 := 75
    let rng : LinkRNG := ⟨[0, 5], 0⟩
    let (playerDmg, playerRNG) := psywavePlayer b rng
    let (enemyDmg, enemyRNG) := psywaveEnemy b rng
    playerDmg = 5 ∧ enemyDmg = 0 ∧
    playerRNG.index = 2 ∧ enemyRNG.index = 1 := by
  native_decide

/-- Same desync at level 100: b = 150, RNG list = [0, 73]. -/
theorem desync_level100 :
    let b : BitVec 8 := 150
    let rng : LinkRNG := ⟨[0, 73], 0⟩
    let (playerDmg, playerRNG) := psywavePlayer b rng
    let (enemyDmg, enemyRNG) := psywaveEnemy b rng
    playerDmg = 73 ∧ enemyDmg = 0 ∧
    playerRNG.index = 2 ∧ enemyRNG.index = 1 := by
  native_decide

/-- Multiple zeros: if the list starts [0, 0, 5], the player must skip
    BOTH zeros, consuming 3 values while enemy still consumes 1.
    The desync widens with more leading zeros. -/
theorem desync_multiple_zeros :
    let b : BitVec 8 := 75
    let rng : LinkRNG := ⟨[0, 0, 5], 0⟩
    let (playerDmg, playerRNG) := psywavePlayer b rng
    let (enemyDmg, enemyRNG) := psywaveEnemy b rng
    playerDmg = 5 ∧ enemyDmg = 0 ∧
    playerRNG.index = 3 ∧ enemyRNG.index = 1 := by
  native_decide

/-- When the first random value is nonzero and < b, both sides agree.
    No desync occurs. -/
theorem no_desync_when_nonzero :
    let b : BitVec 8 := 75
    let rng : LinkRNG := ⟨[42, 5, 100], 0⟩
    let (playerDmg, playerRNG) := psywavePlayer b rng
    let (enemyDmg, enemyRNG) := psywaveEnemy b rng
    playerDmg = enemyDmg ∧ playerRNG.index = enemyRNG.index := by
  native_decide

/-! ### Proof 3: The Desync Propagates -/

/-- After the Psywave desync, the very next random draw gives different
    values to host and guest. The battle is permanently broken. -/
theorem desync_propagates :
    let b : BitVec 8 := 75
    let rng : LinkRNG := ⟨[0, 5, 42, 100, 7], 0⟩
    let (_, playerRNG) := psywavePlayer b rng
    let (_, enemyRNG) := psywaveEnemy b rng
    -- RNG indices diverged
    playerRNG.index ≠ enemyRNG.index ∧
    -- Next random draw gives different values
    playerRNG.next.1 ≠ enemyRNG.next.1 ∧
    -- And the draw after that
    playerRNG.next.2.next.1 ≠ enemyRNG.next.2.next.1 := by
  native_decide

/-! ### Proof 4: Fix Correctness -/

/-- The fixed Psywave: both sides use the same loop (accept [0, b)). -/
def psywaveFixed (b : BitVec 8) (rng : LinkRNG) (fuel : Nat := 10) :
    BitVec 8 × LinkRNG :=
  psywaveEnemy b rng fuel

/-- With the fix, both sides always produce identical damage and RNG state.
    This is trivially true since they run the same function. -/
theorem fix_preserves_sync (b : BitVec 8) (rng : LinkRNG) :
    psywaveFixed b rng = psywaveEnemy b rng := by
  rfl

/-- The fix means both sides agree even when the list contains zeros. -/
theorem fix_sync_with_zeros :
    let b : BitVec 8 := 75
    let rng : LinkRNG := ⟨[0, 5, 42], 0⟩
    let (fixedDmg, fixedRNG) := psywaveFixed b rng
    let (enemyDmg, enemyRNG) := psywaveEnemy b rng
    fixedDmg = enemyDmg ∧ fixedRNG.index = enemyRNG.index := by
  native_decide

/-! ### Interesting: Damage Asymmetry is Also a Gameplay Bug -/

/-- Even WITHOUT a link battle, the asymmetry means player Psywave and enemy
    Psywave have different damage distributions. The player always does at
    least 1 damage, but the enemy can do 0. This makes the player's Psywave
    strictly better than the enemy's (higher expected damage). -/
theorem player_psywave_strictly_better :
    ∃ b : BitVec 8, ∃ rng : LinkRNG,
      b.toNat ≥ 2 ∧
      (psywavePlayer b rng).1.toNat > (psywaveEnemy b rng).1.toNat := by
  refine ⟨75, ⟨[0], 0⟩, by native_decide, ?_⟩
  native_decide

/-! ### #eval Demonstrations -/

-- Level 50 Pokémon, list starts with 0: DESYNC
#eval
  let b : BitVec 8 := 75
  let rng := LinkRNG.mk [0, 5, 42, 100, 7] 0
  let (pd, pr) := psywavePlayer b rng
  let (ed, er) := psywaveEnemy b rng
  (s!"Player: dmg={pd}, idx={pr.index}", s!"Enemy: dmg={ed}, idx={er.index}")

-- Level 50 Pokémon, list starts with 42: NO DESYNC
#eval
  let b : BitVec 8 := 75
  let rng := LinkRNG.mk [42, 5, 100] 0
  let (pd, pr) := psywavePlayer b rng
  let (ed, er) := psywaveEnemy b rng
  (s!"Player: dmg={pd}, idx={pr.index}", s!"Enemy: dmg={ed}, idx={er.index}")

end PokeredBugs
