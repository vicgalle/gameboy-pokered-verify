import SM83

namespace AutoResearch

/-!
# Bug #5: Psywave Link Battle Desynchronization

## Description
Psywave is a Psychic-type move that deals random damage based on the user's level.
In Pokemon Red/Blue, the implementation of this move's damage calculation loop 
differs depending on whether the move is used by the player or by the enemy.

Specifically:
1.  **Player's turn**: The game loops until the random number `r` satisfies `1 ≤ r < 1.5 * level`. 
    The value `0` is explicitly rejected.
2.  **Enemy's turn**: The game loops until `r < 1.5 * level`. The value `0` is accepted.

In a Link Battle, both machines run the same turn but from different perspectives. 
If Player 1 (P1) uses Psywave:
-   P1's Game Boy runs the "Player" logic.
-   P2's Game Boy runs the "Enemy" logic.

If the random number generator (RNG) produces a `0`, P2's machine accepts it as 
0 damage and proceeds to the next game state. P1's machine, however, rejects it, 
calls the RNG again, and takes a second value. This results in the two machines 
having different RNG seeds and different battle states, causing a desync.
-/

/-- 
Calculates the upper bound for Psywave damage (1.5 * level).
Assembly: 
  ld a, [hl] ; level
  ld b, a
  srl a      ; level / 2
  add b      ; level + level/2
  ld b, a    ; store limit in B
-/
def psywaveLimit (level : BitVec 8) : BitVec 8 :=
  (level.ushiftRight 1) + level

/-- 
Player's acceptance criteria: 1 ≤ r < limit.
Assembly:
  .loop
    call BattleRandom
    cp b       ; compare with limit
    jr nc, .loop ; loop if r >= limit
    and a      ; check if r is 0
    jr z, .loop ; loop if r == 0
-/
def playerAccept (limit : BitVec 8) (r : BitVec 8) : Bool :=
  r.toNat < limit.toNat && r != 0

/-- 
Enemy's acceptance criteria: 0 ≤ r < limit.
Assembly:
  .loop
    call BattleRandom
    cp b       ; compare with limit
    jr nc, .loop ; loop if r >= limit
    ; note: "and a / jr z" check is missing here
-/
def enemyAccept (limit : BitVec 8) (r : BitVec 8) : Bool :=
  r.toNat < limit.toNat

/-- Result of a move's random damage calculation -/
inductive MoveResult where
  | success (damage : BitVec 8) (remaining_rng : List (BitVec 8))
  | failure
  deriving Repr, DecidableEq

/-- 
Simulates the SM83 loop of pulling random numbers until one is accepted.
-/
def runMove (accept : BitVec 8 → Bool) : List (BitVec 8) → MoveResult
  | [] => .failure
  | r :: rs => if accept r then .success r rs else runMove accept rs

/-- P1's machine logic when they use Psywave -/
def p1_view (level : BitVec 8) (rng : List (BitVec 8)) : MoveResult :=
  runMove (playerAccept (psywaveLimit level)) rng

/-- P2's machine logic when their opponent (P1) uses Psywave -/
def p2_view (level : BitVec 8) (rng : List (BitVec 8)) : MoveResult :=
  runMove (enemyAccept (psywaveLimit level)) rng

/-- 
A desync occurs if the two machines reach different states 
(different damage or different remaining RNG seeds).
-/
def isDesync (level : BitVec 8) (rng : List (BitVec 8)) : Bool :=
  p1_view level rng != p2_view level rng

/-! ### L1: Bug Existence -/

/-- 
Prove that a desync can occur given a specific level and RNG sequence.
-/
theorem bug_exists : ∃ (level : BitVec 8) (rng : List (BitVec 8)), isDesync level rng := by
  -- Level 10 means limit is 15.
  -- If RNG gives [0, 5]:
  -- P2 accepts 0. Damage = 0, Remaining RNG = [5].
  -- P1 rejects 0, accepts 5. Damage = 5, Remaining RNG = [].
  let level := BitVec.ofNat 8 10
  let rng := [0, 5]
  use level, rng
  native_decide

/-! ### L2: Characterization -/

/-- 
The machines will always desync if the first random number is 0 
and the level is such that 0 is within the Psywave limit.
-/
theorem desync_on_zero_rng (level : BitVec 8) (rs : List (BitVec 8)) :
  (psywaveLimit level).toNat > 0 →
  isDesync level (0 :: rs) = true := by
  intro h_limit
  unfold isDesync p1_view p2_view runMove
  simp [playerAccept, enemyAccept, h_limit]
  -- p2_view returns success 0 rs
  -- p1_view returns runMove (playerAccept ...) rs
  -- These cannot be equal because playerAccept never accepts 0 as damage.
  intro h_eq
  -- Helper lemma: runMove with playerAccept never returns damage 0
  have no_zero (acc : BitVec 8 → Bool) (stream : List (BitVec 8)) :
      (∀ r, acc r → r != 0) →
      (runMove acc stream = .success 0 rs) → False := by
    induction stream with
    | nil => unfold runMove; intro _ h; cases h
    | cons head tail ih =>
      unfold runMove
      split
      · intro h_acc h_succ
        injection h_succ with h_r _
        exact h_acc head (by assumption) (by simp [h_r])
      · intro h_acc h_succ
        exact ih h_acc h_succ
  apply no_zero (playerAccept (psywaveLimit level)) rs
  · intro r; simp [playerAccept]
  · exact h_eq.symm

/-! ### L3: Fix Correctness -/

/-- 
The fix is to unify the acceptance criteria so that both machines
skip 0, ensuring the RNG seeds stay in sync.
-/
def fixedEnemyAccept (limit : BitVec 8) (r : BitVec 8) : Bool :=
  r.toNat < limit.toNat && r != 0

def p2_view_fixed (level : BitVec 8) (rng : List (BitVec 8)) : MoveResult :=
  runMove (fixedEnemyAccept (psywaveLimit level)) rng

theorem fix_is_synced (level : BitVec 8) (rng : List (BitVec 8)) :
  p1_view level rng = p2_view_fixed level rng := by
  -- Since the acceptance predicates are now identical, the outcomes must match.
  unfold p1_view p2_view_fixed playerAccept fixedEnemyAccept
  rfl

end AutoResearch
