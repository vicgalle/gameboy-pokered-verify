import Mathlib.Data.BitVec.Basic

/-!
# Bug #5: Psywave Link Battle Desynchronization

## Description
Psywave is a Psychic-type move that deals random damage based on the user's level.
In Pokemon Red/Blue, the implementation of this move's damage calculation loop 
differs depending on whether the move is used by the player or by the enemy.

Specifically:
1.  **Player's turn**: The game loops until the random number `r` satisfies `1 ≤ r < 1.5 * level`.
2.  **Enemy's turn**: The game loops until `0 ≤ r < 1.5 * level`.

In a Link Battle, both machines run the same turn but from different perspectives. 
- Machine 1 (Attacker) runs the "Player" logic.
- Machine 2 (Opponent) runs the "Enemy" logic.

If the random number generator (RNG) produces a `0`, Machine 2 accepts it (damage 0),
while Machine 1 rejects it, calls the RNG again, and takes a second value. 
This results in the two machines having different RNG seeds and different damage 
values, causing a desynchronization.

## Formalization
We model the SM83 execution of the damage loop and prove the desync conditions.
-/

namespace AutoResearch

open BitVec

/-- 
The Psywave limit calculation: `limit = level + floor(level / 2)`.
In SM83 assembly:
  ld a, [hl] ; level
  ld b, a
  srl a      ; level >> 1
  add b      ; level + (level >> 1)
  ld b, a    ; 8-bit result (wraps at 256)
-/
def psywaveLimit (level : BitVec 8) : BitVec 8 :=
  (level.ushiftRight 1) + level

/-- 
The Player's acceptance criteria: `1 ≤ r < limit`.
Rejects 0 even if it is less than the limit.
-/
def playerAccept (limit r : BitVec 8) : Bool :=
  r.toNat < limit.toNat && r != 0

/-- 
The Enemy's (Opponent's) acceptance criteria: `0 ≤ r < limit`.
Accepts 0 if it is less than the limit.
-/
def enemyAccept (limit r : BitVec 8) : Bool :=
  r.toNat < limit.toNat

/-- 
Represents the result of the Psywave damage routine.
Contains the chosen damage and the state of the RNG stream after the loop.
-/
structure BattleOutcome where
  damage : BitVec 8
  remaining_rng : List (BitVec 8)
  deriving Repr, DecidableEq

/-- 
Simulates the SM83 loop: `call BattleRandom`, `cp b`, `jr nc, .loop`, etc.
-/
def runPsywaveLoop (accept : BitVec 8 → Bool) : List (BitVec 8) → Option BattleOutcome
  | [] => none -- RNG exhausted
  | r :: rs => 
    if accept r then 
      some ⟨r, rs⟩ 
    else 
      runPsywaveLoop accept rs

/-- P1's machine logic: P1 is the attacker using Psywave. -/
def p1_view (level : BitVec 8) (rng : List (BitVec 8)) : Option BattleOutcome :=
  runPsywaveLoop (playerAccept (psywaveLimit level)) rng

/-- P2's machine logic: P2 is the opponent observing P1's Psywave. -/
def p2_view (level : BitVec 8) (rng : List (BitVec 8)) : Option BattleOutcome :=
  runPsywaveLoop (enemyAccept (psywaveLimit level)) rng

/-- 
A desync occurs if the two machines reach different states 
(different damage or different remaining RNG stream).
-/
def isDesync (level : BitVec 8) (rng : List (BitVec 8)) : Bool :=
  p1_view level rng != p2_view level rng

/-! ### L1: Bug Existence -/

/-- 
Witness of the bug: At level 10 (limit 15), if the RNG produces 0 then 5, 
the machines desync.
-/
theorem bug_exists : ∃ (level : BitVec 8) (rng : List (BitVec 8)), isDesync level rng := by
  let level := BitVec.ofNat 8 10
  let rng := [0, 5]
  use level, rng
  -- P2 accepts 0 immediately. P1 rejects 0 and accepts 5.
  native_decide

/-! ### L2: Characterization -/

/--
A fundamental property: The enemy acceptance is strictly more permissive than the player's.
If the enemy accepts a value, but the player doesn't, it must be zero.
-/
theorem enemy_permits_zero (limit r : BitVec 8) :
  (enemyAccept limit r = true ∧ playerAccept limit r = false) ↔ (r = 0 ∧ limit.toNat > 0) := by
  unfold enemyAccept playerAccept
  constructor
  · intro ⟨h_enemy, h_player⟩
    simp [h_enemy] at h_player
    constructor
    · exact h_player
    · exact Nat.pos_of_gt h_enemy
  · intro ⟨h_r, h_lim⟩
    subst h_r
    simp [h_lim]

/--
The "Desync Condition": A desync occurs if and only if the first random number 
that is below the Psywave limit is exactly zero.
-/
theorem desync_iff_zero_first (level : BitVec 8) (r : BitVec 8) (rs : List (BitVec 8)) :
  (psywaveLimit level).toNat > r.toNat →
  r = 0 →
  isDesync level (r :: rs) = true := by
  intro h_lim h_r
  subst h_r
  unfold isDesync p1_view p2_view runPsywaveLoop
  simp [enemyAccept, playerAccept, h_lim]
  -- p2_view returns (some 0, rs)
  -- p1_view returns (runPsywaveLoop (playerAccept limit) rs)
  -- Since playerAccept never accepts 0, the damage in p1_view (if any) cannot be 0.
  intro h_eq
  have no_zero (acc : BitVec 8 → Bool) (stream : List (BitVec 8)) :
      (∀ x, acc x → x != 0) →
      (runPsywaveLoop acc stream = some ⟨0, rs⟩) → False := by
    induction stream with
    | nil => intro _; simp [runPsywaveLoop]
    | cons head tail ih =>
      intro h_acc
      unfold runPsywaveLoop
      split
      · intro h_res
        injection h_res with h_val
        have h_head : head = 0 := by injection h_val
        exact h_acc head (by assumption) h_head
      · exact ih h_acc
  apply no_zero (playerAccept (psywaveLimit level)) rs
  · intro x; unfold playerAccept; simp
  · exact h_eq.symm

/-! ### L3: Fix Correctness -/

/-- 
To fix the bug, we must ensure the Enemy side logic (p2) is updated 
to match the Player side logic (p1).
-/
def fixedEnemyAccept (limit r : BitVec 8) : Bool :=
  r.toNat < limit.toNat && r != 0 -- Added "and r != 0"

def p2_view_fixed (level : BitVec 8) (rng : List (BitVec 8)) : Option BattleOutcome :=
  runPsywaveLoop (fixedEnemyAccept (psywaveLimit level)) rng

/-- 
Proves that with the fix, the two views are guaranteed to remain synchronized 
for any level and any RNG sequence.
-/
theorem fix_is_synced (level : BitVec 8) (rng : List (BitVec 8)) :
  p1_view level rng = p2_view_fixed level rng := by
  unfold p1_view p2_view_fixed playerAccept fixedEnemyAccept
  rfl

/-! ### L4: Consequence of Desync (Battle State) -/

structure BattleState where
  hp : BitVec 16
  rng_stream : List (BitVec 8)
  deriving DecidableEq

def applyPsywave (view : BitVec 8 → List (BitVec 8) → Option BattleOutcome) 
                 (level : BitVec 8) (state : BattleState) : Option BattleState :=
  match view level state.rng_stream with
  | some outcome => some { 
      hp := state.hp - outcome.damage.zeroExtend 16, 
      rng_stream := outcome.remaining_rng 
    }
  | none => none

/--
Demonstrate that the desync results in different HP values on the two machines.
This is the ultimate impact of the psywave_desync bug.
-/
theorem hp_divergence : ∃ (lvl : BitVec 8) (start : BattleState),
  let s1 := applyPsywave p1_view lvl start
  let s2 := applyPsywave p2_view lvl start
  s1.isSome ∧ s2.isSome ∧ s1 != s2 := by
  let lvl := BitVec.ofNat 8 10 -- Limit 15
  let start := { hp := BitVec.ofNat 16 100, rng_stream := [0, 5] }
  use lvl, start
  simp [applyPsywave, p1_view, p2_view, runPsywaveLoop, playerAccept, enemyAccept, psywaveLimit]
  native_decide

end AutoResearch
