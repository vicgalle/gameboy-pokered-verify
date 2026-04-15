import SM83

/-!
# Bug #5: Psywave Link Battle Desynchronization

## Description
In Pokémon Red/Blue, Psywave is a move that deals random damage. The damage range is 
intended to be `[1, 1.5 * Level)`. In link battles, both Game Boys execute their 
own damage calculation logic.

## The Bug
There is a discrepancy in how the random roll is handled between the code path 
used by the "Attacker" (usually the player's console) and the "Defender" (the 
opponent's console) during damage calculation.

1.  **Attacker Path**: Explicitly rejects a random roll of `0` with `and a / jr z, .loop`.
2.  **Defender Path**: Only checks if the roll is less than the upper bound `b`. It 
    accepts `0`.

## Consequences
- **Damage Mismatch**: If the Game Boy rolls a 0, the defender's state records 0 
  damage, while the attacker's state rejects it and rolls again, recording a 
  non-zero value.
- **PRNG Desync**: The attacker consumes an additional value from the shared PRNG 
  stream. Since the PRNG state is now different on both consoles, every subsequent 
  random event (hits, crits, effects) will diverge, leading to a complete breakdown 
  of the link battle state.
- **Level 171 Softlock**: The 8-bit calculation of `level + (level / 2)` overflows 
  at Level 171 (`171 + 85 = 256 ≡ 0`), causing an infinite loop.

-/

namespace AutoResearch

open BitVec

/-- 
Calculates the upper bound `b` for Psywave damage.
Matches assembly:
  ld a, [hl] ; level
  ld b, a
  srl a      ; level / 2
  add b      ; level + level/2 (8-bit)
-/
def psywaveMaxDamage (level : BitVec 8) : BitVec 8 :=
  let half := level >>> 1
  level + half

/-- 
Models the Attacker's Psywave routine.
Rejects 0 (`jr z`) AND values >= b.
-/
def attackerLogic (level : BitVec 8) (stream : List (BitVec 8)) : Option (BitVec 8 × List (BitVec 8)) :=
  match stream with
  | [] => none
  | r :: rs =>
    let b := psywaveMaxDamage level
    -- Rejects 0 (Snippet line 4666) AND rejects r >= b (Standard logic)
    if r == 0 || r >= b then attackerLogic level rs
    else some (r, rs)
termination_by stream.length

/-- 
Models the Defender's Psywave routine.
Crucially missing the zero-check.
-/
def defenderLogic (level : BitVec 8) (stream : List (BitVec 8)) : Option (BitVec 8 × List (BitVec 8)) :=
  match stream with
  | [] => none
  | r :: rs =>
    let b := psywaveMaxDamage level
    -- Only rejects r >= b (Snippet line 4788)
    if r >= b then defenderLogic level rs
    else some (r, rs)
termination_by stream.length

/-! ### L1: Bug Existence -/

/--
A concrete witness: Level 100 Pokémon (b=150).
If the PRNG returns 0 then 15, the consoles diverge.
-/
theorem bug_exists : ∃ (lvl : BitVec 8) (s : List (BitVec 8)), 
  attackerLogic lvl s ≠ defenderLogic lvl s := by
  let lvl := BitVec.ofNat 8 100
  let s := [0, 15]
  exists lvl, s
  -- Attacker rejects 0, takes 15. Result: some (15, [])
  -- Defender accepts 0. Result: some (0, [15])
  native_decide

/-! ### L2: Characterization -/

/--
The "Level 171" overflow bug: at level 171, the upper bound `b` becomes 0.
-/
theorem level_171_overflow : psywaveMaxDamage (BitVec.ofNat 8 171) = 0 := by
  native_decide

/--
When the upper bound is 0, both routines fail to find a valid number 
and consume the entire stream (infinite loop in assembly).
-/
theorem logic_fails_at_171 (s : List (BitVec 8)) :
  attackerLogic (BitVec.ofNat 8 171) s = none ∧ 
  defenderLogic (BitVec.ofNat 8 171) s = none := by
  have h_zero : psywaveMaxDamage (BitVec.ofNat 8 171) = 0 := by native_decide
  induction s with
  | nil => constructor <;> rfl
  | cons head tail ih =>
    unfold attackerLogic defenderLogic
    simp [h_zero]
    -- BitVec 8 is always >= 0
    have always_ge (x : BitVec 8) : x >= 0 := by 
      simp [GE.ge, BitVec.le_def, BitVec.toNat_zero, Nat.zero_le]
    simp [always_ge]
    exact ih

/-! ### L3: Fix Correctness -/

/--
A corrected defender logic that matches the attacker logic.
-/
def fixedDefenderLogic (level : BitVec 8) (stream : List (BitVec 8)) : Option (BitVec 8 × List (BitVec 8)) :=
  match stream with
  | [] => none
  | r :: rs =>
    let b := psywaveMaxDamage level
    if r == 0 || r >= b then fixedDefenderLogic level rs
    else some (r, rs)
termination_by stream.length

theorem fix_is_correct (lvl : BitVec 8) (s : List (BitVec 8)) :
  attackerLogic lvl s = fixedDefenderLogic lvl s := by
  induction s with
  | nil => rfl
  | cons head tail ih =>
    unfold attackerLogic fixedDefenderLogic
    simp [ih]

/-! ### L4: Link Battle Divergence -/

structure BattleSystemState where
  damage : BitVec 8
  consumed : Nat

/-- 
Simulates the outcome of a Psywave call on one console.
Returns damage and how many random numbers were pulled.
-/
def runPsywave (logic : BitVec 8 → List (BitVec 8) → Option (BitVec 8 × List (BitVec 8)))
               (lvl : BitVec 8) (s : List (BitVec 8)) : Option BattleSystemState :=
  match logic lvl s with
  | some (dmg, rem) => some ⟨dmg, s.length - rem.length⟩
  | none => none

/--
Formal proof of desynchronization:
If the first roll is 0 and the second roll is valid (1 to b-1), 
then the damage AND the PRNG state (consumed count) will differ.
-/
theorem psywave_desync_proof (lvl : BitVec 8) (next_val : BitVec 8) (rest : List (BitVec 8)) :
  let b := psywaveMaxDamage lvl
  (b > 0 ∧ next_val > 0 ∧ next_val < b) →
  let s := 0 :: next_val :: rest
  let attacker := runPsywave attackerLogic lvl s
  let defender := runPsywave defenderLogic lvl s
  ∃ a_state d_state, attacker = some a_state ∧ defender = some d_state ∧ 
    a_state.damage ≠ d_state.damage ∧ 
    a_state.consumed ≠ d_state.consumed := by
  intro b_val
  let s := 0 :: next_val :: rest
  unfold runPsywave attackerLogic defenderLogic
  -- Attacker rejects 0, looks at next_val. next_val is valid.
  have h_att : attackerLogic lvl s = some (next_val, rest) := by
    unfold attackerLogic
    simp [b_val.left, b_val.right.left, b_val.right.right]
  -- Defender accepts 0.
  have h_def : defenderLogic lvl s = some (0, next_val :: rest) := by
    unfold defenderLogic
    simp [b_val.left]
  
  exists ⟨next_val, 2⟩, ⟨0, 1⟩
  simp [h_att, h_def]
  -- Show damage is different (next_val > 0)
  constructor
  · exact (BitVec.ne_of_gt b_val.right.left).symm
  · simp

end AutoResearch
