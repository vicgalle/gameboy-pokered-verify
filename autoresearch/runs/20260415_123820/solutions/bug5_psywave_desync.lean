import SM83

/-!
# Bug #5: Psywave Causes Link Battle Desynchronization

In Pokemon Red/Blue, the move Psywave deals random damage based on the user's level.
The damage is calculated as a random value in the range [1, 1.5 * Level) for the player,
but in the range [0, 1.5 * Level) for the opponent.

In a link battle, random numbers are synchronized between consoles. However, because
one console uses the "player" logic (rejecting 0) and the other uses the "enemy" logic
(accepting 0) for the same move, they can pick different values and consume different
amounts of the random number stream, leading to an immediate battle desync.
-/

namespace AutoResearch

open BitVec

/--
Psywave calculates the maximum possible damage `b` as 1.5 * user level.
Assembly implementation:
  ld a, [hl] ; load level
  ld b, a
  srl a      ; divide by 2
  add b      ; level + level/2 = 1.5 * level
-/
def psywaveMaxDamage (level : BitVec 8) : BitVec 8 :=
  level + (level >>> 1)

/--
The logic used by the attacking console (Snippet 1).
It uses rejection sampling to find a value `r` such that `1 ≤ r < b`.
Crucially, it rejects 0 (`and a` / `jr z, .loop`).
-/
def attackerLogic (level : BitVec 8) (stream : List (BitVec 8)) : Option (BitVec 8) :=
  match stream with
  | [] => none
  | r :: rs =>
    let b := psywaveMaxDamage level
    if r != 0 && r < b then some r
    else attackerLogic level rs

/--
The logic used by the defending console for the opponent's move (Snippet 2).
It uses rejection sampling to find a value `r` such that `0 ≤ r < b`.
Crucially, it accepts 0.
-/
def defenderLogic (level : BitVec 8) (stream : List (BitVec 8)) : Option (BitVec 8) :=
  match stream with
  | [] => none
  | r :: rs =>
    let b := psywaveMaxDamage level
    if r < b then some r
    else defenderLogic level rs

/--
A desynchronization occurs when two consoles calculate different damage values
for the same event using the same random entropy stream.
-/
def isDesync (level : BitVec 8) (stream : List (BitVec 8)) : Prop :=
  attackerLogic level stream != defenderLogic level stream

/-! ### L1: Bug Existence -/

theorem bug_exists : ∃ lvl stream, isDesync lvl stream := by
  -- For a level 100 Pokemon, max damage (b) is 150.
  -- If the first random number is 0, the defender accepts 0 damage.
  -- The attacker rejects 0 and consumes the next number (e.g., 10).
  let lvl : BitVec 8 := BitVec.ofNat 8 100
  let stream : List (BitVec 8) := [0, 10]
  exists lvl, stream
  -- Attacker: some 10, Defender: some 0.
  native_decide

/-! ### L2: Characterization -/

/--
A desync always occurs if the first random number that satisfies the range
check (r < b) is 0.
-/
theorem desync_on_zero (lvl : BitVec 8) (rs : List (BitVec 8)) :
  (0 : BitVec 8) < psywaveMaxDamage lvl → isDesync lvl (0 :: rs) := by
  intro h_range
  unfold isDesync attackerLogic defenderLogic
  simp [h_range]
  -- We must prove that attackerLogic (which excludes 0) cannot return 'some 0'
  have no_zero (l : BitVec 8) (s : List (BitVec 8)) : attackerLogic l s ≠ some 0 := by
    induction s with
    | nil => simp [attackerLogic]
    | cons head tail ih =>
      unfold attackerLogic
      split
      · rename_i h_valid
        intro contra
        injection contra with c1
        -- h_valid contains 'head != 0', but 'c1' says 'head = 0'
        simp [c1] at h_valid
      · exact ih
  exact no_zero lvl rs

/-! ### L3: Fix Correctness -/

/--
The fix is to unify the logic so that both consoles use the same rejection range.
Traditionally, the "player" range [1, b) is preferred to prevent 0-damage Psywave.
-/
def fixedDefenderLogic (level : BitVec 8) (stream : List (BitVec 8)) : Option (BitVec 8) :=
  match stream with
  | [] => none
  | r :: rs =>
    let b := psywaveMaxDamage level
    -- Updated to match attackerLogic: reject 0
    if r != 0 && r < b then some r
    else fixedDefenderLogic level rs

/--
The fix prevents desynchronization because both consoles now evaluate the
exact same functional logic.
-/
theorem fix_prevents_desync (lvl : BitVec 8) (stream : List (BitVec 8)) :
  attackerLogic lvl stream = fixedDefenderLogic lvl stream := by
  rfl

end AutoResearch
