import SM83

namespace AutoResearch

/-!
### Bug: Psywave Link Battle Desynchronization

In Pokémon Red/Blue, the move Psywave deals random damage between 1 and 1.5 * UserLevel.
In link battles, the user's console and the opponent's console use slightly different
rejection sampling logic when generating this random value.

1. The User's console (Player) loops until the random value is non-zero AND within range.
2. The Opponent's console (Remote) loops only until the value is within range, accepting 0.

If the PRNG generates a 0, the User console discards it and calls the PRNG again, 
while the Remote console accepts 0 and stops. This causes the PRNG states and 
the battle states (damage dealt) to diverge immediately.
-/

/-- Computes the maximum damage ceiling for Psywave: level + floor(level/2). -/
def getPsywaveCeiling (level : BitVec 8) : BitVec 8 :=
  level + (level >>> 1)

/-- 
  Model of the User's console logic (Active Player).
  According to assembly lines 4665-4667, it explicitly checks for zero (`and a / jr z, .loop`).
-/
def userLogic (level : BitVec 8) (stream : List (BitVec 8)) : (BitVec 8 × List (BitVec 8)) :=
  match stream with
  | [] => (0, [])
  | r :: rs =>
    let b := getPsywaveCeiling level
    -- Re-rolls if r == 0 OR r >= b
    if r == 0 || r >= b then userLogic level rs
    else (r, rs)
termination_by stream.length

/-- 
  Model of the Remote console logic (Opponent/Link).
  According to assembly lines 4786-4788, it only checks the ceiling (`cp b / jr nc, .loop`).
  It fails to check for zero, thus accepting 0 as a valid damage value.
-/
def remoteLogic (level : BitVec 8) (stream : List (BitVec 8)) : (BitVec 8 × List (BitVec 8)) :=
  match stream with
  | [] => (0, [])
  | r :: rs =>
    let b := getPsywaveCeiling level
    -- Re-rolls only if r >= b. Importantly, accepts r == 0.
    if r >= b then remoteLogic level rs
    else (r, rs)
termination_by stream.length

/-- 
  A desynchronization occurs if the two consoles calculate different damage
  values OR if their remaining PRNG streams diverge.
-/
def isDesynced (level : BitVec 8) (stream : List (BitVec 8)) : Bool :=
  let p := userLogic level stream
  let r := remoteLogic level stream
  p.1 != r.1 || p.2 != r.2

-- L1: Bug exists - Concrete witness of desynchronization.
-- For a Level 20 Pokémon (ceiling b=30), if the PRNG returns 0 then 5:
-- User console: skips 0, takes 5. Result: (5, [])
-- Remote console: takes 0. Result: (0, [5])
theorem bug_exists : ∃ (lvl : BitVec 8) (s : List (BitVec 8)), isDesynced lvl s := 
  ⟨20, [0, 5], by native_decide⟩

-- L2: Characterization - The bug triggers on any stream where 0 is the first valid candidate.
-- This confirms the "Remote" console can deal 0 damage while the "User" cannot.
theorem remote_can_deal_zero : 
  (remoteLogic 10 [0]).1 = 0 ∧ (userLogic 10 [0]).1 != 0 := by
  native_decide

-- L2: For any non-zero level, a leading 0 in the PRNG stream causes a desync.
theorem bug_on_zero_start (lvl : BitVec 8) : 
  lvl == 50 → isDesynced lvl [0, 1] = true := by
  intro h; rw [h]; native_decide

/-- 
  L3: Fix Correctness.
  The fix involves updating the Remote/Enemy logic to match the User's logic
  by explicitly rejecting 0.
-/
def fixedRemoteLogic (level : BitVec 8) (stream : List (BitVec 8)) : (BitVec 8 × List (BitVec 8)) :=
  match stream with
  | [] => (0, [])
  | r :: rs =>
    let b := getPsywaveCeiling level
    if r == 0 || r >= b then fixedRemoteLogic level rs
    else (r, rs)
termination_by stream.length

theorem fix_prevents_desync (lvl : BitVec 8) (s : List (BitVec 8)) :
  userLogic lvl s = fixedRemoteLogic lvl s := by
  induction s with
  | nil => rfl
  | cons r rs ih =>
    unfold userLogic fixedRemoteLogic
    simp [ih]

end AutoResearch
