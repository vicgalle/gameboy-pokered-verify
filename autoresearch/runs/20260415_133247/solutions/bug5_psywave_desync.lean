import SM83

namespace AutoResearch

/-- 
Psywave damage is calculated based on the user's level. 
The damage range is [0, level * 1.5).
This function models the upper bound calculation: b = level + (level / 2).
-/
def getUpperBound (level : BitVec 8) : BitVec 8 :=
  level + (level >>> 1)

/-- 
Model of the 'Player Attacking' Psywave logic (engine/battle/core.asm:4664).
Crucially, it contains an 'and a / jr z, .loop' check which rejects 0.
This restricts the damage range to [1, b).
-/
def playerStep (level : BitVec 8) : List (BitVec 8) → (BitVec 8 × List (BitVec 8))
  | [] => (1, []) -- Base case for finite RNG lists
  | r :: rs =>
    let b := getUpperBound level
    if r == 0 || r >= b then playerStep level rs
    else (r, rs)

/-- 
Model of the 'Enemy Attacking' Psywave logic (engine/battle/core.asm:4785).
This logic omits the zero check found in the player's version.
This allows the damage range to be [0, b).
-/
def enemyStep (level : BitVec 8) : List (BitVec 8) → (BitVec 8 × List (BitVec 8))
  | [] => (0, []) -- Base case for finite RNG lists
  | r :: rs =>
    let b := getUpperBound level
    if r >= b then enemyStep level rs
    else (r, rs)

/-- 
In a Link Battle, the two consoles run different code for the same move.
Console 1 (Attacker) runs `playerStep`.
Console 2 (Defender) runs `enemyStep`.
The `impl` models this interaction by returning the result for both sides.
-/
def impl (level : BitVec 8) (rng : List (BitVec 8)) :=
  (playerStep level rng, enemyStep level rng)

/-- 
Correct behavior: both players must execute the exact same logic
to ensure the RNG state and damage values remain synchronized.
-/
def spec (level : BitVec 8) (rng : List (BitVec 8)) :=
  (playerStep level rng, playerStep level rng)

/-- L1: Bug Exists.
    A concrete witness where a single Psywave move causes different damage values.
    If the first random value is 0, the player console skips it, but the enemy accepts it.
-/
theorem bug_exists : ∃ lvl rng, (impl lvl rng).1.1 ≠ (impl lvl rng).2.1 := by
  let lvl : BitVec 8 := 20
  let rng : List (BitVec 8) := [0, 5]
  exists lvl, rng
  -- Player: Skip 0 -> Take 5. Enemy: Take 0. 5 != 0.
  native_decide

/-- L2: Universal RNG Desynchronization.
    For any valid level (1-100), if the first random number is 0, 
    the consoles consume a different amount of RNG samples. 
    This desyncs the RNG stream for every subsequent move in the battle.
-/
theorem rng_consumption_desync : ∀ (lvl : BitVec 8),
  (lvl >= 1 && lvl <= 100) →
  (impl lvl [0, 1]).1.2 ≠ (impl lvl [0, 1]).2.2 := by
  -- At lvl 1, b=1. playerStep skips 0, then skips 1 (since 1 >= 1), returns [].
  -- enemyStep accepts 0, returns [1]. [] != [1].
  native_decide

/-- L3: Fix Correctness.
    By making the 'Enemy' side logic match the 'Player' side (rejecting 0),
    the desynchronization is eliminated.
-/
def fixed_enemyStep (level : BitVec 8) (rng : List (BitVec 8)) := 
  playerStep level rng

theorem fix_is_synchronized (lvl : BitVec 8) (rng : List (BitVec 8)) :
  (playerStep lvl rng, fixed_enemyStep lvl rng) = spec lvl rng := by
  unfold fixed_enemyStep spec
  rfl

/-- L3: Damage Consistency.
    The fix ensures that for any input, both sides calculate the same damage.
-/
theorem fix_prevents_damage_divergence (lvl : BitVec 8) (rng : List (BitVec 8)) :
  (playerStep lvl rng).1 = (fixed_enemyStep lvl rng).1 := by
  unfold fixed_enemyStep
  rfl

end AutoResearch
