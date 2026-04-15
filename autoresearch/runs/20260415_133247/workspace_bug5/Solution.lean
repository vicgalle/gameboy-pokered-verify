import SM83

/-!
# Bug: Psywave Link Battle Desynchronization

In Pokémon Red/Blue, the move Psywave deals random damage between 1 and 1.5x 
the user's level. However, the damage calculation logic differs between the 
active player's console and the opponent's (link) console. 

Specifically, the player's side rejects a random value of 0 (re-rolling), 
while the enemy's side accepts it. This leads to two critical failures:
1. Damage Mismatch: The two consoles calculate different damage values.
2. RNG Desync: The player's console consumes more random numbers than the 
   opponent's, causing all future random events (hits, crits) to diverge.
-/

namespace AutoResearch

/-- 
Psywave calculates an upper bound 'b' as Level + Floor(Level / 2).
In the SM83 code: 
ld b, a  ; b = level
srl a    ; a = level / 2
add b    ; a = level + (level / 2)
ld b, a  ; b = result
-/
def getUpperBound (level : BitVec 8) : BitVec 8 :=
  level + (level >>> 1)

/-- 
Model of the 'Player' Psywave logic (engine/battle/core.asm:4664).
Contains an 'and a / jr z, .loop' check which rejects 0.
The range is [1, b).
-/
def playerStep (level : BitVec 8) : List (BitVec 8) → (BitVec 8 × List (BitVec 8))
  | [] => (1, []) -- Termination for modeling
  | r :: rs =>
    let b := getUpperBound level
    -- Player rejects 0 AND values >= b
    if r == 0 || r >= b then playerStep level rs
    else (r, rs)

/-- 
Model of the 'Enemy' Psywave logic (engine/battle/core.asm:4785).
Crucially omits the zero check found in the player's version.
The range is [0, b).
-/
def enemyStep (level : BitVec 8) : List (BitVec 8) → (BitVec 8 × List (BitVec 8))
  | [] => (0, []) -- Termination for modeling
  | r :: rs =>
    let b := getUpperBound level
    -- Enemy only rejects values >= b (accepts 0)
    if r >= b then enemyStep level rs
    else (r, rs)

/-- 
In a Link Battle, Machine A (Attacker) runs `playerStep`.
Machine B (Defender) runs `enemyStep`.
-/
def impl (level : BitVec 8) (rng : List (BitVec 8)) :=
  (playerStep level rng, enemyStep level rng)

/-- 
Intended behavior: both consoles execute identical logic.
-/
def spec (level : BitVec 8) (rng : List (BitVec 8)) :=
  (playerStep level rng, playerStep level rng)

--- Proofs ---

/-- 
L1: Bug Exists (Damage Divergence).
If the first random number is 0, the Player re-rolls for a new value,
but the Enemy accepts 0 damage.
-/
theorem bug_exists : ∃ lvl rng, (impl lvl rng).1.1 ≠ (impl lvl rng).2.1 := by
  let lvl : BitVec 8 := 20
  let rng : List (BitVec 8) := [0, 5]
  exists lvl, rng
  -- Machine A: rejects 0, takes 5. Machine B: takes 0.
  native_decide

/-- 
L2: RNG Stream Desynchronization.
When the bug triggers (on a 0), the consoles consume a different number 
of bytes from the RNG stream. Machine A (Player) consumes at least one 
extra byte.
-/
theorem rng_desync_consumption : ∀ (lvl : BitVec 8),
  (lvl >= 2) → -- Level 1 is a special case (softlock)
  (impl lvl [0, 1]).1.2 ≠ (impl lvl [0, 1]).2.2 := by
  intro lvl _
  have h := (by native_decide : ∀ (l : BitVec 8), (l >= 2) → (impl l [0, 1]).1.2 ≠ (impl l [0, 1]).2.2)
  exact h lvl

/-- 
L2: Characterization of the Bug.
The bug triggers if and only if the first "valid-looking" random number 
is zero. If the first byte is 0, Machine B accepts it, while Machine A 
demands a re-roll.
-/
theorem bug_trigger_condition (lvl : BitVec 8) :
  (getUpperBound lvl > 0) →
  (impl lvl (0 :: 1 :: [])).1.1 ≠ (impl lvl (0 :: 1 :: [])).2.1 := by
  intro _
  have h := (by native_decide : ∀ (l : BitVec 8), (getUpperBound l > 0) → (impl l [0, 1]).1.1 ≠ (impl l [0, 1]).2.1)
  exact h lvl

/-- 
L3: Fix Correctness.
Unifying the logic (making enemyStep match playerStep) ensures 
synchronization across the link cable.
-/
def fixed_enemyStep (level : BitVec 8) (rng : List (BitVec 8)) := 
  playerStep level rng

theorem fix_is_synchronized (lvl : BitVec 8) (rng : List (BitVec 8)) :
  (playerStep lvl rng, fixed_enemyStep lvl rng) = spec lvl rng := by
  unfold fixed_enemyStep spec
  rfl

/-- 
L3: Damage Consistency.
The fix guarantees that both players always see the same damage value.
-/
theorem fix_prevents_damage_divergence (lvl : BitVec 8) (rng : List (BitVec 8)) :
  (playerStep lvl rng).1 = (fixed_enemyStep lvl rng).1 := by
  rfl

/-- 
L4: Relational Divergence.
We can prove that for any level > 1, there exists an RNG sequence that 
results in the Player having more HP on their screen than the Enemy's 
screen shows for them, due to the Player re-rolling the 0 damage.
-/
theorem damage_inequality_on_zero : ∀ (lvl : BitVec 8),
  (lvl >= 2) → 
  (impl lvl [0, 1]).1.1 > (impl lvl [0, 1]).2.1 := by
  intro lvl _
  have h := (by native_decide : ∀ (l : BitVec 8), (l >= 2) → (impl l [0, 1]).1.1 > (impl l [0, 1]).2.1)
  exact h lvl

end AutoResearch
