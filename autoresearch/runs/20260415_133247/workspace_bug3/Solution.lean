import SM83

namespace AutoResearch

/-- 
In Pokémon Red, `25 percent` is a macro evaluating to 63.
The instruction `cp 25 percent + 1` (equivalent to `cp 64`) sets the carry flag
if the random roll in register A is less than 64. 
The subsequent `ret nc` returns if the roll is 64 or greater, 
meaning the AI proceeds to heal if the roll is in the range [0, 63].
-/
def BLAINE_THRESHOLD : BitVec 8 := BitVec.ofNat 8 64

/-- 
Blaine's AI implementation (Buggy).
As seen in `engine/battle/trainer_ai.asm`, Blaine's routine jumps directly
to `AIUseSuperPotion` after the random roll check, entirely skipping any 
verification of the Pokémon's current HP (such as `AICheckIfHPBelowFraction`).
-/
def impl (hp maxHP : BitVec 16) (roll : BitVec 8) : Bool :=
  roll.ult BLAINE_THRESHOLD

/-- 
Standard Healing AI Specification (Correct).
A restorative item should only be used if the random roll succeeds AND 
the Pokémon's current HP is strictly less than its maximum HP.
-/
def spec (hp maxHP : BitVec 16) (roll : BitVec 8) : Bool :=
  roll.ult BLAINE_THRESHOLD && hp.ult maxHP

/-- 
L1: Bug Existence.
Blaine will use a Super Potion even when his Pokémon is at full HP (e.g., 100/100).
Witness: HP=100, MaxHP=100, Roll=0 (passes the 25% check).
-/
theorem bug_exists : ∃ hp maxHP roll, impl hp maxHP roll ≠ spec hp maxHP roll :=
  ⟨BitVec.ofNat 16 100, BitVec.ofNat 16 100, BitVec.ofNat 8 0, by native_decide⟩

/-- 
L2: Bug Characterization.
Blaine's AI behavior diverges from the specification if and only if the random roll
is successful (roll < 64) but the Pokémon is already at full health (hp >= maxHP).
-/
theorem bug_iff (hp maxHP : BitVec 16) (roll : BitVec 8) :
  impl hp maxHP roll ≠ spec hp maxHP roll ↔ (roll.ult BLAINE_THRESHOLD ∧ ¬(hp.ult maxHP)) := by
  unfold impl spec
  cases (roll.ult BLAINE_THRESHOLD) <;> cases (hp.ult maxHP) <;> simp

/-- 
L2: Wasteful Action Property.
At maximum health, any successful roll causes Blaine to perform a healing action (impl = true)
which the specification identifies as unnecessary (spec = false).
-/
theorem blaine_wastes_at_full_hp (maxHP : BitVec 16) (roll : BitVec 8) :
  roll.ult BLAINE_THRESHOLD → impl maxHP maxHP roll = true ∧ spec maxHP maxHP roll = false := by
  intro h
  unfold impl spec
  simp [h, BitVec.lt_irrefl]

/-- 
L3: Fix Correctness.
A corrected implementation (fix) includes the missing HP check before 
applying the probability threshold.
-/
def fix (hp maxHP : BitVec 16) (roll : BitVec 8) : Bool :=
  if hp.ult maxHP then roll.ult BLAINE_THRESHOLD else false

theorem fix_is_correct (hp maxHP : BitVec 16) (roll : BitVec 8) :
  fix hp maxHP roll = spec hp maxHP roll := by
  unfold fix spec
  cases (hp.ult maxHP) <;> cases (roll.ult BLAINE_THRESHOLD) <;> simp

/-- 
L4: Relational/Efficiency Analysis.
We model the effective HP gain from using a Super Potion (heals up to 50 HP).
We prove that Blaine's buggy implementation results in exactly 0 HP gain 
when triggered at full health, effectively wasting a turn.
-/
def hp_gain (healed : Bool) (hp maxHP : BitVec 16) : Nat :=
  if healed then
    let h := hp.toNat
    let m := maxHP.toNat
    (if h + 50 > m then m else h + 50) - h
  else 0

theorem blaine_efficiency_loss (maxHP : BitVec 16) (roll : BitVec 8) :
  roll.ult BLAINE_THRESHOLD → 
  hp_gain (impl maxHP maxHP roll) maxHP maxHP = 0 := by
  intro h
  unfold impl hp_gain
  simp [h]

/--
L4: Safety Property.
The specification (and the fix) ensures that no restorative item is ever 
consumed if the HP gain would be zero due to being at full health.
-/
theorem spec_never_wastes (hp maxHP : BitVec 16) (roll : BitVec 8) :
  hp = maxHP → spec hp maxHP roll = false := by
  intro h_full
  unfold spec
  simp [h_full, BitVec.lt_irrefl]

end AutoResearch

