import SM83

namespace AutoResearch

/--
Blaine's AI implementation in Pokémon Red.
The assembly logic at `BlaineAI` performs a 25% probability check:
  cp 25 percent + 1
  ret nc
  jp AIUseSuperPotion
This translates to: if roll < 65, use Super Potion. 
Crucially, it jumps to use the potion without calling `AICheckIfHPBelowFraction` 
or any other routine to verify the current HP of the Pokémon.
-/
def impl (hp : BitVec 16) (maxHP : BitVec 16) (roll : BitVec 8) : Bool :=
  roll < 65

/--
The intended behavior for a healing AI (Spec).
A standard healing AI should only consider using a restorative item if 
the Pokémon's current HP is below a certain threshold (e.g., its maximum).
-/
def spec (hp : BitVec 16) (maxHP : BitVec 16) (roll : BitVec 8) : Bool :=
  roll < 65 && hp < maxHP

/-- 
L1: Bug Existence.
Blaine will use a Super Potion even when his Pokémon is at full HP.
Witness: HP=100, MaxHP=100, Roll=10 (successful roll).
-/
theorem bug_exists : ∃ (hp maxHP : BitVec 16) (roll : BitVec 8), impl hp maxHP roll ≠ spec hp maxHP roll :=
  ⟨100, 100, 10, by native_decide⟩

/--
L2: Bug Characterization.
Blaine's AI behaves incorrectly if and only if the random roll is successful (roll < 65)
but the Pokémon does not actually need healing (current HP >= MaxHP).
-/
theorem bug_iff (hp maxHP : BitVec 16) (roll : BitVec 8) :
  impl hp maxHP roll ≠ spec hp maxHP roll ↔ (roll < 65 ∧ ¬(hp < maxHP)) := by
  unfold impl spec
  simp [Bool.and_eq_true]
  cases (roll < 65)
  · simp
  · simp

/--
L2: Specific case - Always bugged at full health on successful roll.
If the Pokémon is at full health and the roll is within the 25% chance, 
the actual implementation will heal while the specification says it shouldn't.
-/
theorem bug_at_full_hp (maxHP : BitVec 16) (roll : BitVec 8) :
  roll < 65 → impl maxHP maxHP roll = true ∧ spec maxHP maxHP roll = false := by
  intro h
  unfold impl spec
  simp [h]
  have h_not_lt : ¬(maxHP < maxHP) := by
    intro h_lt
    exact (BitVec.lt_irrefl maxHP h_lt)
  exact h_not_lt

/--
L3: Fix Correctness.
A fixed implementation that checks if the Pokémon needs healing (HP < MaxHP)
before committing to use the Super Potion.
-/
def fix (hp : BitVec 16) (maxHP : BitVec 16) (roll : BitVec 8) : Bool :=
  if hp < maxHP then roll < 65 else false

theorem fix_correct (hp maxHP : BitVec 16) (roll : BitVec 8) :
  fix hp maxHP roll = spec hp maxHP roll := by
  unfold fix spec
  cases (hp < maxHP) <;> cases (roll < 65) <;> rfl

end AutoResearch
