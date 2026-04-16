import SM83

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Gameplay Description
Bide is a move that stores damage taken over several turns and deals double that 
amount back. In Pokémon Red/Blue, the 16-bit damage counter `wDamageAccumulator` 
must be reset to zero when a Pokémon faints.

The routine `ResetEnemyStatModifiers` (called when an enemy Pokémon faints) contains
 a bug where it only clears the high byte of the 16-bit damage accumulator, leaving 
the low byte intact. In contrast, the routine for a player's Pokémon fainting 
correctly clears both bytes.

In a link battle, this creates a desynchronization:
1. Console A (Player): Pokémon X faints -> Clears both bytes.
2. Console B (Enemy): Pokémon X faints -> Clears only the high byte.
If Bide had accumulated damage that wasn't a multiple of 256, the two consoles 
now disagree on the damage counter, causing subsequent Bide calculations and 
the overall battle state to diverge.
-/

namespace AutoResearch
open SM83

/-- 
  The address of the Bide damage accumulator (wDamageAccumulator) in Pokémon Red/Blue.
  It is a 16-bit Big Endian value in RAM.
  Address: 0xD0D8 (High Byte), 0xD0D9 (Low Byte).
-/
def wDamageAccumulatorHi : BitVec 16 := 0xD0D8
def wDamageAccumulatorLo : BitVec 16 := 0xD0D9

/--
  `impl` models the buggy routine used when an enemy Pokémon faints.
  It only resets the high byte of the damage accumulator.
-/
def impl (s : CPUState) : CPUState :=
  s.writeMem wDamageAccumulatorHi 0

/--
  `spec` models the intended behavior (as seen in the player fainting routine).
  It correctly resets both the high and low bytes of the damage accumulator.
-/
def spec (s : CPUState) : CPUState :=
  let s' := s.writeMem wDamageAccumulatorHi 0
  s'.writeMem wDamageAccumulatorLo 0

/-! ### Level 1: Concrete Witness
  We show that if the damage accumulator has a non-zero low byte, the buggy 
  implementation results in a state different from the specification.
-/
theorem L1_desync_witness : ∃ s : CPUState, impl s ≠ spec s := by
  -- Create an initial state where Bide has accumulated 1 damage (Low byte = 1).
  let s0 := defaultState
  let s := s0.writeMem wDamageAccumulatorLo 1
  use s
  intro h_eq
  -- If the states were equal, their memory at the low byte address must be equal.
  have h_mem := congr_arg (fun st => st.readMem wDamageAccumulatorLo) h_eq
  simp [impl, spec, wDamageAccumulatorHi, wDamageAccumulatorLo] at h_mem
  -- 0xD0D9 != 0xD0D8, so (writeMem Hi 0) doesn't change Lo.
  have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
  simp [h_neq] at h_mem
  -- 1 = 0 is a contradiction.
  contradiction

/-! ### Level 2: Universal Characterization
  The buggy implementation produces a state functionally equivalent to the specification
  if and only if the low byte of the damage accumulator was already zero.
-/
theorem L2_characterization (s : CPUState) :
  (∀ addr, (impl s).readMem addr = (spec s).readMem addr) ↔ s.readMem wDamageAccumulatorLo = 0 := by
  constructor
  · -- Forward: If the routines result in the same memory, the low byte must have been 0.
    intro h
    specialize h wDamageAccumulatorLo
    simp [impl, spec, wDamageAccumulatorHi, wDamageAccumulatorLo] at h
    have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
    simp [h_neq] at h
    exact h
  · -- Backward: If the low byte is 0, both routines effectively clear the whole counter.
    intro h addr
    simp [impl, spec]
    have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
    if ha : addr = wDamageAccumulatorLo then
      -- If addr is Lo, impl leaves it as 0 (by assumption), spec sets it to 0.
      subst ha
      simp [h, h_neq]
    else if hb : addr = wDamageAccumulatorHi then
      -- If addr is Hi, both set it to 0.
      subst hb
      simp
    else
      -- All other addresses are unchanged by both routines.
      simp [ha, hb]

/-! ### Level 3: The Fix
  The fix is to ensure both bytes are cleared, matching the specification exactly.
-/
def fixed_impl (s : CPUState) : CPUState :=
  let s' := s.writeMem wDamageAccumulatorHi 0
  s'.writeMem wDamageAccumulatorLo 0

theorem L3_fix_is_correct (s : CPUState) :
  ∀ addr, (fixed_impl s).readMem addr = (spec s).readMem addr := by
  intro addr
  rfl

/-! ### Level 4: Relational Desync (Link Battle)
  In a link battle, two consoles refer to the same event. We prove that if they 
  start synchronized but with non-zero Bide damage, the faint event causes their 
  states to diverge because they run different routines.
-/
theorem L4_link_battle_desync (s_a s_b : CPUState)
  (h_synced : ∀ addr, s_a.readMem addr = s_b.readMem addr)
  (h_bide_damage : s_a.readMem wDamageAccumulatorLo ≠ 0) :
  ∃ addr, (spec s_a).readMem addr ≠ (impl s_b).readMem addr := by
  -- The consoles diverge at the low byte address (0xD0D9).
  use wDamageAccumulatorLo
  simp [spec, impl, wDamageAccumulatorHi, wDamageAccumulatorLo]
  have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
  simp [h_neq]
  -- Console A (running spec) has 0 at the low byte.
  -- Console B (running impl) has the old value.
  -- Since they were synced, s_b's old value is s_a's old value, which is non-zero.
  rw [h_synced]
  exact h_bide_damage

end AutoResearch
