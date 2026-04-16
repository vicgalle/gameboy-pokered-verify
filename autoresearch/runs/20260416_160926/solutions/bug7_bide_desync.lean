import SM83

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Gameplay Description
Bide is a move that stores damage taken over 2-3 turns and deals double that amount back.
When a Pokemon faints, the Bide damage accumulator (a 16-bit word) should be reset to zero.
In Pokémon Red/Blue, the routine `ResetEnemyStatModifiers` (which handles an enemy fainting)
only clears the high byte of the accumulator, leaving the low byte intact.
The player fainting routine correctly clears both bytes.

In a link battle, this causes a desync:
- Console 1 (where the Pokemon is the "Player") clears both bytes.
- Console 2 (where the same Pokemon is the "Enemy") clears only one byte.
Any subsequent use of Bide will deal different damage on each side, leading to a permanent desync.
-/

namespace AutoResearch
open SM83

/-- The address of the Bide damage accumulator (wDamageAccumulator) in Pokémon Red/Blue.
    It is a 16-bit value (Big Endian) in RAM. -/
def wDamageAccumulatorHi : BitVec 16 := 0xD0D8
def wDamageAccumulatorLo : BitVec 16 := 0xD0D9

/--
  `impl` models the buggy routine used when an enemy Pokemon faints.
  It only resets the high byte of the damage accumulator.
-/
def impl (s : CPUState) : CPUState :=
  s.writeMem wDamageAccumulatorHi 0

/--
  `spec` models the correct behavior (as seen in the player fainting routine).
  It resets both the high and low bytes of the damage accumulator.
-/
def spec (s : CPUState) : CPUState :=
  let s' := s.writeMem wDamageAccumulatorHi 0
  s'.writeMem wDamageAccumulatorLo 0

/-! ### Level 1: Concrete Witness
  We show that if the damage accumulator has a non-zero low byte (e.g., total damage > 255),
  the buggy implementation fails to reach the same state as the specification.
-/
theorem L1_desync_witness : ∃ s : CPUState, impl s ≠ spec s := by
  -- Create an initial state where Bide has accumulated 1 damage (Low byte = 1).
  let s0 := defaultState
  let s := s0.writeMem wDamageAccumulatorLo 1
  use s
  intro h_eq
  -- If the states were equal, their memory at the low byte address must be equal.
  have h_mem := congr_arg (fun st => st.readMem wDamageAccumulatorLo) h_eq
  -- Calculate resulting low-byte values:
  -- impl: (writeMem s Hi 0).readMem Lo = s.readMem Lo (since Lo != Hi)
  -- spec: (writeMem (writeMem s Hi 0) Lo 0).readMem Lo = 0
  simp [impl, spec, readMem, writeMem] at h_mem
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
  · -- Forward: impl ≈ spec -> low byte was 0
    intro h
    specialize h wDamageAccumulatorLo
    simp [impl, spec, readMem, writeMem] at h
    have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
    simp [h_neq] at h
    exact h
  · -- Backward: low byte is 0 -> impl ≈ spec
    intro h addr
    simp [impl, spec, readMem, writeMem]
    if ha : addr = wDamageAccumulatorLo then
      -- If addr is Lo, impl leaves it as s.readMem Lo (which is 0), spec sets it to 0.
      subst ha
      simp [h]
      have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
      simp [h_neq]
    else
      -- If addr is Hi, both set it to 0. If addr is anything else, both leave it as s.readMem addr.
      if hb : addr = wDamageAccumulatorHi then
        subst hb
        simp
      else
        simp [ha, hb]

/-! ### Level 3: The Fix
  The fix is to ensure both bytes are cleared, matching the specification.
-/
def fixed_impl (s : CPUState) : CPUState :=
  let s' := s.writeMem wDamageAccumulatorHi 0
  s'.writeMem wDamageAccumulatorLo 0

theorem L3_fix_is_correct (s : CPUState) :
  ∀ addr, (fixed_impl s).readMem addr = (spec s).readMem addr := by
  intro addr
  rfl

/-! ### Level 4: Relational Desync (Link Battle)
  In a link battle, the Player on Console 1 and the Enemy on Console 2 refer to the
  same Pokémon. We prove that if they start synchronized but Bide has accumulated
  non-zero damage, the faint event causes their memories to permanently diverge
  because one console uses the buggy 'impl' and the other uses the correct 'spec'.
-/
theorem L4_link_battle_desync (s1 s2 : CPUState)
  (h_synced : ∀ addr, s1.readMem addr = s2.readMem addr)
  (h_acc_damage : s1.readMem wDamageAccumulatorLo ≠ 0) :
  ∃ addr, (spec s1).readMem addr ≠ (impl s2).readMem addr := by
  -- The consoles diverge specifically at the low byte address.
  use wDamageAccumulatorLo
  simp [spec, impl, readMem, writeMem]
  have h_neq : wDamageAccumulatorLo ≠ wDamageAccumulatorHi := by decide
  simp [h_neq]
  -- Console 1 clears the low byte to 0.
  -- Console 2 leaves the low byte as s2.readMem Lo.
  -- By sync, s2.readMem Lo = s1.readMem Lo, which is non-zero.
  rw [← h_synced]
  exact h_acc_damage

end AutoResearch
