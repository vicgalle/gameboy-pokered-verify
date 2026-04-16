import SM83

namespace AutoResearch

/-
  Bug #4: heal_overflow (Pokémon Red/Blue)
  
  In Pokémon Red, Blue, and Yellow, recovery moves (Recover, Softboiled, Rest) 
  calculate the difference between a Pokémon's current HP and its maximum HP 
  to determine if the Pokémon is already at full HP. 
  
  The bug occurs because the comparison logic incorrectly uses the Z (zero) flag 
  from an 8-bit 'sbc' operation on the high bytes of the HP values, rather than 
  checking the full 16-bit result. If the high byte of the subtraction 
  (MaxHP - CurrentHP) is zero, the game incorrectly concludes the Pokémon 
  is at full HP, even if the low byte of the difference is non-zero.
  
  This happens whenever 0 ≤ (MaxHP - CurrentHP) < 256. 
  Specifically, if the gap is between 1 and 255, the move fails when it 
  should have succeeded.
-/

-- Define addresses for Battle Pokémon HP in Gen 1 (Red/Blue/Yellow)
def wBattleMonHP_Hi : BitVec 16    := 0xD015
def wBattleMonHP_Lo : BitVec 16    := 0xD016
def wBattleMonMaxHP_Hi : BitVec 16 := 0xD01D
def wBattleMonMaxHP_Lo : BitVec 16 := 0xD01E

/-- Helper to get Current HP from the CPU state -/
def hp (s : SM83.CPUState) : BitVec 16 := 
  SM83.mk16 (s.readMem wBattleMonHP_Hi) (s.readMem wBattleMonHP_Lo)

/-- Helper to get Maximum HP from the CPU state -/
def maxHP (s : SM83.CPUState) : BitVec 16 := 
  SM83.mk16 (s.readMem wBattleMonMaxHP_Hi) (s.readMem wBattleMonMaxHP_Lo)

/-- 
  The buggy implementation of the "is full HP" check found in Gen 1.
  It performs a 16-bit subtraction but only relies on the Z flag 
  from the high-byte subtraction.
-/
def impl_is_full (s : SM83.CPUState) : Bool :=
  -- Load MaxHP low byte into A
  let s1 := s.setA (s.readMem wBattleMonMaxHP_Lo)
  -- Subtract CurrentHP low byte (sets Carry flag)
  let s2 := s1.execSub (s.readMem wBattleMonHP_Lo)
  -- Load MaxHP high byte into A
  let s3 := s2.setA (s.readMem wBattleMonMaxHP_Hi)
  -- Subtract CurrentHP high byte with Carry
  let s4 := s3.execSbc (s.readMem wBattleMonHP_Hi)
  -- The bug: use the Z flag from the last 8-bit sbc
  s4.zFlag

/-- 
  The correct implementation of the "is full HP" check.
  A Pokémon is at full HP if and only if CurrentHP == MaxHP.
-/
def spec_is_full (s : SM83.CPUState) : Bool :=
  hp s == maxHP s

/-- 
  Level 1: Concrete witness.
  We show that for a gap of 255 HP (e.g., MaxHP=511, HP=256), 
  the buggy implementation incorrectly reports the Pokémon is at "Full HP".
-/
def buggyState : SM83.CPUState :=
  let s := SM83.defaultState
  -- Set MaxHP = 511 (0x01FF)
  let s := s.writeMem wBattleMonMaxHP_Hi 0x01
  let s := s.writeMem wBattleMonMaxHP_Lo 0xFF
  -- Set Current HP = 256 (0x0100)
  let s := s.writeMem wBattleMonHP_Hi 0x01
  let s := s.writeMem wBattleMonHP_Lo 0x00
  s

theorem L1_witness : impl_is_full buggyState = true ∧ spec_is_full buggyState = false := by
  rfl

/--
  Level 2: Universal characterization.
  The bug triggers (impl_is_full returns true while spec_is_full is false)
  if and only if the difference between MaxHP and HP is between 1 and 255.
  (Assuming HP ≤ MaxHP).
-/
theorem L2_characterization (s : SM83.CPUState) :
  (hp s).toNat ≤ (maxHP s).toNat →
  (impl_is_full s = true ∧ spec_is_full s = false) ↔ 
  (0 < (maxHP s).toNat - (hp s).toNat ∧ (maxHP s).toNat - (hp s).toNat < 256) := by
  sorry -- Proof involves showing how carry propogates through sbc.

/--
  Level 3: Fixed implementation.
  To fix the bug, we must 'OR' the high byte of the subtraction result with the 
  low byte of the subtraction result to check if the entire 16-bit result is zero.
-/
def fix_is_full (s : SM83.CPUState) : Bool :=
  let s1 := s.setA (s.readMem wBattleMonMaxHP_Lo)
  let s2 := s1.execSub (s.readMem wBattleMonHP_Lo)
  let res_lo := s2.a
  let s3 := s2.setA (s.readMem wBattleMonMaxHP_Hi)
  let s4 := s3.execSbc (s.readMem wBattleMonHP_Hi)
  let res_hi := s4.a
  -- Correct 16-bit zero check: (res_hi | res_lo) == 0
  (res_hi.toNat ||| res_lo.toNat) == 0

theorem L3_fix_verified (s : SM83.CPUState) : fix_is_full s = spec_is_full s := by
  sorry -- Proof involves showing bitwise OR of bytes equals 0 iff the 16-bit word is 0.

/--
  Level 4: Relational property.
  The buggy implementation and the correct implementation agree whenever 
  the HP gap is 0 or greater than or equal to 256.
-/
theorem L4_relational (s : SM83.CPUState) :
  (hp s).toNat ≤ (maxHP s).toNat →
  ((maxHP s).toNat - (hp s).toNat = 0 ∨ (maxHP s).toNat - (hp s).toNat >= 256) →
  impl_is_full s = spec_is_full s := by
  sorry

end AutoResearch
