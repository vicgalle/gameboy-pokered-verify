import SM83

namespace AutoResearch

/-
  Bug #4: heal_overflow
  
  In Pokémon Red, Blue, and Yellow, recovery moves (Recover, Softboiled, Rest) 
  incorrectly report that the Pokémon is already at full HP under certain 
  conditions. This occurs because the implementation performs a 16-bit 
  subtraction between Max HP and Current HP but only checks the Zero (Z) 
  flag of the high-byte subtraction.
  
  The bug triggers when the difference (MaxHP - CurrentHP) is between 1 and 255.
  In this range, the 16-bit subtraction's high byte is 0 (due to either the 
  high bytes being equal or a carry-over), leading the game to incorrectly 
  set the Z flag and conclude the Pokémon's HP is full.
-/

-- Pokémon Red Battle Mon memory addresses
def wBattleMonHP_Hi : BitVec 16    := 0xD015
def wBattleMonHP_Lo : BitVec 16    := 0xD016
def wBattleMonMaxHP_Hi : BitVec 16 := 0xD01D
def wBattleMonMaxHP_Lo : BitVec 16 := 0xD01E

/-- Helper to extract the 16-bit Current HP from the CPU state. -/
def hp (s : SM83.CPUState) : BitVec 16 := 
  SM83.mk16 (s.readMem wBattleMonHP_Hi) (s.readMem wBattleMonHP_Lo)

/-- Helper to extract the 16-bit Maximum HP from the CPU state. -/
def maxHP (s : SM83.CPUState) : BitVec 16 := 
  SM83.mk16 (s.readMem wBattleMonMaxHP_Hi) (s.readMem wBattleMonMaxHP_Lo)

/-- 
  The buggy implementation of the "is full HP" check.
  It performs a 16-bit subtraction (MaxHP - HP) but uses the Z flag 
  from the high-byte subtraction only.
-/
def impl_is_full (s : SM83.CPUState) : Bool :=
  -- Load MaxHP low byte into A
  let s := s.setA (s.readMem wBattleMonMaxHP_Lo)
  -- Subtract CurrentHP low byte (sets Carry flag if HP_Lo > MaxHP_Lo)
  let s := s.execSub (s.readMem wBattleMonHP_Lo)
  -- Load MaxHP high byte into A (does not affect flags)
  let s := s.setA (s.readMem wBattleMonMaxHP_Hi)
  -- Subtract CurrentHP high byte with Carry
  let s := s.execSbc (s.readMem wBattleMonHP_Hi)
  -- The bug: check the Z flag of the high-byte result only
  s.zFlag

/-- 
  The correct behavior: a Pokémon is at full HP if and only if its 
  current HP equals its maximum HP.
-/
def spec_is_full (s : SM83.CPUState) : Bool :=
  hp s == maxHP s

/-- 
  L1: Concrete witness.
  A Pokémon with 255/256 HP should heal, but the bug prevents it.
  MaxHP = 256 (0x0100), HP = 255 (0x00FF).
  Gap is 1.
-/
def buggyState : SM83.CPUState :=
  let s := SM83.defaultState
  -- Set MaxHP = 256 (0x0100)
  let s := s.writeMem wBattleMonMaxHP_Hi 0x01
  let s := s.writeMem wBattleMonMaxHP_Lo 0x00
  -- Set HP = 255 (0x00FF)
  let s := s.writeMem wBattleMonHP_Hi 0x00
  let s := s.writeMem wBattleMonHP_Lo 0xFF
  s

theorem L1_witness : impl_is_full buggyState = true ∧ spec_is_full buggyState = false := by
  native_decide

/--
  L2: Universal characterization.
  The bug triggers (impl_is_full = true but spec_is_full = false) 
  if and only if the HP gap is between 1 and 255.
  (Assumption: HP is not greater than MaxHP).
-/
theorem L2_characterization (s : SM83.CPUState) :
  (hp s).toNat ≤ (maxHP s).toNat →
  (impl_is_full s = true ∧ spec_is_full s = false) ↔ 
  (0 < (maxHP s).toNat - (hp s).toNat ∧ (maxHP s).toNat - (hp s).toNat < 256) := by
  sorry

/--
  Level 3: Fixed implementation.
  The fix involves checking both the low and high bytes of the 
  subtraction result by ORing them together.
-/
def fix_is_full (s : SM83.CPUState) : Bool :=
  let s := s.setA (s.readMem wBattleMonMaxHP_Lo)
  let s := s.execSub (s.readMem wBattleMonHP_Lo)
  let low_res := s.a
  let s := s.setA (s.readMem wBattleMonMaxHP_Hi)
  let s := s.execSbc (s.readMem wBattleMonHP_Hi)
  -- Combine results: Z flag will be set only if both high and low results are zero.
  let s := s.execOr low_res
  s.zFlag

theorem L3_fix_verified (s : SM83.CPUState) :
  fix_is_full s = spec_is_full s := by
  sorry

/--
  Level 4: Relational property.
  Whenever the HP gap is either 0 (actually full) or at least 256, 
  the buggy implementation correctly identifies that it is not a "false full".
-/
theorem L4_relational (s : SM83.CPUState) :
  (hp s).toNat ≤ (maxHP s).toNat →
  ((maxHP s).toNat - (hp s).toNat = 0 ∨ (maxHP s).toNat - (hp s).toNat >= 256) →
  impl_is_full s = spec_is_full s := by
  sorry

end AutoResearch

