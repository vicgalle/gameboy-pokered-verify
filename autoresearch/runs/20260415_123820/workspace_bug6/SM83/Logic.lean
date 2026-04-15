/-
  SM83/Logic.lean — AND, OR, XOR, shifts, bit ops for the SM83.
-/
import SM83.Flags
import SM83.Basic

namespace SM83

/-! ### Logical Operations -/

/-- AND r — AND with A, set flags Z 0 1 0. -/
def execAnd (s : CPUState) (v : BitVec 8) : CPUState :=
  let result := s.a &&& v
  { s with a := result, f := mkFlags (result == 0) false true false }

/-- OR r — OR with A, set flags Z 0 0 0. -/
def execOr (s : CPUState) (v : BitVec 8) : CPUState :=
  let result := s.a ||| v
  { s with a := result, f := mkFlags (result == 0) false false false }

/-- XOR r — XOR with A, set flags Z 0 0 0. -/
def execXor (s : CPUState) (v : BitVec 8) : CPUState :=
  let result := s.a ^^^ v
  { s with a := result, f := mkFlags (result == 0) false false false }

/-- CPL — Complement A (flip all bits), set flags - 1 1 -. -/
def execCpl (s : CPUState) : CPUState :=
  let cVal := s.cFlag
  let zVal := s.zFlag
  { s with a := ~~~s.a, f := mkFlags zVal true true cVal }

/-! ### Bit Shift Operations -/

/-- SRL r — Shift right logical. Bit 0 → C, bit 7 = 0. Flags: Z 0 0 C. -/
def execSrl (v : BitVec 8) : BitVec 8 × BitVec 8 :=
  let carry := v.getLsbD 0
  let result := v >>> 1
  (result, mkFlags (result == 0) false false carry)

/-- SLA r — Shift left arithmetic. Bit 7 → C, bit 0 = 0. Flags: Z 0 0 C. -/
def execSla (v : BitVec 8) : BitVec 8 × BitVec 8 :=
  let carry := v.getLsbD 7
  let result := v <<< 1
  (result, mkFlags (result == 0) false false carry)

/-- SRA r — Shift right arithmetic. Bit 0 → C, bit 7 unchanged. Flags: Z 0 0 C. -/
def execSra (v : BitVec 8) : BitVec 8 × BitVec 8 :=
  let carry := v.getLsbD 0
  let msb := v &&& 0x80
  let result := (v >>> 1) ||| msb
  (result, mkFlags (result == 0) false false carry)

/-- SWAP r — Swap nibbles. Flags: Z 0 0 0. -/
def execSwap (v : BitVec 8) : BitVec 8 × BitVec 8 :=
  let result := swapNibbles v
  (result, mkFlags (result == 0) false false false)

/-- RLCA — Rotate A left. Old bit 7 → carry and bit 0. Flags: 0 0 0 C. -/
def execRlca (s : CPUState) : CPUState :=
  let carry := s.a.getLsbD 7
  let result := (s.a <<< 1) ||| (if carry then 1 else 0)
  { s with a := result, f := mkFlags false false false carry }

/-- RRCA — Rotate A right. Old bit 0 → carry and bit 7. Flags: 0 0 0 C. -/
def execRrca (s : CPUState) : CPUState :=
  let carry := s.a.getLsbD 0
  let result := (s.a >>> 1) ||| (if carry then 0x80 else 0)
  { s with a := result, f := mkFlags false false false carry }

/-- RLA — Rotate A left through carry. Flags: 0 0 0 C. -/
def execRla (s : CPUState) : CPUState :=
  let oldCarry := s.cFlag
  let newCarry := s.a.getLsbD 7
  let result := (s.a <<< 1) ||| (if oldCarry then 1 else 0)
  { s with a := result, f := mkFlags false false false newCarry }

/-- RRA — Rotate A right through carry. Flags: 0 0 0 C. -/
def execRra (s : CPUState) : CPUState :=
  let oldCarry := s.cFlag
  let newCarry := s.a.getLsbD 0
  let result := (s.a >>> 1) ||| (if oldCarry then 0x80 else 0)
  { s with a := result, f := mkFlags false false false newCarry }

/-! ### Bit Operations -/

/-- BIT n, r — Test bit n. Flags: Z 0 1 -. Z is set if bit n is 0. -/
def execBit (n : Nat) (v : BitVec 8) (oldFlags : BitVec 8) : BitVec 8 :=
  let z := !v.getLsbD n
  let cVal := oldFlags.getLsbD cBit
  mkFlags z false true cVal

/-- SET n, r — Set bit n. No flag changes. -/
def execSet (n : Nat) (v : BitVec 8) : BitVec 8 := setBit8 v n

/-- RES n, r — Reset bit n. No flag changes. -/
def execRes (n : Nat) (v : BitVec 8) : BitVec 8 := resBit8 v n

/-- SCF — Set carry flag. Flags: - 0 0 1. -/
def execScf (s : CPUState) : CPUState :=
  let zVal := s.zFlag
  { s with f := mkFlags zVal false false true }

/-- CCF — Complement carry flag. Flags: - 0 0 !C. -/
def execCcf (s : CPUState) : CPUState :=
  let zVal := s.zFlag
  { s with f := mkFlags zVal false false (!s.cFlag) }

/-! ### #eval Validation Tests -/

-- SRL 0x04 → 0x02, C=0
#eval
  let (result, flags) := execSrl (0x04 : BitVec 8)
  (result == 0x02, flags.getLsbD cBit == false)

-- SRL 0x01 → 0x00, Z=1, C=1
#eval
  let (result, flags) := execSrl (0x01 : BitVec 8)
  (result == 0x00, flags.getLsbD zBit == true, flags.getLsbD cBit == true)

-- SLA 0x04 → 0x08, C=0
#eval
  let (result, flags) := execSla (0x04 : BitVec 8)
  (result == 0x08, flags.getLsbD cBit == false)

-- SLA 0x80 → 0x00, Z=1, C=1
#eval
  let (result, flags) := execSla (0x80 : BitVec 8)
  (result == 0x00, flags.getLsbD zBit == true, flags.getLsbD cBit == true)

-- AND 0xF0 with A=0xFF → 0xF0
#eval
  let s := defaultState.setA 0xFF
  let s' := execAnd s 0xF0
  (s'.a == 0xF0, s'.hFlag == true)

-- XOR A with itself → 0, Z=1
#eval
  let s := defaultState.setA 0x42
  let s' := execXor s 0x42
  (s'.a == 0x00, s'.zFlag == true)

-- SWAP 0xAB → 0xBA
#eval
  let (result, _) := execSwap (0xAB : BitVec 8)
  result == 0xBA

-- BIT 0, 0x01 → Z=0 (bit is set)
#eval
  let flags := execBit 0 (0x01 : BitVec 8) (0x00 : BitVec 8)
  flags.getLsbD zBit == false

-- BIT 1, 0x01 → Z=1 (bit is not set)
#eval
  let flags := execBit 1 (0x01 : BitVec 8) (0x00 : BitVec 8)
  flags.getLsbD zBit == true

end SM83
