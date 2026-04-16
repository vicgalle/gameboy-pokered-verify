/-
  SM83/Arithmetic.lean — ADD, SUB, INC, DEC, CP opcodes for the SM83.

  All arithmetic opcodes set flags according to the SM83 specification:
  - Z: set if result is zero
  - N: set if subtraction
  - H: half-carry (carry from bit 3 to bit 4)
  - C: carry (carry from bit 7 / borrow)
-/
import SM83.Flags

namespace SM83

/-! ### 8-bit Arithmetic -/

/-- Half-carry for addition: carry from bit 3 to bit 4. -/
def halfCarryAdd (a b : BitVec 8) : Bool :=
  ((a &&& 0x0F) + (b &&& 0x0F)).getLsbD 4

/-- Half-carry for addition with carry. -/
def halfCarryAdc (a b : BitVec 8) (carry : Bool) : Bool :=
  let c : BitVec 8 := if carry then 1 else 0
  ((a &&& 0x0F) + (b &&& 0x0F) + c).getLsbD 4

/-- Half-borrow for subtraction: borrow from bit 4. -/
def halfBorrowSub (a b : BitVec 8) : Bool :=
  (a &&& 0x0F) < (b &&& 0x0F)

/-- Half-borrow for subtraction with carry. -/
def halfBorrowSbc (a b : BitVec 8) (carry : Bool) : Bool :=
  let c : BitVec 8 := if carry then 1 else 0
  (a &&& 0x0F) < (b &&& 0x0F) + c

/-- Full carry for 8-bit addition. -/
def carryAdd (a b : BitVec 8) : Bool :=
  (a.toNat + b.toNat) > 0xFF

/-- Full carry for 8-bit addition with carry. -/
def carryAdc (a b : BitVec 8) (carry : Bool) : Bool :=
  let c := if carry then 1 else 0
  (a.toNat + b.toNat + c) > 0xFF

/-- Borrow for 8-bit subtraction. -/
def borrowSub (a b : BitVec 8) : Bool :=
  a.toNat < b.toNat

/-- Borrow for 8-bit subtraction with carry. -/
def borrowSbc (a b : BitVec 8) (carry : Bool) : Bool :=
  let c := if carry then 1 else 0
  a.toNat < b.toNat + c

/-- ADD A, r — Add r to A, set flags Z 0 H C. -/
def execAddA (s : CPUState) (v : BitVec 8) : CPUState :=
  let result := s.a + v
  { s with
    a := result
    f := mkFlags (result == 0) false (halfCarryAdd s.a v) (carryAdd s.a v) }

/-- ADC A, r — Add r + carry to A, set flags Z 0 H C. -/
def execAdcA (s : CPUState) (v : BitVec 8) : CPUState :=
  let c : BitVec 8 := if s.cFlag then 1 else 0
  let result := s.a + v + c
  { s with
    a := result
    f := mkFlags (result == 0) false (halfCarryAdc s.a v s.cFlag) (carryAdc s.a v s.cFlag) }

/-- SUB r — Subtract r from A, set flags Z 1 H C. -/
def execSub (s : CPUState) (v : BitVec 8) : CPUState :=
  let result := s.a - v
  { s with
    a := result
    f := mkFlags (result == 0) true (halfBorrowSub s.a v) (borrowSub s.a v) }

/-- SBC A, r — Subtract r + carry from A, set flags Z 1 H C. -/
def execSbcA (s : CPUState) (v : BitVec 8) : CPUState :=
  let c : BitVec 8 := if s.cFlag then 1 else 0
  let result := s.a - v - c
  { s with
    a := result
    f := mkFlags (result == 0) true (halfBorrowSbc s.a v s.cFlag) (borrowSbc s.a v s.cFlag) }

/-- CP r — Compare A with r (subtract but discard result), set flags Z 1 H C. -/
def execCp (s : CPUState) (v : BitVec 8) : CPUState :=
  let result := s.a - v
  { s with
    f := mkFlags (result == 0) true (halfBorrowSub s.a v) (borrowSub s.a v) }

/-- INC r — Increment 8-bit value, set flags Z 0 H -. Carry flag unchanged. -/
def execInc8 (v : BitVec 8) (oldFlags : BitVec 8) : BitVec 8 × BitVec 8 :=
  let result := v + 1
  let hc := halfCarryAdd v 1
  let z := result == 0
  -- Preserve carry flag (bit 4), set Z 0 H
  let cBitVal := oldFlags &&& (1 <<< 4)
  let newFlags := mkFlags z false hc false ||| cBitVal
  (result, newFlags)

/-- DEC r — Decrement 8-bit value, set flags Z 1 H -. Carry flag unchanged. -/
def execDec8 (v : BitVec 8) (oldFlags : BitVec 8) : BitVec 8 × BitVec 8 :=
  let result := v - 1
  let hb := halfBorrowSub v 1
  let z := result == 0
  let cBitVal := oldFlags &&& (1 <<< 4)
  let newFlags := mkFlags z true hb false ||| cBitVal
  (result, newFlags)

/-- INC A. -/
def CPUState.incA (s : CPUState) : CPUState :=
  let (result, flags) := execInc8 s.a s.f
  { s with a := result, f := flags }

/-- DEC A. -/
def CPUState.decA (s : CPUState) : CPUState :=
  let (result, flags) := execDec8 s.a s.f
  { s with a := result, f := flags }

/-- INC B. -/
def CPUState.incB (s : CPUState) : CPUState :=
  let (result, flags) := execInc8 s.b s.f
  { s with b := result, f := flags }

/-- DEC B. -/
def CPUState.decB (s : CPUState) : CPUState :=
  let (result, flags) := execDec8 s.b s.f
  { s with b := result, f := flags }

/-- INC C. -/
def CPUState.incC (s : CPUState) : CPUState :=
  let (result, flags) := execInc8 s.c s.f
  { s with c := result, f := flags }

/-- DEC C. -/
def CPUState.decC (s : CPUState) : CPUState :=
  let (result, flags) := execDec8 s.c s.f
  { s with c := result, f := flags }

/-- INC H. -/
def CPUState.incH (s : CPUState) : CPUState :=
  let (result, flags) := execInc8 s.h s.f
  { s with h := result, f := flags }

/-- DEC H. -/
def CPUState.decH (s : CPUState) : CPUState :=
  let (result, flags) := execDec8 s.h s.f
  { s with h := result, f := flags }

/-- INC L. -/
def CPUState.incL (s : CPUState) : CPUState :=
  let (result, flags) := execInc8 s.l s.f
  { s with l := result, f := flags }

/-- DEC L. -/
def CPUState.decL (s : CPUState) : CPUState :=
  let (result, flags) := execDec8 s.l s.f
  { s with l := result, f := flags }

/-! ### 16-bit Arithmetic -/

/-- INC rr — Increment 16-bit register pair. No flags affected. -/
def CPUState.incBC (s : CPUState) : CPUState := s.setBC (s.bc + 1)
def CPUState.incDE (s : CPUState) : CPUState := s.setDE (s.de + 1)
def CPUState.incHL (s : CPUState) : CPUState := s.setHL (s.hl + 1)
def CPUState.incSP (s : CPUState) : CPUState := { s with sp := s.sp + 1 }

/-- DEC rr — Decrement 16-bit register pair. No flags affected. -/
def CPUState.decBC (s : CPUState) : CPUState := s.setBC (s.bc - 1)
def CPUState.decDE (s : CPUState) : CPUState := s.setDE (s.de - 1)
def CPUState.decHL (s : CPUState) : CPUState := s.setHL (s.hl - 1)
def CPUState.decSP (s : CPUState) : CPUState := { s with sp := s.sp - 1 }

/-- ADD HL, rr — Add 16-bit register pair to HL. Flags: - 0 H C (Z unchanged). -/
def CPUState.addHL (s : CPUState) (v : BitVec 16) : CPUState :=
  let hl := s.hl
  let result := hl + v
  let hc := ((hl &&& 0x0FFF) + (v &&& 0x0FFF)).toNat > 0x0FFF
  let carry := (hl.toNat + v.toNat) > 0xFFFF
  let zVal := s.zFlag  -- Z is preserved
  { s with
    h := SM83.hi result
    l := SM83.lo result
    f := mkFlags zVal false hc carry }

/-! ### #eval Validation Tests -/

-- ADD A, 0xFF when A = 0x01 → A = 0x00, Z=1, H=1, C=1
#eval
  let s := defaultState.setA 0x01
  let s' := execAddA s 0xFF
  (s'.a == 0x00, s'.zFlag == true, s'.hFlag == true, s'.cFlag == true)
  -- expected: (true, true, true, true)

-- SUB 0x01 when A = 0x01 → A = 0x00, Z=1, N=1, C=0
#eval
  let s := defaultState.setA 0x01
  let s' := execSub s 0x01
  (s'.a == 0x00, s'.zFlag == true, s'.nFlag == true, s'.cFlag == false)

-- CP 0x05 when A = 0x05 → Z=1, A unchanged
#eval
  let s := defaultState.setA 0x05
  let s' := execCp s 0x05
  (s'.a == 0x05, s'.zFlag == true)

-- INC 0xFF → 0x00, Z=1, H=1
#eval
  let s := defaultState.setA 0xFF
  let s' := s.incA
  (s'.a == 0x00, s'.zFlag == true, s'.hFlag == true)

-- DEC 0x01 → 0x00, Z=1, N=1
#eval
  let s := defaultState.setA 0x01
  let s' := s.decA
  (s'.a == 0x00, s'.zFlag == true, s'.nFlag == true)

-- DEC 0x00 → 0xFF, Z=0, H=1 (borrow from bit 4)
#eval
  let s := defaultState.setA 0x00
  let s' := s.decA
  (s'.a == 0xFF, s'.zFlag == false, s'.hFlag == true)

-- ADD A, 0x0F when A = 0x01 → A = 0x10, Z=0, H=1, C=0
#eval
  let s := defaultState.setA 0x01
  let s' := execAddA s 0x0F
  (s'.a == 0x10, s'.zFlag == false, s'.hFlag == true, s'.cFlag == false)

end SM83
