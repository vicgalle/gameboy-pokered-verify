/-
  SM83/Flags.lean — Flag register (Z, N, H, C) semantics for the SM83.

  The F register layout:
    Bit 7: Z (Zero flag)
    Bit 6: N (Subtract flag)
    Bit 5: H (Half-carry flag)
    Bit 4: C (Carry flag)
    Bits 3-0: Always 0
-/
import SM83.State

namespace SM83

-- Flag bit positions
def zBit : Nat := 7
def nBit : Nat := 6
def hBit : Nat := 5
def cBit : Nat := 4

/-- Get the Zero flag. -/
def CPUState.zFlag (s : CPUState) : Bool := s.f.getLsbD zBit

/-- Get the Subtract flag. -/
def CPUState.nFlag (s : CPUState) : Bool := s.f.getLsbD nBit

/-- Get the Half-carry flag. -/
def CPUState.hFlag (s : CPUState) : Bool := s.f.getLsbD hBit

/-- Get the Carry flag. -/
def CPUState.cFlag (s : CPUState) : Bool := s.f.getLsbD cBit

/-- Build a flag byte from individual flag booleans. Bits 3-0 are always 0. -/
def mkFlags (z n h c : Bool) : BitVec 8 :=
  let zv : BitVec 8 := if z then 1 <<< 7 else 0
  let nv : BitVec 8 := if n then 1 <<< 6 else 0
  let hv : BitVec 8 := if h then 1 <<< 5 else 0
  let cv : BitVec 8 := if c then 1 <<< 4 else 0
  zv ||| nv ||| hv ||| cv

/-- Set all flags at once. -/
def CPUState.setFlags (s : CPUState) (z n h c : Bool) : CPUState :=
  { s with f := mkFlags z n h c }

/-- Set just the Zero flag, preserving others. -/
def CPUState.setZFlag (s : CPUState) (v : Bool) : CPUState :=
  let mask : BitVec 8 := ~~~(1 <<< 7)
  let bit : BitVec 8 := if v then 1 <<< 7 else 0
  { s with f := (s.f &&& mask) ||| bit }

/-- Set just the Carry flag, preserving others. -/
def CPUState.setCFlag (s : CPUState) (v : Bool) : CPUState :=
  let mask : BitVec 8 := ~~~(1 <<< 4)
  let bit : BitVec 8 := if v then 1 <<< 4 else 0
  { s with f := (s.f &&& mask) ||| bit }

end SM83
