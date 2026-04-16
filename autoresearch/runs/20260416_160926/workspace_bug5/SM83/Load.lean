/-
  SM83/Load.lean — LD opcodes, PUSH/POP for the SM83.
-/
import SM83.Flags
import SM83.Memory

namespace SM83

/-! ### 8-bit Loads -/

-- LD r, n — Load immediate 8-bit value into register.
-- These are just the setter functions on CPUState (setA, setB, etc.)

/-- LD A, [HL] — Load byte at address HL into A. -/
def CPUState.ldAHL (s : CPUState) : CPUState :=
  { s with a := s.readMem s.hl }

/-- LD [HL], A — Store A at address HL. -/
def CPUState.ldHLA (s : CPUState) : CPUState :=
  s.writeMem s.hl s.a

/-- LD [HL], r — Store register value at address HL. -/
def CPUState.ldHLr (s : CPUState) (v : BitVec 8) : CPUState :=
  s.writeMem s.hl v

/-- LD A, [nn] — Load byte at absolute address into A. -/
def CPUState.ldAnn (s : CPUState) (addr : BitVec 16) : CPUState :=
  { s with a := s.readMem addr }

/-- LD [nn], A — Store A at absolute address. -/
def CPUState.ldnnA (s : CPUState) (addr : BitVec 16) : CPUState :=
  s.writeMem addr s.a

/-- LD A, [BC]. -/
def CPUState.ldABC (s : CPUState) : CPUState :=
  { s with a := s.readMem s.bc }

/-- LD A, [DE]. -/
def CPUState.ldADE (s : CPUState) : CPUState :=
  { s with a := s.readMem s.de }

/-- LD [BC], A. -/
def CPUState.ldBCA (s : CPUState) : CPUState :=
  s.writeMem s.bc s.a

/-- LD [DE], A. -/
def CPUState.ldDEA (s : CPUState) : CPUState :=
  s.writeMem s.de s.a

/-- LDI [HL], A — Store A at [HL], then increment HL. -/
def CPUState.ldiHLA (s : CPUState) : CPUState :=
  let s := s.writeMem s.hl s.a
  s.setHL (s.hl + 1)

/-- LDD [HL], A — Store A at [HL], then decrement HL. -/
def CPUState.lddHLA (s : CPUState) : CPUState :=
  let s := s.writeMem s.hl s.a
  s.setHL (s.hl - 1)

/-- LDI A, [HL] — Load [HL] into A, then increment HL. -/
def CPUState.ldiAHL (s : CPUState) : CPUState :=
  let v := s.readMem s.hl
  let s := { s with a := v }
  s.setHL (s.hl + 1)

/-- LDD A, [HL] — Load [HL] into A, then decrement HL. -/
def CPUState.lddAHL (s : CPUState) : CPUState :=
  let v := s.readMem s.hl
  let s := { s with a := v }
  s.setHL (s.hl - 1)

/-! ### 16-bit Loads -/

/-- LD rr, nn — Load immediate 16-bit value. -/
def CPUState.ldBCnn (s : CPUState) (v : BitVec 16) : CPUState := s.setBC v
def CPUState.ldDEnn (s : CPUState) (v : BitVec 16) : CPUState := s.setDE v
def CPUState.ldHLnn (s : CPUState) (v : BitVec 16) : CPUState := s.setHL v
def CPUState.ldSPnn (s : CPUState) (v : BitVec 16) : CPUState := { s with sp := v }

/-! ### Stack Operations -/

/-- PUSH BC. -/
def CPUState.pushBC (s : CPUState) : CPUState := s.pushStack s.bc

/-- PUSH DE. -/
def CPUState.pushDE (s : CPUState) : CPUState := s.pushStack s.de

/-- PUSH HL. -/
def CPUState.pushHL (s : CPUState) : CPUState := s.pushStack s.hl

/-- PUSH AF. -/
def CPUState.pushAF (s : CPUState) : CPUState := s.pushStack s.af

/-- POP BC. -/
def CPUState.popBC (s : CPUState) : CPUState :=
  let (s, v) := s.popStack
  s.setBC v

/-- POP DE. -/
def CPUState.popDE (s : CPUState) : CPUState :=
  let (s, v) := s.popStack
  s.setDE v

/-- POP HL. -/
def CPUState.popHL (s : CPUState) : CPUState :=
  let (s, v) := s.popStack
  s.setHL v

/-- POP AF — note: lower 4 bits of F are always 0. -/
def CPUState.popAF (s : CPUState) : CPUState :=
  let (s, v) := s.popStack
  { s with a := hi v, f := lo v &&& 0xF0 }

end SM83
