/-
  SM83/State.lean — CPU state for the Sharp SM83 (Game Boy CPU).
-/
import SM83.Basic

namespace SM83

/-- The SM83 CPU state. Memory is modeled as a total function from 16-bit addresses to 8-bit values. -/
structure CPUState where
  a : BitVec 8
  f : BitVec 8        -- Flags: bit 7=Z, 6=N, 5=H, 4=C (bits 3-0 always 0)
  b : BitVec 8
  c : BitVec 8
  d : BitVec 8
  e : BitVec 8
  h : BitVec 8
  l : BitVec 8
  sp : BitVec 16
  pc : BitVec 16
  mem : BitVec 16 → BitVec 8
  halted : Bool

/-- Register pair BC. -/
def CPUState.bc (s : CPUState) : BitVec 16 := s.b ++ s.c

/-- Register pair DE. -/
def CPUState.de (s : CPUState) : BitVec 16 := s.d ++ s.e

/-- Register pair HL. -/
def CPUState.hl (s : CPUState) : BitVec 16 := s.h ++ s.l

/-- Register pair AF. -/
def CPUState.af (s : CPUState) : BitVec 16 := s.a ++ s.f

/-- Set register pair BC. -/
def CPUState.setBC (s : CPUState) (v : BitVec 16) : CPUState :=
  { s with b := hi v, c := lo v }

/-- Set register pair DE. -/
def CPUState.setDE (s : CPUState) (v : BitVec 16) : CPUState :=
  { s with d := hi v, e := lo v }

/-- Set register pair HL. -/
def CPUState.setHL (s : CPUState) (v : BitVec 16) : CPUState :=
  { s with h := hi v, l := lo v }

/-- Default CPU state: all registers zero, memory all zeros. -/
def defaultState : CPUState where
  a := 0
  f := 0
  b := 0
  c := 0
  d := 0
  e := 0
  h := 0
  l := 0
  sp := 0xFFFE
  pc := 0x0100
  mem := fun _ => 0
  halted := false

/-- Convenience setter for register A. -/
def CPUState.setA (s : CPUState) (v : BitVec 8) : CPUState := { s with a := v }

/-- Convenience setter for register B. -/
def CPUState.setB (s : CPUState) (v : BitVec 8) : CPUState := { s with b := v }

/-- Convenience setter for register C. -/
def CPUState.setC (s : CPUState) (v : BitVec 8) : CPUState := { s with c := v }

/-- Convenience setter for register D. -/
def CPUState.setD (s : CPUState) (v : BitVec 8) : CPUState := { s with d := v }

/-- Convenience setter for register E. -/
def CPUState.setE (s : CPUState) (v : BitVec 8) : CPUState := { s with e := v }

/-- Convenience setter for register H. -/
def CPUState.setH (s : CPUState) (v : BitVec 8) : CPUState := { s with h := v }

/-- Convenience setter for register L. -/
def CPUState.setL (s : CPUState) (v : BitVec 8) : CPUState := { s with l := v }

/-- Read a byte from memory. -/
def CPUState.readMem (s : CPUState) (addr : BitVec 16) : BitVec 8 := s.mem addr

/-- Write a byte to memory. -/
def CPUState.writeMem (s : CPUState) (addr : BitVec 16) (v : BitVec 8) : CPUState :=
  { s with mem := fun a => if a == addr then v else s.mem a }

/-- Read a 16-bit little-endian value from memory. -/
def CPUState.readMem16 (s : CPUState) (addr : BitVec 16) : BitVec 16 :=
  let lo := s.readMem addr
  let hi := s.readMem (addr + 1)
  mk16 hi lo

/-- Write a 16-bit little-endian value to memory. -/
def CPUState.writeMem16 (s : CPUState) (addr : BitVec 16) (v : BitVec 16) : CPUState :=
  let s := s.writeMem addr (lo v)
  s.writeMem (addr + 1) (hi v)

end SM83
