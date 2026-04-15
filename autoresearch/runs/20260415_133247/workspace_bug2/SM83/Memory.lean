/-
  SM83/Memory.lean — Memory model for the Game Boy.

  For our purposes, memory is a total function `BitVec 16 → BitVec 8`.
  This file provides named constants for important memory regions and
  helper functions for common memory operations.
-/
import SM83.State

namespace SM83

-- Game Boy memory regions
def romBank0Start : BitVec 16 := 0x0000
def romBank1Start : BitVec 16 := 0x4000
def vramStart     : BitVec 16 := 0x8000
def sramStart     : BitVec 16 := 0xA000
def wramStart     : BitVec 16 := 0xC000
def oamStart      : BitVec 16 := 0xFE00
def ioStart       : BitVec 16 := 0xFF00
def hramStart     : BitVec 16 := 0xFF80

/-- Write a block of bytes starting at an address. -/
def CPUState.writeBlock (s : CPUState) (addr : BitVec 16) (bytes : List (BitVec 8)) : CPUState :=
  bytes.foldl (fun (acc : CPUState × BitVec 16) b =>
    (acc.1.writeMem acc.2 b, acc.2 + 1)) (s, addr) |>.1

/-- Push a 16-bit value onto the stack (decrement SP by 2, write little-endian). -/
def CPUState.pushStack (s : CPUState) (v : BitVec 16) : CPUState :=
  let sp' := s.sp - 2
  let s := { s with sp := sp' }
  s.writeMem16 sp' v

/-- Pop a 16-bit value from the stack (read little-endian, increment SP by 2). -/
def CPUState.popStack (s : CPUState) : CPUState × BitVec 16 :=
  let v := s.readMem16 s.sp
  let s := { s with sp := s.sp + 2 }
  (s, v)

end SM83
