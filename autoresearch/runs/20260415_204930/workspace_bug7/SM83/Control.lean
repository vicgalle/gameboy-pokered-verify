/-
  SM83/Control.lean — JP, JR, CALL, RET and condition opcodes for the SM83.
-/
import SM83.Flags
import SM83.Memory
import SM83.Basic

namespace SM83

/-! ### Condition Codes -/

/-- SM83 condition codes for conditional jumps/calls/returns. -/
inductive Condition where
  | nz  -- Not Zero (Z=0)
  | z   -- Zero (Z=1)
  | nc  -- Not Carry (C=0)
  | c   -- Carry (C=1)
  deriving Repr, DecidableEq

/-- Evaluate a condition against the current flags. -/
def CPUState.evalCond (s : CPUState) (cc : Condition) : Bool :=
  match cc with
  | .nz => !s.zFlag
  | .z  => s.zFlag
  | .nc => !s.cFlag
  | .c  => s.cFlag

/-! ### Jump Instructions -/

/-- JP nn — Unconditional jump to 16-bit address. -/
def CPUState.jp (s : CPUState) (addr : BitVec 16) : CPUState :=
  { s with pc := addr }

/-- JP cc, nn — Conditional jump. -/
def CPUState.jpCond (s : CPUState) (cc : Condition) (addr : BitVec 16) : CPUState :=
  if s.evalCond cc then { s with pc := addr } else s

/-- JR offset — Relative jump (signed 8-bit offset added to PC). -/
def CPUState.jr (s : CPUState) (offset : BitVec 8) : CPUState :=
  { s with pc := s.pc + signExtend8to16 offset }

/-- JR cc, offset — Conditional relative jump. -/
def CPUState.jrCond (s : CPUState) (cc : Condition) (offset : BitVec 8) : CPUState :=
  if s.evalCond cc then { s with pc := s.pc + signExtend8to16 offset } else s

/-- JP [HL] — Jump to address in HL. -/
def CPUState.jpHL (s : CPUState) : CPUState :=
  { s with pc := s.hl }

/-! ### Call and Return -/

/-- CALL nn — Push PC onto stack, jump to address. -/
def CPUState.call (s : CPUState) (addr : BitVec 16) : CPUState :=
  let s := s.pushStack s.pc
  { s with pc := addr }

/-- CALL cc, nn — Conditional call. -/
def CPUState.callCond (s : CPUState) (cc : Condition) (addr : BitVec 16) : CPUState :=
  if s.evalCond cc then s.call addr else s

/-- RET — Pop address from stack, jump to it. -/
def CPUState.ret (s : CPUState) : CPUState :=
  let (s, addr) := s.popStack
  { s with pc := addr }

/-- RET cc — Conditional return. -/
def CPUState.retCond (s : CPUState) (cc : Condition) : CPUState :=
  if s.evalCond cc then s.ret else s

/-! ### Misc Control -/

/-- HALT — Halt the CPU until an interrupt. -/
def CPUState.halt (s : CPUState) : CPUState :=
  { s with halted := true }

/-- DI / EI are no-ops in our model (we don't model interrupts). -/
def CPUState.di (s : CPUState) : CPUState := s
def CPUState.ei (s : CPUState) : CPUState := s

/-- NOP — No operation. -/
def CPUState.nop (s : CPUState) : CPUState := s

end SM83
