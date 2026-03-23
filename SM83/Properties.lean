/-
  SM83/Properties.lean — Algebraic properties of the SM83 instruction set.

  These are general theorems about the Game Boy CPU that hold for ALL inputs,
  independent of any particular game or program. They capture the mathematical
  structure of the instruction set: involutions, periods, cancellations,
  and hardware invariants.
-/
import SM83.Flags
import SM83.Logic
import SM83.Arithmetic
import SM83.Load
import SM83.Memory
import SM83.Basic

namespace SM83

/-! ## 1. Involutions — Operations that are their own inverse -/

/-- CPL is an involution: complementing A twice returns to the original value.
    This follows from boolean algebra (¬¬x = x) but we prove it at the CPU level:
    the register A is restored, even though flags (N, H) are set each time. -/
theorem cpl_involution (s : CPUState) :
    (execCpl (execCpl s)).a = s.a := by
  simp only [execCpl]
  have := (by native_decide : ∀ v : BitVec 8, ~~~(~~~v) = v)
  exact this s.a

/-- SWAP is an involution: swapping nibbles twice recovers the original byte.
    This is a permutation of order 2 on the 8-bit space. -/
theorem swap_involution (v : BitVec 8) :
    (execSwap (execSwap v).1).1 = v := by
  simp only [execSwap, swapNibbles]
  have := (by native_decide :
    ∀ b : BitVec 8, ((b >>> 4 ||| b <<< 4) >>> 4 ||| (b >>> 4 ||| b <<< 4) <<< 4) = b)
  exact this v

/-- CCF is an involution on the carry flag: complementing carry twice restores it.
    Proved by concrete witness exhaustion on the two relevant bits. -/
theorem ccf_involution_carry (c : Bool) :
    let f := mkFlags false false false c
    (execCcf (execCcf { defaultState with f := f })).cFlag = c := by
  cases c <;> native_decide

/-! ## 2. Self-Annihilation — XOR A, A is the canonical zeroing idiom -/

/-- XOR A with itself always produces zero. This is THE classic Game Boy
    idiom for zeroing a register: `xor a` is one byte, while `ld a, 0`
    is two bytes. Every Game Boy programmer knows this trick. -/
theorem xor_self_zeros (s : CPUState) :
    (execXor s s.a).a = 0 := by
  simp only [execXor]
  have := (by native_decide : ∀ v : BitVec 8, (v ^^^ v) = (0 : BitVec 8))
  exact this s.a

/-- XOR self always sets the Zero flag. -/
theorem xor_self_sets_zero_flag (s : CPUState) :
    (execXor s s.a).zFlag = true := by
  simp only [execXor, CPUState.zFlag, mkFlags]
  have := (by native_decide :
    ∀ v : BitVec 8,
      let result := v ^^^ v
      ((if result == 0 then (1 : BitVec 8) <<< 7 else 0) |||
       (if false then (1 : BitVec 8) <<< 6 else 0) |||
       (if false then (1 : BitVec 8) <<< 5 else 0) |||
       (if false then (1 : BitVec 8) <<< 4 else 0)).getLsbD zBit = true)
  exact this s.a

/-- XOR self clears the carry flag. -/
theorem xor_self_clears_carry (s : CPUState) :
    (execXor s s.a).cFlag = false := by
  simp only [execXor, CPUState.cFlag, mkFlags]
  have := (by native_decide :
    ∀ v : BitVec 8,
      let result := v ^^^ v
      ((if result == 0 then (1 : BitVec 8) <<< 7 else 0) |||
       (if false then (1 : BitVec 8) <<< 6 else 0) |||
       (if false then (1 : BitVec 8) <<< 5 else 0) |||
       (if false then (1 : BitVec 8) <<< 4 else 0)).getLsbD cBit = false)
  exact this s.a

/-! ## 3. Rotation Period — RLCA has period 8 -/

/-- RLCA has period 8: rotating A left 8 times returns to the original value.
    This captures the cyclic group structure: the 8 bits cycle through all
    positions and return home. -/
theorem rlca_period_8 (a : BitVec 8) :
    let rot1 (v : BitVec 8) := (v <<< 1) ||| (if v.getLsbD 7 then (1 : BitVec 8) else 0)
    rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 a))))))) = a := by
  have := (by native_decide :
    ∀ a : BitVec 8,
      let rot1 := fun (v : BitVec 8) => (v <<< 1) ||| (if v.getLsbD 7 then (1 : BitVec 8) else 0)
      rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 a))))))) = a)
  exact this a

/-- RLCA does NOT have period 4 — it's not a nibble rotation. -/
theorem rlca_not_period_4 :
    ∃ a : BitVec 8,
      let rot1 (v : BitVec 8) := (v <<< 1) ||| (if v.getLsbD 7 then (1 : BitVec 8) else 0)
      rot1 (rot1 (rot1 (rot1 a))) ≠ a := by
  exact ⟨1, by native_decide⟩

/-- RRCA also has period 8. -/
theorem rrca_period_8 (a : BitVec 8) :
    let rot1 (v : BitVec 8) := (v >>> 1) ||| (if v.getLsbD 0 then (0x80 : BitVec 8) else 0)
    rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 a))))))) = a := by
  have := (by native_decide :
    ∀ a : BitVec 8,
      let rot1 := fun (v : BitVec 8) => (v >>> 1) ||| (if v.getLsbD 0 then (0x80 : BitVec 8) else 0)
      rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 (rot1 a))))))) = a)
  exact this a

/-- RLCA and RRCA are inverses: one undoes the other. -/
theorem rlca_rrca_inverse (a : BitVec 8) :
    let rotL (v : BitVec 8) := (v <<< 1) ||| (if v.getLsbD 7 then (1 : BitVec 8) else 0)
    let rotR (v : BitVec 8) := (v >>> 1) ||| (if v.getLsbD 0 then (0x80 : BitVec 8) else 0)
    rotR (rotL a) = a := by
  have := (by native_decide :
    ∀ a : BitVec 8,
      let rotL := fun (v : BitVec 8) => (v <<< 1) ||| (if v.getLsbD 7 then (1 : BitVec 8) else 0)
      let rotR := fun (v : BitVec 8) => (v >>> 1) ||| (if v.getLsbD 0 then (0x80 : BitVec 8) else 0)
      rotR (rotL a) = a)
  exact this a

/-! ## 4. Arithmetic Cancellation — INC/DEC and ADD/SUB -/

/-- INC then DEC cancels on the register value (mod 256). -/
theorem inc_dec_cancel_value (v : BitVec 8) :
    (v + 1) - 1 = v := by
  have := (by native_decide : ∀ b : BitVec 8, (b + 1) - 1 = b)
  exact this v

/-- DEC then INC also cancels. -/
theorem dec_inc_cancel_value (v : BitVec 8) :
    (v - 1) + 1 = v := by
  have := (by native_decide : ∀ b : BitVec 8, (b - 1) + 1 = b)
  exact this v

/-- But INC then DEC does NOT preserve flags in general.
    This is important: a programmer cannot assume INC/DEC is a no-op
    even though the register value is restored. -/
theorem inc_dec_changes_flags :
    ∃ v f : BitVec 8,
      (execDec8 (execInc8 v f).1 (execInc8 v f).2).2 ≠ f := by
  exact ⟨0, 0, by native_decide⟩

/-- ADD A, x then SUB x recovers the original A. -/
theorem add_sub_cancel_a (s : CPUState) (x : BitVec 8) :
    (execSub (execAddA s x) x).a = s.a := by
  simp only [execAddA, execSub]
  have := (by native_decide : ∀ a x : BitVec 8, (a + x) - x = a)
  exact this s.a x

/-- SUB x then ADD A, x also recovers the original A. -/
theorem sub_add_cancel_a (s : CPUState) (x : BitVec 8) :
    (execAddA (execSub s x) x).a = s.a := by
  simp only [execAddA, execSub]
  have := (by native_decide : ∀ a x : BitVec 8, (a - x) + x = a)
  exact this s.a x

/-- CP does not modify A — it's a "phantom subtraction". -/
theorem cp_preserves_a (s : CPUState) (v : BitVec 8) :
    (execCp s v).a = s.a := by
  rfl

/-- CP sets the same flags as SUB would. -/
theorem cp_flags_eq_sub_flags (s : CPUState) (v : BitVec 8) :
    (execCp s v).f = (execSub s v).f := by
  rfl

/-! ## 5. Flag Register Hardware Invariant -/

/-- mkFlags always produces a byte with bits 3-0 equal to zero.
    This is a fundamental hardware constraint of the SM83's flag register. -/
theorem mkFlags_low_nibble_zero (z n h c : Bool) :
    mkFlags z n h c &&& 0x0F = 0 := by
  cases z <;> cases n <;> cases h <;> cases c <;> native_decide

/-- Consequence: after any ADD, the low nibble of F is zero. -/
theorem add_flags_low_nibble_zero (s : CPUState) (v : BitVec 8) :
    (execAddA s v).f &&& 0x0F = 0 := by
  simp only [execAddA]
  exact mkFlags_low_nibble_zero _ _ _ _

/-- Consequence: after any SUB, the low nibble of F is zero. -/
theorem sub_flags_low_nibble_zero (s : CPUState) (v : BitVec 8) :
    (execSub s v).f &&& 0x0F = 0 := by
  simp only [execSub]
  exact mkFlags_low_nibble_zero _ _ _ _

/-- Consequence: after any XOR, the low nibble of F is zero. -/
theorem xor_flags_low_nibble_zero (s : CPUState) (v : BitVec 8) :
    (execXor s v).f &&& 0x0F = 0 := by
  simp only [execXor]
  exact mkFlags_low_nibble_zero _ _ _ _

/-! ## 6. Memory Non-Interference (Frame Rule) -/

/-- Writing and reading the same address returns the written value. -/
theorem mem_write_read_same (s : CPUState) (a : BitVec 16) (val : BitVec 8) :
    (s.writeMem a val).readMem a = val := by
  simp [CPUState.writeMem, CPUState.readMem]

/-- Writing the same address twice: the second write wins. -/
theorem mem_write_write (s : CPUState) (a : BitVec 16) (v1 v2 : BitVec 8) :
    (s.writeMem a v1 |>.writeMem a v2).readMem a = v2 := by
  simp [CPUState.writeMem, CPUState.readMem]

/-! ## 7. Bitwise Absorption Laws -/

/-- AND with 0xFF is identity on A. -/
theorem and_ff_identity (s : CPUState) :
    (execAnd s 0xFF).a = s.a := by
  simp only [execAnd]
  have := (by native_decide : ∀ v : BitVec 8, v &&& 0xFF = v)
  exact this s.a

/-- OR with 0x00 is identity on A. -/
theorem or_zero_identity (s : CPUState) :
    (execOr s 0x00).a = s.a := by
  simp only [execOr]
  have := (by native_decide : ∀ v : BitVec 8, v ||| 0x00 = v)
  exact this s.a

/-- AND with 0x00 always zeros A. -/
theorem and_zero_annihilates (s : CPUState) :
    (execAnd s 0x00).a = 0 := by
  simp only [execAnd]
  have := (by native_decide : ∀ v : BitVec 8, v &&& 0x00 = (0 : BitVec 8))
  exact this s.a

/-- OR with 0xFF always gives 0xFF. -/
theorem or_ff_annihilates (s : CPUState) :
    (execOr s 0xFF).a = 0xFF := by
  simp only [execOr]
  have := (by native_decide : ∀ v : BitVec 8, v ||| 0xFF = (0xFF : BitVec 8))
  exact this s.a

/-- XOR is its own inverse: XOR x twice returns to A.
    This is the basis of the classic XOR encryption/swap trick. -/
theorem xor_xor_cancel (s : CPUState) (x : BitVec 8) :
    (execXor (execXor s x) x).a = s.a := by
  simp only [execXor]
  have := (by native_decide : ∀ a x : BitVec 8, (a ^^^ x) ^^^ x = a)
  exact this s.a x

/-! ## 8. Shift Composition Laws -/

/-- SLA then SRL does not perfectly roundtrip — it clears the MSB.
    This is the dual of the srl-then-sla property proved in Focus Energy. -/
theorem sla_then_srl_clears_msb (v : BitVec 8) :
    (execSrl (execSla v).1).1 = v &&& 0x7F := by
  simp only [execSla, execSrl]
  have := (by native_decide :
    ∀ b : BitVec 8, ((b <<< 1) >>> 1) = b &&& 0x7F)
  exact this v

/-- SRL then SLA clears the LSB. -/
theorem srl_then_sla_clears_lsb (v : BitVec 8) :
    (execSla (execSrl v).1).1 = v &&& 0xFE := by
  simp only [execSrl, execSla]
  have := (by native_decide :
    ∀ b : BitVec 8, ((b >>> 1) <<< 1) = b &&& 0xFE)
  exact this v

/-- SRL applied 8 times always gives 0. All bits have been shifted out. -/
theorem srl_8_times_zero (v : BitVec 8) :
    v >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = (0 : BitVec 8) := by
  have := (by native_decide :
    ∀ b : BitVec 8, b >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = (0 : BitVec 8))
  exact this v

/-- SLA applied 8 times always gives 0. All bits have been shifted out. -/
theorem sla_8_times_zero (v : BitVec 8) :
    v <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 = (0 : BitVec 8) := by
  have := (by native_decide :
    ∀ b : BitVec 8, b <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 <<< 1 = (0 : BitVec 8))
  exact this v

/-! ## 9. Through-Carry Rotation — RLA/RRA have period 9

    RLCA and RRCA rotate the 8 bits of A: period 8.
    RLA and RRA rotate A *through the carry flag*, creating a 9-bit cycle.
    The carry flag extends the orbit by one position, so the period is
    9 rather than 8. This is the key algebraic difference between the
    two flavors of rotation on the SM83. -/

/-- RLA has period 9: rotating A left through carry 9 times restores both A
    and the carry flag. Unlike RLCA (period 8), RLA treats A and carry as a
    single 9-bit register, adding one position to the cycle. -/
theorem rla_period_9 (a : BitVec 8) (c : Bool) :
    let rla := fun (p : BitVec 8 × Bool) =>
      ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
    rla (rla (rla (rla (rla (rla (rla (rla (rla (a, c))))))))) = (a, c) := by
  have := (by native_decide :
    ∀ a : BitVec 8, ∀ c : Bool,
      let rla := fun (p : BitVec 8 × Bool) =>
        ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
      rla (rla (rla (rla (rla (rla (rla (rla (rla (a, c))))))))) = (a, c))
  exact this a c

/-- RLA does NOT have period 3, so the minimal period is exactly 9.
    (Since 9 = 3², its only proper divisors are 1 and 3.) -/
theorem rla_not_period_3 :
    ∃ a : BitVec 8, ∃ c : Bool,
      let rla := fun (p : BitVec 8 × Bool) =>
        ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
      rla (rla (rla (a, c))) ≠ (a, c) := by
  exact ⟨1, false, by native_decide⟩

/-- RLA does NOT have period 8 — applying the RLCA loop count is a bug.
    A programmer who confuses RLCA (period 8) with RLA (period 9) gets
    corrupted data: the carry flag leaks into A on the 8th iteration. -/
theorem rla_not_period_8 :
    ∃ a : BitVec 8, ∃ c : Bool,
      let rla := fun (p : BitVec 8 × Bool) =>
        ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
      rla (rla (rla (rla (rla (rla (rla (rla (a, c)))))))) ≠ (a, c) := by
  exact ⟨0, true, by native_decide⟩

/-- Concrete carry leak: starting from (A=0x00, C=1), eight RLAs produce
    (A=0x80, C=0). The carry bit has traveled through all 8 positions of A
    and is now stranded in bit 7 — one more RLA is needed to push it home.
    This is the mechanism by which the period-8 assumption corrupts data. -/
theorem rla_8_carry_leak :
    let rla := fun (p : BitVec 8 × Bool) =>
      ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
    rla (rla (rla (rla (rla (rla (rla (rla ((0x00 : BitVec 8), true)))))))) =
      ((0x80 : BitVec 8), false) := by
  native_decide

/-- RRA also has period 9: right rotation through carry on 9 bits. -/
theorem rra_period_9 (a : BitVec 8) (c : Bool) :
    let rra := fun (p : BitVec 8 × Bool) =>
      ((p.1 >>> 1) ||| (if p.2 then (0x80 : BitVec 8) else 0), p.1.getLsbD 0)
    rra (rra (rra (rra (rra (rra (rra (rra (rra (a, c))))))))) = (a, c) := by
  have := (by native_decide :
    ∀ a : BitVec 8, ∀ c : Bool,
      let rra := fun (p : BitVec 8 × Bool) =>
        ((p.1 >>> 1) ||| (if p.2 then (0x80 : BitVec 8) else 0), p.1.getLsbD 0)
      rra (rra (rra (rra (rra (rra (rra (rra (rra (a, c))))))))) = (a, c))
  exact this a c

/-- RLA and RRA are inverses on the (A, carry) pair. -/
theorem rla_rra_inverse (a : BitVec 8) (c : Bool) :
    let rla := fun (p : BitVec 8 × Bool) =>
      ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
    let rra := fun (p : BitVec 8 × Bool) =>
      ((p.1 >>> 1) ||| (if p.2 then (0x80 : BitVec 8) else 0), p.1.getLsbD 0)
    rra (rla (a, c)) = (a, c) := by
  have := (by native_decide :
    ∀ a : BitVec 8, ∀ c : Bool,
      let rla := fun (p : BitVec 8 × Bool) =>
        ((p.1 <<< 1) ||| (if p.2 then (1 : BitVec 8) else 0), p.1.getLsbD 7)
      let rra := fun (p : BitVec 8 × Bool) =>
        ((p.1 >>> 1) ||| (if p.2 then (0x80 : BitVec 8) else 0), p.1.getLsbD 0)
      rra (rla (a, c)) = (a, c))
  exact this a c

/-! ## 10. SWAP decomposes as four rotations

    SWAP exchanges high and low nibbles. Four left rotations move each bit
    4 positions — exactly the same permutation. This connects two seemingly
    unrelated SM83 instructions through the cyclic group Z/8Z of rotations:
    SWAP is the unique element of order 2. -/

/-- SWAP is equivalent to four RLCA rotations: nibble-swapping IS rotating by 4. -/
theorem swap_eq_four_rlca (v : BitVec 8) :
    let rot1 (w : BitVec 8) := (w <<< 1) ||| (if w.getLsbD 7 then (1 : BitVec 8) else 0)
    rot1 (rot1 (rot1 (rot1 v))) = swapNibbles v := by
  have := (by native_decide :
    ∀ b : BitVec 8,
      let rot1 := fun (w : BitVec 8) => (w <<< 1) ||| (if w.getLsbD 7 then (1 : BitVec 8) else 0)
      rot1 (rot1 (rot1 (rot1 b))) = swapNibbles b)
  exact this v

/-! ## 11. SRA convergence — contrast with RLCA periodicity

    SRA (arithmetic right shift) preserves the sign bit, so it converges to
    a fixed point rather than cycling. Positive values (bit 7 = 0) converge
    to 0x00, negative values (bit 7 = 1) converge to 0xFF. After 7 shifts,
    the 7 non-sign bits have been replaced by copies of the sign bit. -/

/-- After 7 arithmetic right shifts, the result is a fixed point of SRA. -/
theorem sra_convergence (v : BitVec 8) :
    let sra (w : BitVec 8) := (w >>> 1) ||| (w &&& 0x80)
    let v7 := sra (sra (sra (sra (sra (sra (sra v))))))
    sra v7 = v7 := by
  have := (by native_decide :
    ∀ b : BitVec 8,
      let sra := fun (w : BitVec 8) => (w >>> 1) ||| (w &&& 0x80)
      let v7 := sra (sra (sra (sra (sra (sra (sra b))))))
      sra v7 = v7)
  exact this v

/-- SRA convergence target: positive bytes go to 0x00, negative to 0xFF. -/
theorem sra_converges_to_sign_extension (v : BitVec 8) :
    let sra (w : BitVec 8) := (w >>> 1) ||| (w &&& 0x80)
    let v7 := sra (sra (sra (sra (sra (sra (sra v))))))
    v7 = if v.getLsbD 7 then (0xFF : BitVec 8) else (0x00 : BitVec 8) := by
  have := (by native_decide :
    ∀ b : BitVec 8,
      let sra := fun (w : BitVec 8) => (w >>> 1) ||| (w &&& 0x80)
      let v7 := sra (sra (sra (sra (sra (sra (sra b))))))
      v7 = if b.getLsbD 7 then (0xFF : BitVec 8) else (0x00 : BitVec 8))
  exact this v

end SM83
