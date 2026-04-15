/-
  SM83/Basic.lean — BitVec helpers for the SM83 CPU model.
-/

namespace SM83

/-- Extract the high byte of a 16-bit value. -/
def hi (v : BitVec 16) : BitVec 8 := v.extractLsb' 8 8

/-- Extract the low byte of a 16-bit value. -/
def lo (v : BitVec 16) : BitVec 8 := v.extractLsb' 0 8

/-- Combine two 8-bit values into a 16-bit value (hi ++ lo). -/
def mk16 (high low : BitVec 8) : BitVec 16 := high ++ low

/-- Sign-extend an 8-bit value to 16 bits (for relative jumps). -/
def signExtend8to16 (v : BitVec 8) : BitVec 16 := v.signExtend 16

/-- Check if bit `n` is set in an 8-bit value. -/
def testBit8 (v : BitVec 8) (n : Nat) : Bool := v.getLsbD n

/-- Set bit `n` in an 8-bit value. -/
def setBit8 (v : BitVec 8) (n : Nat) : BitVec 8 :=
  let mask : BitVec 8 := 1 <<< n
  v ||| mask

/-- Reset (clear) bit `n` in an 8-bit value. -/
def resBit8 (v : BitVec 8) (n : Nat) : BitVec 8 :=
  let mask : BitVec 8 := 1 <<< n
  v &&& ~~~mask

/-- Swap the high and low nibbles of an 8-bit value. -/
def swapNibbles (v : BitVec 8) : BitVec 8 :=
  (v >>> 4) ||| (v <<< 4)

end SM83
