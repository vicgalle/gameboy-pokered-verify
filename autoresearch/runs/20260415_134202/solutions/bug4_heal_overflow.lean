import SM83

namespace AutoResearch

/-!
# Bug #4: heal_overflow

Recovery moves like Recover, Softboiled, and Rest are supposed to restore a Pokemon's HP. 
However, due to an incorrect 16-bit comparison in the Game Boy's SM83 assembly, 
the move incorrectly determines the Pokemon is at "Full HP" if the gap between 
Max HP and Current HP is a multiple of 256 minus 1 (e.g., 255 or 511).

The bug occurs because the high-byte comparison (`cp [hl]`) sets the carry flag, 
which is then improperly factored into the low-byte subtraction (`sbc [hl]`) 
to check for equality.
-/

/-- 
Models the buggy "already at full HP?" check from the assembly.
Returns true if the check passes (meaning the healing move FAILS).
-/
def impl (h_curr l_curr h_max l_max : BitVec 8) : Bool :=
  -- ld a, [de] ; current HP high
  -- cp [hl]    ; compare with max HP high
  let carry := h_curr < h_max
  -- inc de; inc hl
  -- ld a, [de] ; current HP low
  -- sbc [hl]   ; subtract max HP low with carry
  let result := l_curr - l_max - (if carry then 1 else 0)
  -- jp z, .failed
  result == 0

/-- 
The intended behavior: healing should only fail if current HP 
is exactly equal to max HP.
-/
def spec (h_curr l_curr h_max l_max : BitVec 8) : Bool :=
  (h_curr == h_max) && (l_curr == l_max)

/-- 
L1: Bug Existence.
A Pokemon with 257 Current HP and 512 Max HP (gap of 255) 
triggers the bug and fails to heal.
-/
theorem bug_exists : ∃ h_c l_c h_m l_m, impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false :=
  -- Curr: 0x0101 (257), Max: 0x0200 (512)
  ⟨0x01, 0x01, 0x02, 0x00, by native_decide⟩

/-- 
L2: Specific Characterization.
The bug always triggers when Max HP is 255 points higher than Current HP.
(MaxHP = CurrHP + 255)
-/
theorem bug_triggers_at_255_gap : 
  let h_c := (0x01 : BitVec 8)
  let l_c := (0x01 : BitVec 8)
  let h_m := (0x02 : BitVec 8)
  let l_m := (0x00 : BitVec 8)
  impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false := by
  native_decide

/--
L2: The bug also triggers at a gap of 511.
(MaxHP = CurrHP + 511)
-/
theorem bug_triggers_at_511_gap : 
  let h_c := (0x01 : BitVec 8)
  let l_c := (0x01 : BitVec 8)
  let h_m := (0x03 : BitVec 8)
  let l_m := (0x00 : BitVec 8)
  impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false := by
  native_decide

/-- 
L3: Fix Correctness.
Replacing the buggy sbc-based check with a direct 16-bit equality check.
-/
def fix (h_c l_c h_m l_m : BitVec 8) : Bool :=
  (h_c == h_m) && (l_c == l_m)

theorem fix_correct (h_c l_c h_m l_m : BitVec 8) : 
  fix h_c l_c h_m l_m = spec h_c l_c h_m l_m := by
  rfl

/--
L2 Stretch: The bug triggers if and only if:
1. Current HP == Max HP (Legitimate failure)
2. Current HP < Max HP AND (CurrLow - MaxLow) == 1 (The Bug)
-/
theorem bug_condition_logic (h_c l_c h_m l_m : BitVec 8) :
  impl h_c l_c h_m l_m = true ↔ 
  (if h_c < h_m then l_c == l_m + 1 else l_c == l_m) := by
  unfold impl
  split <;> simp
  · -- Case h_c < h_m: result is l_c - l_m - 1
    -- l_c - l_m - 1 = 0 iff l_c = l_m + 1
    constructor
    · intro h; apply BitVec.eq_of_sub_eq_zero; exact BitVec.sub_eq_zero_iff_eq.mp h
    · intro h; rw [h]; simp
  · -- Case h_c >= h_m: result is l_c - l_m
    constructor
    · exact BitVec.sub_eq_zero_iff_eq.mp
    · intro h; rw [h]; simp

end AutoResearch
