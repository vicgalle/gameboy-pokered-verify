import SM83

namespace AutoResearch

/-!
# Bug #4: heal_overflow

Recovery moves like Recover, Softboiled, and Rest are supposed to restore a Pokemon's HP. 
However, due to an incorrect 16-bit comparison in the Game Boy's SM83 assembly, 
the move incorrectly determines the Pokemon is at "Full HP" if the gap between 
Max HP and Current HP is a multiple of 256 minus 1 (e.g., 255 or 511).

The bug occurs because the high-byte comparison (`cp [hl]`) sets the carry flag 
if CurrentHP_Hi < MaxHP_Hi. This carry is then subtracted from the low-byte 
result in `sbc [hl]`. If the result is zero, the game assumes CurrentHP == MaxHP.
-/

/-- 
Models the buggy "already at full HP?" check from `HealEffect_` in `heal.asm`.
Returns true if the check mistakenly decides the Pokemon is at full HP.
-/
def impl (h_curr l_curr h_max l_max : BitVec 8) : Bool :=
  -- ld a, [de] ; current HP high
  -- cp [hl]    ; compare with max HP high (Sets Carry if h_curr < h_max)
  let carry := h_curr < h_max
  -- inc de; inc hl
  -- ld a, [de] ; current HP low
  -- sbc [hl]   ; result = l_curr - l_max - carry
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
  -- Curr: 0x0101 (257), Max: 0x0200 (512). Gap: 255.
  ⟨0x01, 0x01, 0x02, 0x00, by native_decide⟩

/-- 
L2: The bug triggers specifically at a gap of 255.
-/
theorem bug_triggers_at_255_gap : 
  let h_c := (0x00 : BitVec 8); let l_c := (0x01 : BitVec 8) -- HP: 1
  let h_m := (0x01 : BitVec 8); let l_m := (0x00 : BitVec 8) -- HP: 256
  impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false := by
  native_decide

/--
L2: The bug triggers specifically at a gap of 511.
-/
theorem bug_triggers_at_511_gap : 
  let h_c := (0x00 : BitVec 8); let l_c := (0x01 : BitVec 8) -- HP: 1
  let h_m := (0x02 : BitVec 8); let l_m := (0x00 : BitVec 8) -- HP: 512
  impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false := by
  native_decide

/--
L2: Universal Characterization.
The bug triggers (impl is true but spec is false) if and only if:
The high byte of Max HP is strictly greater than Current HP,
AND the low byte of Current HP is exactly 1 greater than Max HP's low byte.
-/
theorem bug_iff (h_c l_c h_m l_m : BitVec 8) :
  (impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false) ↔ 
  (h_c < h_m ∧ l_c = l_m + 1) := by
  have := (by native_decide : ∀ h_c l_c h_m l_m : BitVec 8, 
    (impl h_c l_c h_m l_m = true ∧ spec h_c l_c h_m l_m = false) ↔ 
    (h_c < h_m ∧ l_c = l_m + 1))
  exact this h_c l_c h_m l_m

/--
L2: Full correctness of the check. 
The SM83 check `impl` only returns true if HP is actually full 
OR if the specific bug condition is met.
-/
theorem impl_is_correct_or_buggy (h_c l_c h_m l_m : BitVec 8) :
  impl h_c l_c h_m l_m = true ↔ 
  (spec h_c l_c h_m l_m = true ∨ (h_c < h_m ∧ l_c = l_m + 1)) := by
  have := (by native_decide : ∀ h_c l_c h_m l_m : BitVec 8, 
    impl h_c l_c h_m l_m = true ↔ 
    (spec h_c l_c h_m l_m = true ∨ (h_c < h_m ∧ l_c = l_m + 1)))
  exact this h_c l_c h_m l_m

/-- 
L3: Fix Correctness.
A proper fix requires checking both high and low bytes for equality 
without letting the high-byte comparison pollute the low-byte subtraction 
via the carry flag.
-/
def fix (h_c l_c h_m l_m : BitVec 8) : Bool :=
  (h_c == h_m) && (l_c == l_m)

theorem fix_correct (h_c l_c h_m l_m : BitVec 8) : 
  fix h_c l_c h_m l_m = spec h_c l_c h_m l_m := by
  rfl

/--
L4: Numeric Characterization.
If we consider the 16-bit values, the bug triggers exactly when
the gap (MaxHP - CurrHP) is of the form 256*k - 1 for k > 0.
This theorem demonstrates this for k=1 (255) and k=2 (511).
-/
theorem gap_numeric_property (h_c l_c h_m l_m : BitVec 8) :
  let cur := h_c.toNat * 256 + l_c.toNat
  let max := h_m.toNat * 256 + l_m.toNat
  (h_c < h_m ∧ l_c = l_m + 1) → ∃ k, k > 0 ∧ max - cur = 256 * k - 1 := by
  intro h
  let k := h_m.toNat - h_c.toNat
  use k
  constructor
  · have h_lt := BitVec.toNat_lt_toNat_of_lt h.1
    omega
  · have h_l := h.2
    have h_l_nat : l_c.toNat = (l_m.toNat + 1) % 256 := by
      rw [←BitVec.toNat_add l_m 1]
      apply congr_arg BitVec.toNat h_l
    -- Case split on whether l_m + 1 wrapped around 256
    by_cases h_wrap : l_m.toNat < 255
    · have h_l_val : l_c.toNat = l_m.toNat + 1 := by
        rw [h_l_nat, Nat.mod_eq_of_lt]
        omega
      simp [h_l_val]
      have h_h_nat : h_m.toNat > h_c.toNat := BitVec.toNat_lt_toNat_of_lt h.1
      omega
    · have h_l_max : l_m.toNat = 255 := by omega
      have h_l_val : l_c.toNat = 0 := by
        rw [h_l_nat, h_l_max]
        native_decide
      simp [h_l_val, h_l_max]
      have h_h_nat : h_m.toNat > h_c.toNat := BitVec.toNat_lt_toNat_of_lt h.1
      omega

end AutoResearch
