/-
  PokeredBugs/Proofs/HealOverflow.lean — Heal move fails at 255/511/767 HP gap.

  ## The Bug
  The heal moves (Recover, Softboiled, Rest) first check if the Pokémon is
  already at full HP. The check at heal.asm lines 13-20 is:

    ld a, [de]      ; a = currentHP_hi (big-endian: high byte first)
    cp [hl]         ; compare with maxHP_hi → sets carry/borrow
    inc de / inc hl
    ld a, [de]      ; a = currentHP_lo
    sbc [hl]        ; a = currentHP_lo - maxHP_lo - borrow
    jp z, .failed   ; if zero: "But it failed!"

  This is a broken 16-bit equality check. `jp z` only checks if the LOW byte
  subtraction-with-borrow gives zero — it doesn't verify the full 16-bit
  equality. The move incorrectly fails when the high bytes differ AND the
  low bytes satisfy `currentHP_lo ≡ maxHP_lo + 1 (mod 256)`.

  This happens at HP gaps of 255, 511, and 767 (the values 256k-1 for k≥1,
  but only when maxHP ≥ 256 so the high bytes actually differ).

  Source: engine/battle/move_effects/heal.asm lines 13-20
-/
import SM83

namespace PokeredBugs

/-! ### Model -/

/-- Extract high byte (big-endian: first byte in memory). -/
def hiBE (v : Nat) : Nat := v / 256

/-- Extract low byte (big-endian: second byte in memory). -/
def loBE (v : Nat) : Nat := v % 256

/-- The buggy "already at full HP" check from heal.asm.
    Returns true if the move FAILS (correctly or incorrectly).
    Models: cp [hl]; sbc [hl]; jp z. -/
def healCheckFails (currentHP maxHP : Nat) : Bool :=
  let curHi := hiBE currentHP
  let curLo := loBE currentHP
  let maxHi := hiBE maxHP
  let maxLo := loBE maxHP
  let borrow : Nat := if curHi < maxHi then 1 else 0
  let sbcResult := (curLo + 256 - maxLo - borrow) % 256
  sbcResult == 0

/-! ### Proof 1: The Bug Exists -/

/-- At maxHP=300, currentHP=45 (gap=255): the move incorrectly fails. -/
theorem heal_fails_at_gap_255 :
    healCheckFails 45 300 = true ∧ 300 - 45 = 255 := by native_decide

/-- At maxHP=600, currentHP=89 (gap=511): the move incorrectly fails. -/
theorem heal_fails_at_gap_511 :
    healCheckFails 89 600 = true ∧ 600 - 89 = 511 := by native_decide

/-- At maxHP=999, currentHP=232 (gap=767): the move incorrectly fails. -/
theorem heal_fails_at_gap_767 :
    healCheckFails 232 999 = true ∧ 999 - 232 = 767 := by native_decide

/-! ### Proof 2: The Bug Does NOT Trigger for maxHP ≤ 255 -/

/-- When maxHP ≤ 255, the check is correct: only fails at full HP.
    Gap of 255 does NOT trigger because the high bytes are both 0. -/
theorem no_false_fail_below_256 :
    ∀ c m : BitVec 8,
      c.toNat ≤ m.toNat →
      healCheckFails c.toNat m.toNat = true →
      c.toNat = m.toNat := by
  native_decide

/-! ### Proof 3: Exact False Failure Enumeration -/

/-- For maxHP ≤ 999 and currentHP ≤ maxHP: if the check triggers and
    the Pokémon is NOT at full HP, the gap must be 255, 511, or 767. -/
theorem bad_gaps_enumerated (currentHP maxHP : Nat)
    (hle : currentHP ≤ maxHP) (hmax : maxHP ≤ 999) (hneq : currentHP ≠ maxHP)
    (hfail : healCheckFails currentHP maxHP = true) :
    maxHP - currentHP = 255 ∨ maxHP - currentHP = 511 ∨ maxHP - currentHP = 767 := by
  have key := (by native_decide :
    ∀ c : Fin 1000, ∀ m : Fin 1000,
      c.val ≤ m.val → c.val ≠ m.val →
      healCheckFails c.val m.val = true →
      m.val - c.val = 255 ∨ m.val - c.val = 511 ∨ m.val - c.val = 767)
  exact key ⟨currentHP, by omega⟩ ⟨maxHP, by omega⟩ hle hneq hfail

/-! ### Proof 4: Adjacent HP Values Work Fine -/

/-- One HP more or less than the bug trigger, the move works. -/
theorem adjacent_works :
    healCheckFails 46 300 = false ∧   -- gap 254: fine
    healCheckFails 44 300 = false ∧   -- gap 256: fine
    healCheckFails 90 600 = false ∧   -- gap 510: fine
    healCheckFails 88 600 = false := by -- gap 512: fine
  native_decide

/-! ### Proof 5: The Correct Check -/

/-- A correct 16-bit equality check (both bytes compared). -/
def healCheckCorrect (currentHP maxHP : Nat) : Bool :=
  currentHP == maxHP

/-- The correct check never has false failures. -/
theorem correct_no_false_fail (currentHP maxHP : Nat)
    (hlt : currentHP < maxHP) :
    healCheckCorrect currentHP maxHP = false := by
  simp [healCheckCorrect]; omega

/-! ### Proof 6: Concrete Gameplay Scenarios -/

/-- Snorlax: maxHP ≈ 524. Using Rest at HP 269 (gap=255): fails! -/
theorem snorlax_rest_fails :
    healCheckFails 269 524 = true ∧ 524 - 269 = 255 := by native_decide

/-- Chansey: maxHP ≈ 703.
    Softboiled at HP 448 (gap=255): fails! At ~64% health. -/
theorem chansey_softboiled_fails :
    healCheckFails 448 703 = true ∧ 703 - 448 = 255 := by native_decide

/-- Chansey at HP 192 (gap=511): also fails! -/
theorem chansey_softboiled_511 :
    healCheckFails 192 703 = true ∧ 703 - 192 = 511 := by native_decide

/-- But gap=255 with maxHP=255: does NOT fail (high bytes are the same). -/
theorem low_maxhp_no_bug :
    healCheckFails 0 255 = false := by native_decide

/-! ### #eval Demonstrations -/

-- Gap = 255 at various maxHP values
#eval
  let maxHPs := [255, 256, 300, 400, 500, 524, 600, 703, 800, 999]
  maxHPs.map fun m => (m, m - 255, healCheckFails (m - 255) m)

-- Gap = 511
#eval
  let maxHPs := [511, 512, 600, 703, 800, 999]
  maxHPs.map fun m => (m, m - 511, healCheckFails (m - 511) m)

end PokeredBugs
