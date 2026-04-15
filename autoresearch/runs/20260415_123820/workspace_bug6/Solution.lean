import Mathlib.Data.BitVec.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Bug #6: Substitute HP Calculation Bugs

## Description
In Pokémon Red/Blue, the move Substitute contains two separate HP-related bugs:

1. **Zero-HP Substitute**: The substitute's HP is calculated as `floor(MaxHP / 4)`.
   If the user's Max HP is between 1 and 3, this value rounds down to 0. 
   The game allows the creation of a substitute with 0 HP, which breaks 
   immediately upon being created or on the first hit.

2. **User left at 0 HP**: To check if the user has enough HP to create a 
   substitute, the routine subtracts the cost from the current HP and 
   branches to failure only if a carry occurs (`jr c`). If `Current HP` 
   is exactly equal to the cost, the subtraction results in 0 with no 
   carry, allowing the user to remain in battle with 0 HP—a state 
   normally reserved for fainted Pokémon.

## Formalization
We model HP as `BitVec 16`. The substitute's HP storage is `BitVec 8`.
-/

namespace SubstituteBug

/-- 
Models the 16-bit division by 4 used in the assembly:
`srl a; rr b; srl a; rr b` 
This performs a logical right shift on the 16-bit pair (A, B).
The routine then stores the low byte `B` as the cost.
-/
def calculateCost (maxHP : BitVec 16) : BitVec 8 :=
  (maxHP >>> 2).toBitVec 8

/-- 
Models the SM83 carry-based check:
`sub b`
`ld d, a`
`ld a, [hl]`
`sbc 0`
`jr c, .notEnoughHP`
The carry flag is set if `currHP < cost`.
-/
def canAfford (currHP : BitVec 16) (cost : BitVec 8) : Bool :=
  -- In SM83, SUB/SBC sets carry if borrow is needed.
  -- This happens if currHP < cost.
  !(currHP.toNat < cost.toNat)

/-- The resulting HP if the move is successful (no carry). -/
def applyCost (currHP : BitVec 16) (cost : BitVec 8) : BitVec 16 :=
  currHP - cost.toBitVec 16

/-! ### Bug 1: Zero-HP Substitute -/

/-- A bug occurs if Max HP > 0 but the resulting substitute HP is 0. -/
def isZeroHPSubstituteBug (maxHP : BitVec 16) : Prop :=
  maxHP.toNat > 0 ∧ calculateCost maxHP == 0

/-- L1: Prove the bug exists for Max HP = 1, 2, or 3. -/
theorem bug1_exists : ∃ (h : BitVec 16), isZeroHPSubstituteBug h := by
  use BitVec.ofNat 16 3
  native_decide

/-- L2: Characterize the bug for all "standard" HP values (below 1024). -/
theorem bug1_characterization (h : BitVec 16) (h_limit : h.toNat < 1024) : 
  isZeroHPSubstituteBug h ↔ (h.toNat >= 1 ∧ h.toNat <= 3) := by
  unfold isZeroHPSubstituteBug calculateCost
  constructor
  · intro ⟨h_pos, h_cost⟩
    have h_val := h.toNat
    -- BitVec 8 being 0 means the original value was 0, 256, 512, or 768.
    -- Since h < 1024, h/4 < 256. Thus h/4 must be 0.
    have h_div : (h >>> 2).toNat = h_val / 4 := by simp [BitVec.toNat_ushiftRight]
    have h_cost_nat : (calculateCost h).toNat = (h_val / 4) % 256 := by
      simp [calculateCost, BitVec.toNat_toBitVec, h_div]
    rw [h_cost_nat] at h_cost
    have h_is_zero : h_val / 4 = 0 := by
      have : h_val / 4 < 256 := by omega
      exact Nat.eq_zero_of_add_pow_mod_self this (by simp at h_cost; exact h_cost)
    omega
  · intro ⟨h1, h2⟩
    simp [BitVec.toNat_ushiftRight]
    constructor
    · omega
    · apply BitVec.eq_of_toNat_eq
      simp [calculateCost, BitVec.toNat_toBitVec, BitVec.toNat_ushiftRight]
      omega

/-! ### Bug 2: User left at 0 HP -/

/-- 
A bug occurs if the user can afford the move, but the resulting HP is 0.
We exclude cases where cost is 0 (Bug 1) to isolate the behavior.
-/
def isZeroHPUserBug (currHP : BitVec 16) (maxHP : BitVec 16) : Prop :=
  let cost := calculateCost maxHP
  cost.toNat > 0 ∧ canAfford currHP cost ∧ applyCost currHP cost == 0

/-- L1: Prove the bug exists (e.g., Max HP 40, Current HP 10). -/
theorem bug2_exists : ∃ (curr max : BitVec 16), isZeroHPUserBug curr max := by
  use BitVec.ofNat 16 10, BitVec.ofNat 16 40
  native_decide

/-- L2: The bug triggers specifically when current HP exactly equals the cost. -/
theorem bug2_characterization (curr max : BitVec 16) :
  isZeroHPUserBug curr max ↔ (calculateCost max > 0 ∧ curr.toNat = (calculateCost max).toNat) := by
  simp [isZeroHPUserBug, canAfford, applyCost]
  constructor
  · intro ⟨h_pos, h_afford, h_zero⟩
    constructor
    · exact h_pos
    · have h_curr := curr.toNat
      have h_cost := (calculateCost max).toNat
      -- Since h_afford is true, curr.toNat >= cost.toNat.
      -- Thus subtraction in Nat is exactly what BitVec.sub does (mod 2^16).
      have h_sub := BitVec.toNat_sub curr (calculateCost max).toBitVec
      simp [h_zero] at h_sub
      have h_lt : (calculateCost max).toBitVec 16 < 2^16 := by
        apply Nat.lt_trans (BitVec.toNat_lt _) (by decide)
      rw [Nat.sub_mod_eq_zero_of_le] at h_sub
      · exact h_sub
      · omega
  · intro ⟨h_pos, h_eq⟩
    constructor
    · exact h_pos
    · constructor
      · omega
      · apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_sub, h_eq]

/-! ### L3: Fix Correctness -/

/-- 
The intended behavior:
1. If maxHP/4 is 0, cost is at least 1.
2. User must have STRICTLY more HP than the cost.
-/
structure Fix where
  cost : BitVec 8
  canAfford : Bool
  resultingHP : BitVec 16

def substituteFix (currHP : BitVec 16) (maxHP : BitVec 16) : Fix :=
  let c := calculateCost maxHP
  -- Fix 1: Minimum cost of 1
  let actualCost := if c == 0 then BitVec.ofNat 8 1 else c
  -- Fix 2: Use > instead of >= (i.e. check for 0 result)
  let afford := currHP.toNat > actualCost.toNat
  ⟨actualCost, afford, currHP - actualCost.toBitVec 16⟩

/-- Prove the fix prevents both bugs. -/
theorem fix_is_safe (curr max : BitVec 16) (h_max_pos : max.toNat > 0) :
  let res := substituteFix curr max
  res.canAfford → (res.cost.toNat > 0 ∧ res.resultingHP.toNat > 0) := by
  intro res h_afford
  unfold substituteFix at *
  simp at *
  constructor
  · -- Prove cost > 0
    split at h_afford
    · rename_i h_c_zero
      simp [h_c_zero]
    · rename_i h_c_nz
      apply Nat.pos_of_ne_zero
      intro h_abs
      exact h_c_nz (BitVec.eq_of_toNat_eq (by simp [h_abs]))
  · -- Prove resulting HP > 0
    have h_cost_lt : (if calculateCost max == 0 then BitVec.ofNat 8 1 else calculateCost max).toBitVec 16 < 2^16 := by
      split <;> apply Nat.lt_trans (BitVec.toNat_lt _) (by decide)
    simp [BitVec.toNat_sub, h_cost_lt]
    rw [Nat.mod_eq_of_lt]
    · omega
    · apply Nat.lt_trans (Nat.sub_lt_of_pos_le _ _ _ _) (BitVec.toNat_lt _)
      · apply Nat.pos_of_ne_zero
        intro h_abs; simp [h_abs] at h_afford
      · omega

/-! ### L4: Relational Property (Invariants) -/

/-- 
The "HP Conservation" Law: 
The sum of User HP and Substitute HP should equal the original HP if the move succeeds.
This is violated by Bug 1 (cost 0, but substitute gets HP).
Wait, Bug 1 actually gives the substitute 0 HP, which is consistent but useless.
The real violation is Bug 2 where the user effectively "dies" while creating a shield.
-/
theorem bug2_violates_vitality (curr max : BitVec 16) :
  isZeroHPUserBug curr max → (applyCost curr (calculateCost max)).toNat = 0 := by
  intro h
  rcases (bug2_characterization curr max).mp h with ⟨_, h_eq⟩
  simp [applyCost, h_eq]
  apply BitVec.toNat_sub_eq_zero_of_toNat_le
  simp [h_eq]

end SubstituteBug
