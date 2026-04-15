import SM83

namespace AutoResearch

/-!
# Bug: Substitute Creates 0 HP Shield and Leaves User at 0 HP

This file formalizes two bugs in the Pokemon Red/Blue `Substitute` move:
1.  **Zero-HP Substitute**: If Max HP < 4, the cost (MaxHP / 4) rounds to 0. 
    The game creates a substitute with 0 HP.
2.  **User at 0 HP**: The game checks for underflow (`jr c`) but not for a zero 
    result. If `Current HP == Cost`, the user is left at 0 HP, which is 
    normally an impossible state for a non-fainted Pokemon.
-/

/-- 
Simulates the SM83 assembly for calculating cost:
`ld a, [hli]`, `ld b, [hl]`, `srl a`, `rr b`, `srl a`, `rr b`.
This shifts the 16-bit Max HP right by 2 and takes the lower 8 bits.
-/
def calculateCost (maxHP : BitVec 16) : BitVec 8 :=
  (maxHP >>> 2).toBitVec 8

/-- Outcomes of the Substitute effect. -/
inductive SubstituteResult
  | success (userHP : BitVec 16) (subHP : BitVec 8)
  | tooWeak
  deriving DecidableEq, Repr

/-- 
Faithful model of `SubstituteEffect_` in `engine/battle/move_effects/substitute.asm`.
Note the lack of checks for `cost == 0` and the use of `jr c` (carry flag) 
which only triggers if `currHP < cost`.
-/
def impl (currHP maxHP : BitVec 16) : SubstituteResult :=
  let cost8 := calculateCost maxHP
  let cost16 := cost8.toBitVec 16
  -- jr c, .notEnoughHP
  if currHP.toNat < cost16.toNat then
    SubstituteResult.tooWeak
  else
    SubstituteResult.success (currHP - cost16) cost8

/-- 
The intended behavior of Substitute:
1. Cost must be at least 1.
2. Resulting HP must be at least 1.
-/
def spec (currHP maxHP : BitVec 16) : SubstituteResult :=
  let cost8 := calculateCost maxHP
  let cost16 := cost8.toBitVec 16
  if cost8 == 0 || currHP.toNat <= cost16.toNat then
    SubstituteResult.tooWeak
  else
    SubstituteResult.success (currHP - cost16) cost8

/-- L1: Bug 1 - A 0-HP substitute can be created. -/
theorem bug_zero_hp_sub_exists : ∃ curr max, 
  match impl curr max with
  | SubstituteResult.success _ subHP => subHP == 0
  | _ => False := by
  -- Max HP 3, Curr HP 3. Cost = 3 >> 2 = 0.
  use BitVec.ofNat 16 3, BitVec.ofNat 16 3
  native_decide

/-- L1: Bug 2 - The user can be left with exactly 0 HP. -/
theorem bug_user_at_zero_hp_exists : ∃ curr max,
  match impl curr max with
  | SubstituteResult.success userHP _ => userHP == 0
  | _ => False := by
  -- Max HP 4, Curr HP 1. Cost = 4 >> 2 = 1. Remaining = 0.
  use BitVec.ofNat 16 1, BitVec.ofNat 16 4
  native_decide

/-- L2: Logic Characterization.
The implementation differs from the specification if and only if 
the cost is zero OR the user would be left with exactly zero HP.
-/
theorem bug_characterization (curr max : BitVec 16) :
  impl curr max ≠ spec curr max ↔ 
  (calculateCost max = 0 ∧ curr.toNat >= (calculateCost max).toBitVec 16 |>.toNat) ∨ 
  (curr.toNat = (calculateCost max).toBitVec 16 |>.toNat) := by
  unfold impl spec
  let cost := calculateCost max
  let c16 := cost.toBitVec 16
  split <;> split <;> simp_all
  · -- Case 1: impl success, spec tooWeak
    omega
  · -- Case 2: impl tooWeak, spec success
    -- This case is impossible because spec is stricter than impl
    omega

/-- L2: The bug always triggers if current HP is exactly equal to cost (and cost > 0). -/
theorem bug_triggers_at_exact_cost (n : Nat) (h_pos : n > 0) (h_limit : n < 256) :
  let cost := BitVec.ofNat 16 n
  let max  := BitVec.ofNat 16 (4 * n)
  match impl cost max with
  | SubstituteResult.success userHP _ => userHP = 0
  | _ => False := by
  intro cost max
  unfold impl calculateCost
  have h_c : (BitVec.ofNat 16 (4 * n) >>> 2).toBitVec 8 = BitVec.ofNat 8 n := by
    simp [BitVec.ofNat, BitVec.toBitVec]
    rw [Nat.shiftRight_eq_div_pow]
    simp; rw [Nat.mul_div_cancel _ (by omega)]
    split <;> split <;> simp <;> omega
  simp [h_c, cost]
  exact BitVec.sub_self (BitVec.ofNat 16 n)

/-- L3: Fix Correctness. 
A fixed implementation that explicitly checks for cost > 0 and result > 0 matches spec.
-/
def fix (currHP maxHP : BitVec 16) : SubstituteResult :=
  let cost8 := calculateCost maxHP
  let cost16 := cost8.toBitVec 16
  if cost8 == 0 then SubstituteResult.tooWeak
  else if currHP.toNat <= cost16.toNat then SubstituteResult.tooWeak
  else SubstituteResult.success (currHP - cost16) cost8

theorem fix_is_correct (curr max : BitVec 16) : fix curr max = spec curr max := by
  unfold fix spec
  split <;> simp_all

end AutoResearch
