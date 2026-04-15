import SM83

/-!
# Bug #6: Substitute HP Logic Bugs

This file formalizes two distinct bugs in the SM83 assembly for the move Substitute:
1. **Zero-HP Substitute**: Integer division `MaxHP / 4` rounds to 0 for small MaxHP,
   creating a decoy with 0 HP.
2. **User at 0 HP**: The routine only checks for underflow (carry flag), allowing
   the user's HP to reach exactly 0, which should be a fainted state.

The assembly logic:
- `cost = maxHP / 4` (via 16-bit right shifts)
- `newHP = curHP - cost`
- `if newHP < 0 (Carry) then failure else success`
-/

namespace AutoResearch

/-- Represents the relevant battle state for the Substitute routine. -/
structure BattleState where
  /-- Pokemon Max HP (wBattleMonMaxHP). Max 1023 in Gen 1. -/
  maxHP : BitVec 16
  /-- Pokemon Current HP (wBattleMonHP). -/
  curHP : BitVec 16
  deriving DecidableEq, Repr

/-- The output of the Substitute move effect. -/
structure SubResult where
  userHP    : BitVec 16
  subHP     : BitVec 8
  success   : Bool
  deriving DecidableEq, Repr

/-- 
  Buggy implementation matching `SubstituteEffect_` in `substitute.asm`.
  The routine performs a 16-bit subtraction and branches only on Carry (`jr c`).
-/
def impl (s : BattleState) : SubResult :=
  let cost := s.maxHP.toNat / 4
  -- The assembly performs: curHP - cost
  -- Success is determined by the absence of a carry flag (curHP >= cost)
  let success := s.curHP.toNat >= cost
  if success then
    { userHP := s.curHP - BitVec.ofNat 16 cost,
      subHP  := BitVec.ofNat 8 cost,
      success := true }
  else
    { userHP  := s.curHP,
      subHP   := 0,
      success := false }

/-- 
  Intended behavior (Specification):
  1. The user must have strictly MORE HP than the cost (cannot be left at 0).
  2. The cost must be at least 1 (cannot create a 0-HP substitute).
-/
def spec (s : BattleState) : SubResult :=
  let cost := s.maxHP.toNat / 4
  let canAfford := s.curHP.toNat > cost
  let isValid   := cost > 0
  if canAfford && isValid then
    { userHP := s.curHP - BitVec.ofNat 16 cost,
      subHP  := BitVec.ofNat 8 cost,
      success := true }
  else
    { userHP  := s.curHP,
      subHP   := 0,
      success := false }

/-! ### L1: Bug Existence (Witnesses) -/

/-- Bug 1: A Pokemon with 2 Max HP creates a 0-HP Substitute for free. -/
theorem bug1_zero_hp_sub_exists : ∃ s, (impl s).success ∧ (impl s).subHP = 0 :=
  ⟨{ maxHP := 2, curHP := 2 }, by native_decide⟩

/-- Bug 2: A Pokemon with 4 HP and 4 Max HP is left at 0 HP. -/
theorem bug2_user_at_zero_exists : ∃ s, (impl s).success ∧ (impl s).userHP = 0 :=
  ⟨{ maxHP := 4, curHP := 1 }, by native_decide⟩

/-! ### L2: Characterization -/

/-- The bug triggers if and only if the routine succeeds when it should have failed. -/
theorem bug_iff_success_mismatch (s : BattleState) :
  impl s ≠ spec s ↔ ((impl s).success ∧ ¬(spec s).success) := by
  unfold impl spec
  split <;> split <;> simp_all
  · -- Both successful: only mismatch if results differ (impossible here)
    intro h; cases h; omega
  · -- Impl success, Spec failure: this is the bug condition
    exact iff_true_intro rfl
  · -- Impl failure, Spec success: mathematically impossible (curHP < cost -> not curHP > cost)
    omega

/-- Specifically, the bug triggers when cost is 0 OR remaining HP is 0. -/
theorem bug_condition_logic (s : BattleState) :
  impl s ≠ spec s ↔ ((impl s).success ∧ ((impl s).subHP = 0 ∨ (impl s).userHP = 0)) := by
  unfold impl spec
  split <;> split <;> simp_all
  · intro h; cases h; omega
  · intro _; constructor <;> [rfl, omega]
  · omega

/-! ### L3: Fix Correctness -/

/-- 
  Fixed implementation. 
  In assembly, this would require:
  1. `ld a, b; and a; jr z, .notEnoughHP` (check cost > 0)
  2. Checking the result of subtraction is not zero (`or d` after `sbc`).
-/
def fix (s : BattleState) : SubResult :=
  let cost := s.maxHP.toNat / 4
  -- Check: cost > 0 AND curHP - cost > 0
  if cost > 0 && s.curHP.toNat > cost then
    { userHP := s.curHP - BitVec.ofNat 16 cost,
      subHP  := BitVec.ofNat 8 cost,
      success := true }
  else
    { userHP  := s.curHP,
      subHP   := 0,
      success := false }

theorem fix_is_correct (s : BattleState) : fix s = spec s := by
  unfold fix spec; rfl

/-! ### L4: Relational Properties (Safety) -/

/-- A Pokemon is 'Fainted' if its HP is 0. -/
def isFainted (hp : BitVec 16) : Prop := hp = 0

/-- The fix guarantees that a successful Substitute never leaves the user fainted. -/
theorem fix_prevents_fainting (s : BattleState) :
  (fix s).success → ¬isFainted (fix s).userHP := by
  unfold fix isFainted
  intro h
  simp_all
  intro h_zero
  have h_val := s.curHP.toNat
  have c_val := s.maxHP.toNat / 4
  have : (BitVec.ofNat 16 h_val - BitVec.ofNat 16 c_val) = 0 := h_zero
  -- If val - cost = 0 and val > cost, we have a contradiction
  omega

/-- The fix guarantees that a successful Substitute always has health. -/
theorem fix_prevents_useless_sub (s : BattleState) :
  (fix s).success → (fix s).subHP.toNat > 0 := by
  unfold fix
  intro h
  simp_all
  omega

end AutoResearch
