import SM83

/-!
# Bug #6: Substitute HP Logic Bugs

This file formalizes two bugs in Pokemon Red's `Substitute` move:
1. **Zero-HP Substitute**: Max HP < 4 results in a cost of 0, creating a 0-HP decoy.
2. **User at 0 HP**: The routine only checks for underflow (carry), allowing 
   the user's HP to reach exactly 0, which should be impossible.
-/

namespace AutoResearch

/-- Represents the state involved in the Substitute move logic. -/
structure BattleState where
  maxHP : BitVec 16
  curHP : BitVec 16
  deriving DecidableEq, Repr

/-- The outcome of attempting to use Substitute. -/
structure SubResult where
  userHP    : BitVec 16
  subHP     : BitVec 8
  success   : Bool
  deriving DecidableEq, Repr

/-- 
  Buggy implementation from `SubstituteEffect_`.
  Follows the assembly:
  1. cost = maxHP / 4 (via two `srl; rr` shifts)
  2. success if (curHP - cost) does not underflow (Carry flag)
  3. subHP = low byte of cost
-/
def impl (s : BattleState) : SubResult :=
  let cost := s.maxHP.toNat / 4
  let cost16 := BitVec.ofNat 16 cost
  let success := s.curHP.toNat >= cost -- No carry if curHP >= cost
  if success then
    { userHP := s.curHP - cost16,
      subHP  := BitVec.ofNat 8 cost,
      success := true }
  else
    { userHP := s.curHP,
      subHP  := 0,
      success := false }

/-- 
  Intended behavior:
  1. Substitute must have at least 1 HP (maxHP >= 4).
  2. User must have at least 1 HP remaining after use (curHP > cost).
-/
def spec (s : BattleState) : SubResult :=
  let cost := s.maxHP.toNat / 4
  let cost16 := BitVec.ofNat 16 cost
  let canAfford := s.curHP.toNat > cost
  let validSub  := cost > 0
  if canAfford && validSub then
    { userHP := s.curHP - cost16,
      subHP  := BitVec.ofNat 8 cost,
      success := true }
  else
    { userHP := s.curHP,
      subHP  := 0,
      success := false }

/-! ### L1: Bug Existence (Witnesses) -/

/-- Bug 1 Witness: Max HP 2 results in a successful Substitute with 0 HP. -/
theorem bug1_zero_hp_substitute_exists : ∃ s, (impl s).success ∧ (impl s).subHP = 0 :=
  ⟨{ maxHP := 2, curHP := 10 }, by native_decide⟩

/-- Bug 2 Witness: Current HP exactly 1/4 of Max HP leaves user with 0 HP. -/
theorem bug2_user_at_zero_exists : ∃ s, (impl s).success ∧ (impl s).userHP = 0 :=
  ⟨{ maxHP := 40, curHP := 10 }, by native_decide⟩

/-! ### L2: Characterization -/

/-- The bug triggers if the user would be left at 0 HP OR if the substitute has 0 HP. -/
theorem bug_iff (s : BattleState) : 
  impl s ≠ spec s ↔ 
  ((impl s).success ∧ ((impl s).userHP = 0 ∨ (impl s).subHP = 0)) := by
  unfold impl spec
  split <;> split <;> simp_all
  · -- Both success
    intro h
    cases h
    omega
  · -- Impl success, Spec failure
    intro _
    constructor
    · exact rfl
    · omega
  · -- Impl failure, Spec success (Impossible)
    omega

/-! ### L3: Fix Correctness -/

/-- 
  A fixed implementation that checks for both zero result and zero cost.
  In SM83 assembly, this would involve `or d` for the result and checking `b` for cost.
-/
def fix (s : BattleState) : SubResult :=
  let cost := s.maxHP.toNat / 4
  let cost16 := BitVec.ofNat 16 cost
  -- Logic: Success only if cost > 0 AND curHP - cost > 0 (i.e. curHP > cost)
  let success := (cost > 0) && (s.curHP.toNat > cost)
  if success then
    { userHP := s.curHP - cost16,
      subHP  := BitVec.ofNat 8 cost,
      success := true }
  else
    { userHP := s.curHP,
      subHP  := 0,
      success := false }

/-- Prove the fix matches the intended specification. -/
theorem fix_correct (s : BattleState) : fix s = spec s := by
  unfold fix spec
  rfl

/-- Verification that the fix never leaves the user at 0 HP. -/
theorem fix_prevents_user_zero (s : BattleState) : 
  (fix s).success → (fix s).userHP > 0 := by
  unfold fix
  intro h
  simp_all
  omega

/-- Verification that the fix never creates a 0-HP substitute. -/
theorem fix_prevents_zero_sub (s : BattleState) : 
  (fix s).success → (fix s).subHP > 0 := by
  unfold fix
  intro h
  simp_all
  apply BitVec.val_gt_0
  intro hn
  simp [hn] at h

end AutoResearch
