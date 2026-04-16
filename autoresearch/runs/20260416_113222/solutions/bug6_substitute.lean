import SM83

namespace AutoResearch

/-
  Bug #6: Substitute HP Cost Bugs in Pokemon Red

  Bug 1 (Zero-HP Substitute): The SM83 "SRL a; RR b; SRL a; RR b" sequence
  divides maxHP by 4 via integer division. For maxHP ∈ {1,2,3}, this yields 0,
  creating a substitute with 0 HP (breaks on first hit) at no cost to the user.

  Bug 2 (User at 0 HP): The code checks affordability via "jr c, .notEnoughHP"
  (branch on carry = underflow), but never checks for an exact-zero result.
  When currentHP = maxHP/4, the subtraction gives 0 with no carry flag set,
  so the substitute is created and the user is left at 0 HP — an impossible state.
-/

-- Bug 1: The substitute cost (models SRL SRL = logical right-shift by 2 = ÷4)
-- Returns 0 for maxHP ∈ {0,1,2,3} — the buggy behavior
def impl (maxHp : BitVec 8) : BitVec 8 :=
  maxHp >>> 2

-- Correct: substitute must cost at least 1 HP (can't create a 0-HP shield)
def spec (maxHp : BitVec 8) : BitVec 8 :=
  let cost := maxHp >>> 2
  if cost == (0 : BitVec 8) then (1 : BitVec 8) else cost

-- Bug 2: Buggy affordability check (only tests carry — "jr c, .notEnoughHP")
-- Returns true when user "can afford" substitute; allows 0 HP result
def implCanUse (currentHp cost : BitVec 8) : Bool :=
  currentHp.toNat >= cost.toNat   -- no underflow → allowed (but 0 HP result passes!)

-- Correct: user must retain strictly more than 0 HP after paying the cost
def specCanUse (currentHp cost : BitVec 8) : Bool :=
  currentHp.toNat > cost.toNat    -- strictly greater → at least 1 HP remains

-- Fixed Bug 1: cost is clamped to minimum 1
def implFixed (maxHp : BitVec 8) : BitVec 8 :=
  let cost := maxHp >>> 2
  if cost == (0 : BitVec 8) then (1 : BitVec 8) else cost

-- Fixed Bug 2: require strictly positive remaining HP
def implFixedCanUse (currentHp cost : BitVec 8) : Bool :=
  currentHp.toNat > cost.toNat

-- ======== L1: Concrete witnesses ========

-- Bug 1 witness: maxHP=2 → impl cost=0, but spec requires cost=1
theorem l1_witness : impl 2 ≠ spec 2 := by native_decide

-- Bug 2 witness: when currentHP equals cost, impl allows it but spec rejects it
theorem l1_witness_bug2 : implCanUse 4 4 ≠ specCanUse 4 4 := by native_decide

-- Bug 1 also triggers for maxHP=1 and maxHP=3
theorem l1_witness_maxhp1 : impl 1 = 0 ∧ spec 1 = 1 := by native_decide
theorem l1_witness_maxhp3 : impl 3 = 0 ∧ spec 3 = 1 := by native_decide

-- ======== L2: Universal characterizations ========

-- Bug 1: impl produces 0 (worthless substitute) for all small maxHP values
theorem l2_zero_cost_for_small_maxhp : ∀ x : BitVec 8,
    x.toNat ≤ 3 → (impl x).toNat = 0 := by native_decide

-- Spec always returns a positive cost (no zero-HP substitutes)
theorem l2_spec_always_positive : ∀ x : BitVec 8,
    (spec x).toNat ≥ 1 := by native_decide

-- Bug 1 characterization: impl and spec diverge exactly on maxHP < 4
theorem l2_divergence_iff : ∀ x : BitVec 8,
    impl x ≠ spec x ↔ x.toNat < 4 := by native_decide

-- Bug 2: impl always permits use when currentHP equals cost (0 HP result)
theorem l2_impl_allows_zero_hp : ∀ x : BitVec 8,
    implCanUse x x = true := by native_decide

-- Spec always rejects the exact-zero-HP scenario
theorem l2_spec_rejects_zero_hp : ∀ x : BitVec 8,
    specCanUse x x = false := by native_decide

-- Bug 2 universal: impl and specCanUse diverge whenever currentHP = cost (and cost > 0)
theorem l2_zero_hp_bug_universal : ∀ x : BitVec 8,
    x.toNat > 0 → implCanUse x x = true ∧ specCanUse x x = false := by native_decide

-- impl cost is bounded by maxHP (never exceeds it)
theorem l2_cost_bounded : ∀ x : BitVec 8,
    (impl x).toNat ≤ x.toNat := by native_decide

-- spec cost is also bounded by maxHP
theorem l2_spec_cost_bounded : ∀ x : BitVec 8,
    (spec x).toNat ≤ x.toNat + 1 := by native_decide

-- ======== L3: Fixes verified ========

-- Fix for Bug 1: implFixed matches spec for all inputs
theorem l3_fix_correct : ∀ x : BitVec 8, implFixed x = spec x := by native_decide

-- Fixed cost is always at least 1 (no zero-HP substitutes)
theorem l3_fixed_always_positive : ∀ x : BitVec 8,
    (implFixed x).toNat ≥ 1 := by native_decide

-- Fix for Bug 2: implFixedCanUse matches specCanUse for all inputs
theorem l3_fix_can_use_correct : ∀ x y : BitVec 8,
    implFixedCanUse x y = specCanUse x y := by native_decide

-- Combined fix: for all maxHP, if the fixed check passes,
-- the user retains at least 1 HP
theorem l3_fixed_user_survives : ∀ maxHp currentHp : BitVec 8,
    implFixedCanUse currentHp (implFixed maxHp) = true →
    currentHp.toNat > (implFixed maxHp).toNat := by native_decide

end AutoResearch
