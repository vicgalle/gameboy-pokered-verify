import SM83

namespace AutoResearch

/-
  Bug #6: Substitute HP Cost Bugs in Pokemon Red

  Bug 1 (Zero-HP Substitute): SRL a; RR b; SRL a; RR b divides maxHP by 4
  via integer division. For maxHP ∈ {1,2,3}, this yields 0 — creating a free
  substitute with 0 HP that breaks on the very first hit.

  Bug 2 (User at 0 HP): The code checks "jr c, .notEnoughHP" (branch on carry
  = underflow), but never tests for an exact-zero result. When currentHP equals
  exactly maxHP/4, subtraction gives 0 with no carry, so the substitute is
  created and the user is left with 0 HP — an impossible game state.
-/

-- Bug 1: substitute cost (models SRL; SRL = logical right shift by 2 = ÷4)
def impl (maxHp : BitVec 8) : BitVec 8 :=
  maxHp >>> 2

-- Correct: substitute cost must be at least 1 HP
def spec (maxHp : BitVec 8) : BitVec 8 :=
  let cost := maxHp >>> 2
  if cost == (0 : BitVec 8) then (1 : BitVec 8) else cost

-- Bug 2: buggy affordability check (only tests carry, not zero result)
def implCanUse (currentHp cost : BitVec 8) : Bool :=
  currentHp.toNat >= cost.toNat   -- allows currentHp = cost → 0 HP!

-- Correct: user must retain strictly positive HP after paying the cost
def specCanUse (currentHp cost : BitVec 8) : Bool :=
  currentHp.toNat > cost.toNat

-- Fixed Bug 1: clamp cost to minimum 1
def implFixed (maxHp : BitVec 8) : BitVec 8 :=
  let cost := maxHp >>> 2
  if cost == (0 : BitVec 8) then (1 : BitVec 8) else cost

-- Fixed Bug 2: require strictly positive remaining HP
def implFixedCanUse (currentHp cost : BitVec 8) : Bool :=
  currentHp.toNat > cost.toNat

-- L4 model: two linked game instances computing substitute HP cost
def game1SubstituteHP (maxHp : BitVec 8) : BitVec 8 := impl maxHp   -- buggy
def game2SubstituteHP (maxHp : BitVec 8) : BitVec 8 := spec maxHp   -- correct

-- ======== L1: Concrete witnesses ========

-- Bug 1 witness: maxHP=2 → impl cost=0, but spec requires cost=1
theorem l1_witness : impl 2 ≠ spec 2 := by native_decide

-- Bug 2 witness: when currentHP equals cost, impl allows it but spec rejects it
theorem l1_witness_bug2 : implCanUse 4 4 ≠ specCanUse 4 4 := by native_decide

-- Bug 1 also triggers for maxHP=1 and maxHP=3
theorem l1_witness_maxhp1 : impl 1 = 0 ∧ spec 1 = 1 := by native_decide
theorem l1_witness_maxhp3 : impl 3 = 0 ∧ spec 3 = 1 := by native_decide

-- ======== L2: Universal characterizations ========

-- Bug 1: impl produces 0 for all small maxHP values
theorem l2_zero_cost_for_small_maxhp : ∀ x : BitVec 8,
    x.toNat ≤ 3 → (impl x).toNat = 0 := by native_decide

-- Bug 1: exact characterization — cost is 0 iff maxHP ≤ 3
theorem l2_zero_cost_iff : ∀ x : BitVec 8,
    (impl x).toNat = 0 ↔ x.toNat ≤ 3 := by native_decide

-- spec always returns a positive cost (no zero-HP substitutes)
theorem l2_spec_always_positive : ∀ x : BitVec 8,
    (spec x).toNat ≥ 1 := by native_decide

-- impl and spec diverge exactly on maxHP < 4
theorem l2_divergence_iff : ∀ x : BitVec 8,
    impl x ≠ spec x ↔ x.toNat < 4 := by native_decide

-- For maxHP ≥ 4, impl and spec agree (bug only affects very small HP values)
theorem l2_agree_for_large : ∀ x : BitVec 8,
    x.toNat ≥ 4 → impl x = spec x := by native_decide

-- Bug 2: impl always permits substitute when currentHP equals cost (0 HP result)
theorem l2_impl_allows_zero_hp : ∀ x : BitVec 8,
    implCanUse x x = true := by native_decide

-- spec always rejects the exact-zero-HP scenario
theorem l2_spec_rejects_zero_hp : ∀ x : BitVec 8,
    specCanUse x x = false := by native_decide

-- Bug 2 universal: for any nonzero HP, impl allows 0-HP state but spec rejects it
theorem l2_zero_hp_bug_universal : ∀ x : BitVec 8,
    x.toNat > 0 → implCanUse x x = true ∧ specCanUse x x = false := by native_decide

-- impl cost is bounded by maxHP
theorem l2_cost_bounded : ∀ x : BitVec 8,
    (impl x).toNat ≤ x.toNat := by native_decide

-- spec cost is at most maxHP/4 + 1 (tight bound for clamped case)
theorem l2_spec_cost_bounded : ∀ x : BitVec 8,
    (spec x).toNat ≤ x.toNat / 4 + 1 := by native_decide

-- spec is exactly clamping impl to a minimum of 1
theorem l2_spec_is_clamp : ∀ x : BitVec 8,
    spec x = if impl x == 0 then 1 else impl x := by native_decide

-- impl gives the exact integer quarter of maxHP
theorem l2_impl_is_quarter : ∀ x : BitVec 8,
    (impl x).toNat = x.toNat / 4 := by native_decide

-- Both bugs trigger simultaneously for small HP: free 0-HP substitute allowed
theorem l2_both_bugs_small_hp : ∀ x : BitVec 8,
    0 < x.toNat → x.toNat < 4 →
    (impl x).toNat = 0 ∧ implCanUse x (impl x) = true := by native_decide

-- implCanUse and specCanUse agree when cost strictly exceeds currentHP (both reject)
theorem l2_both_reject_when_too_costly : ∀ x y : BitVec 8,
    x.toNat < y.toNat → implCanUse x y = false ∧ specCanUse x y = false := by native_decide

-- implCanUse and specCanUse agree when currentHP strictly exceeds cost (both accept)
theorem l2_both_accept_when_affordable : ∀ x y : BitVec 8,
    x.toNat > y.toNat → implCanUse x y = true ∧ specCanUse x y = true := by native_decide

-- The two checks differ exactly when currentHP = cost
theorem l2_checks_disagree_iff : ∀ x y : BitVec 8,
    implCanUse x y ≠ specCanUse x y ↔ x = y := by native_decide

-- ======== L3: Fixes verified ========

-- Fix for Bug 1 matches spec exactly for all inputs
theorem l3_fix_correct : ∀ x : BitVec 8, implFixed x = spec x := by native_decide

-- Fixed cost is always at least 1 (no zero-HP substitutes possible)
theorem l3_fixed_always_positive : ∀ x : BitVec 8,
    (implFixed x).toNat ≥ 1 := by native_decide

-- Fix for Bug 2 matches specCanUse exactly for all inputs
theorem l3_fix_can_use_correct : ∀ x y : BitVec 8,
    implFixedCanUse x y = specCanUse x y := by native_decide

-- Combined fix: when use is allowed, user retains at least 1 HP
theorem l3_fixed_user_survives : ∀ maxHp currentHp : BitVec 8,
    implFixedCanUse currentHp (implFixed maxHp) = true →
    currentHp.toNat > (implFixed maxHp).toNat := by native_decide

-- With both fixes, the 0 HP survivor state is impossible
theorem l3_no_zero_hp_state : ∀ maxHp currentHp : BitVec 8,
    implFixedCanUse currentHp (implFixed maxHp) = true →
    currentHp.toNat > 0 := by native_decide

-- Fixed substitute always has positive HP (never breaks on first hit)
theorem l3_substitute_always_viable : ∀ x : BitVec 8,
    (implFixed x).toNat > 0 := by native_decide

-- ======== L4: Link battle desync ========

-- Two linked games disagree on substitute HP for small maxHP values
theorem l4_desync_small_maxhp : ∀ x : BitVec 8,
    0 < x.toNat → x.toNat < 4 →
    game1SubstituteHP x ≠ game2SubstituteHP x := by native_decide

-- For maxHP ≥ 4, both games agree on substitute cost (no desync)
theorem l4_agree_normal_maxhp : ∀ x : BitVec 8,
    x.toNat ≥ 4 → game1SubstituteHP x = game2SubstituteHP x := by native_decide

-- Exact consequence: buggy game creates 0-HP shield, fixed game creates 1-HP shield
theorem l4_desync_consequence : ∀ x : BitVec 8,
    0 < x.toNat → x.toNat < 4 →
    (game1SubstituteHP x).toNat = 0 ∧ (game2SubstituteHP x).toNat = 1 := by native_decide

-- Desync is bidirectional: game1 < game2 for small maxHP, equal otherwise
theorem l4_game1_leq_game2 : ∀ x : BitVec 8,
    (game1SubstituteHP x).toNat ≤ (game2SubstituteHP x).toNat := by native_decide

end AutoResearch
