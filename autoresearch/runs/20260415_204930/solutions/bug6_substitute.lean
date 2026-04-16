import SM83
import Harness

namespace AutoResearch

/-!
# Pokemon Red: Substitute Move — Dual HP Bug

Two bugs in `SubstituteEffect_` (`engine/battle/move_effects/substitute.asm`):

**Bug 1 (Zero-HP Substitute)**: When `maxHP ≤ 3`, integer division by 4 gives
cost = 0. The routine creates a free Substitute with 0 HP (breaks on first hit)
and charges the user nothing.

**Bug 2 (User at 0 HP)**: The `jr c, .notEnoughHP` branch fires only on carry,
equivalent to `currentHP < cost` (strict). When `currentHP = cost` exactly,
there is no carry, so the Substitute is created and the user survives at exactly
0 HP — an impossible game state.
-/

/-- HP cost to create a Substitute: one quarter of max HP.
    Assembly: two `SRL A; RR B` pairs on the 16-bit maxHP value.
    Simplified here to 8-bit for decidable verification. -/
def costOf (maxHP : BitVec 8) : BitVec 8 := maxHP >>> 2

/-- **Buggy implementation** (mirrors original assembly).
    The `jr c` guard is equivalent to `currentHP < cost` (unsigned carry),
    which admits both a zero-cost substitute (Bug 1) and a zero-HP user (Bug 2). -/
def impl (maxHP : BitVec 8) (currentHP : BitVec 8) : Option (BitVec 8 × BitVec 8) :=
  let cost := costOf maxHP
  if currentHP < cost then none          -- carry branch: not enough HP
  else some (currentHP - cost, cost)     -- (newUserHP, substituteHP)

/-- **Correct specification**: Substitute is valid only when
    the cost is strictly positive *and* the user retains strictly positive HP. -/
def spec (maxHP : BitVec 8) (currentHP : BitVec 8) : Option (BitVec 8 × BitVec 8) :=
  let cost := costOf maxHP
  if cost = 0 then none                  -- Bug 1 fix: reject zero-cost substitute
  else if currentHP ≤ cost then none     -- Bug 2 fix: reject when user hits 0 HP
  else some (currentHP - cost, cost)

-- ============================================================
-- L1: Concrete witnesses for each bug
-- ============================================================

/-- **Bug 1 witness**: maxHP = 3 → cost = 3 >>> 2 = 0.
    `impl` creates a free Substitute with 0 HP; `spec` rejects. -/
theorem L1_bug1_zero_cost_substitute :
    impl 3 1 = some (1, 0) ∧ spec 3 1 = none := by native_decide

/-- **Bug 2 witness**: maxHP = 8, currentHP = 2 = maxHP / 4.
    `impl` creates Substitute and leaves user at 0 HP; `spec` rejects. -/
theorem L1_bug2_user_survives_at_zero_hp :
    impl 8 2 = some (0, 2) ∧ spec 8 2 = none := by native_decide

-- ============================================================
-- L2: Universal characterization of when each bug fires
-- ============================================================

/-- The implementations diverge on (maxHP, currentHP) if and only if:
    - `costOf maxHP = 0`          (Bug 1: maxHP ≤ 3), **or**
    - `currentHP = costOf maxHP`  (Bug 2: user reaches exactly 0 HP). -/
theorem L2_diverge_iff (maxHP currentHP : BitVec 8) :
    impl maxHP currentHP ≠ spec maxHP currentHP ↔
    costOf maxHP = 0 ∨ currentHP = costOf maxHP := by
  native_decide

/-- Bug 1 range: zero cost occurs exactly when maxHP fits in 2 bits (≤ 3). -/
theorem L2_zero_cost_iff (n : BitVec 8) :
    costOf n = 0 ↔ n.toNat ≤ 3 := by native_decide

/-- Bug 2 minimal example: maxHP = 4 (smallest non-trivial), currentHP = 1.
    cost = 1, so the user hits exactly 0 HP. -/
theorem L2_bug2_minimal_trigger :
    impl 4 1 = some (0, 1) ∧ spec 4 1 = none := by native_decide

/-- Bug 2 only fires at one specific currentHP per maxHP value (when cost > 0):
    the unique input `currentHP = cost` causes the divergence. -/
theorem L2_bug2_unique_trigger (maxHP : BitVec 8) (h : costOf maxHP ≠ 0) :
    ∀ currentHP : BitVec 8,
      (impl maxHP currentHP ≠ spec maxHP currentHP ∧ costOf maxHP ≠ 0) ↔
      currentHP = costOf maxHP := by
  intro currentHP
  constructor
  · intro ⟨hdiv, _⟩
    rw [L2_diverge_iff] at hdiv
    exact hdiv.resolve_left h
  · intro heq
    exact ⟨by rw [L2_diverge_iff]; exact Or.inr heq, h⟩

-- ============================================================
-- L3: Minimal fix — verify it matches spec on all inputs
-- ============================================================

/-- **Fixed implementation**: two-line change from the original.
    Guard 1 (new): reject when cost = 0.
    Guard 2 (fixed): strict `<` → non-strict `≤` for the HP check. -/
def implFixed (maxHP : BitVec 8) (currentHP : BitVec 8) : Option (BitVec 8 × BitVec 8) :=
  let cost := costOf maxHP
  if cost = 0 then none                  -- new check: no zero-HP substitute
  else if currentHP ≤ cost then none     -- corrected: ≤ instead of <
  else some (currentHP - cost, cost)

/-- The fix is complete and sound: `implFixed` agrees with `spec` on every input. -/
theorem L3_fix_sound : ∀ maxHP currentHP : BitVec 8,
    implFixed maxHP currentHP = spec maxHP currentHP := by native_decide

-- ============================================================
-- L4: Relational — spec maintains HP-positivity; impl breaks it
-- ============================================================

/-- **Spec invariant** (holds universally): whenever Substitute succeeds,
    both the user's remaining HP and the substitute's HP are strictly positive. -/
theorem L4_spec_preserves_positive_hp :
    ∀ maxHP currentHP newHP subHP : BitVec 8,
    spec maxHP currentHP = some (newHP, subHP) →
    newHP ≠ 0 ∧ subHP ≠ 0 := by native_decide

/-- **Bug 2 reachable**: `impl` can produce a state with user HP = 0,
    which `spec` can never produce — the invariant is broken. -/
theorem L4_impl_zero_user_hp_reachable :
    ∃ maxHP currentHP newHP subHP : BitVec 8,
    impl maxHP currentHP = some (newHP, subHP) ∧ newHP = 0 ∧
    spec maxHP currentHP = none := by
  exact ⟨8, 2, 0, 2, by native_decide, rfl, by native_decide⟩

/-- **Bug 1 reachable**: `impl` can produce a substitute with 0 HP,
    which `spec` can never produce — the invariant is broken. -/
theorem L4_impl_zero_sub_hp_reachable :
    ∃ maxHP currentHP newHP subHP : BitVec 8,
    impl maxHP currentHP = some (newHP, subHP) ∧ subHP = 0 ∧
    spec maxHP currentHP = none := by
  exact ⟨3, 1, 1, 0, by native_decide, rfl, by native_decide⟩

/-- **Divergence count**: exactly 128 input pairs trigger Bug 1
    (any of the 4 low-maxHP values × 256 possible currentHP values,
    minus the 4 pairs also counted by Bug 2... but Bug 2 cost=0 subsumes them).
    Precisely: 4 × 256 + 252 × 1 pairs diverge in total. -/
theorem L4_divergence_count :
    (Finset.univ.filter (fun p : BitVec 8 × BitVec 8 =>
      impl p.1 p.2 ≠ spec p.1 p.2)).card = 1276 := by native_decide

end AutoResearch
