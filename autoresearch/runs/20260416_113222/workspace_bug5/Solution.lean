import SM83

namespace AutoResearch

/-- Psywave damage upper bound: floor(level * 1.5) in 8-bit wrapping arithmetic.
    Assembly: ld b, a; srl a (level >>> 1); add b (level + half); ld b, a -/
def psywaveMax (level : BitVec 8) : BitVec 8 :=
  level + (level >>> 1)

/-- Enemy Psywave damage acceptance — BUGGY (lines 4785-4788).
    `cp b; jr nc, .loop` accepts any r with r < psywaveMax(level).
    Range [0, max): zero damage IS possible. -/
def impl (level : BitVec 8) (r : BitVec 8) : Bool :=
  decide (r.toNat < (psywaveMax level).toNat)

/-- Player Psywave damage acceptance — CORRECT (lines 4664-4667).
    `and a; jr z, .loop` rejects r=0 before the upper-bound check.
    Range [1, max): zero damage is always rejected. -/
def spec (level : BitVec 8) (r : BitVec 8) : Bool :=
  (r != 0#8) && decide (r.toNat < (psywaveMax level).toNat)

-- ============================================================
-- L1: Concrete witness demonstrating the bug
-- ============================================================

-- Level 20: psywaveMax = 30; enemy accepts r=0 (0 damage), player rejects it
theorem l1_witness : impl 20#8 0#8 ≠ spec 20#8 0#8 := by native_decide

-- Another concrete witness at the minimum useful level
theorem l1_witness_level2 : impl 2#8 0#8 = true ∧ spec 2#8 0#8 = false := by native_decide

-- ============================================================
-- L2: Universal characterization of the bug
-- ============================================================

-- Player code always rejects r=0 regardless of level
theorem l2_spec_rejects_zero : ∀ level : BitVec 8, spec level 0#8 = false := by
  native_decide

-- Enemy code accepts r=0 exactly when psywaveMax > 0
theorem l2_impl_zero_iff : ∀ level : BitVec 8,
    impl level 0#8 = true ↔ 0 < (psywaveMax level).toNat := by
  native_decide

-- For r ≠ 0, both codes agree completely
theorem l2_nonzero_agree : ∀ level r : BitVec 8,
    r ≠ 0#8 → impl level r = spec level r := by
  native_decide

-- Full divergence characterization: codes disagree iff r=0 and max>0
theorem l2_diverge_iff : ∀ level r : BitVec 8,
    impl level r ≠ spec level r ↔ r = 0#8 ∧ 0 < (psywaveMax level).toNat := by
  native_decide

-- impl accepts precisely [0, psywaveMax)
theorem l2_impl_range : ∀ level r : BitVec 8,
    impl level r = true ↔ r.toNat < (psywaveMax level).toNat := by
  native_decide

-- spec accepts precisely [1, psywaveMax) — guarantees at least 1 damage
theorem l2_spec_range : ∀ level r : BitVec 8,
    spec level r = true ↔ 0 < r.toNat ∧ r.toNat < (psywaveMax level).toNat := by
  native_decide

-- spec acceptance implies impl acceptance (impl is strictly more permissive)
theorem l2_spec_implies_impl : ∀ level r : BitVec 8,
    spec level r = true → impl level r = true := by
  native_decide

-- Level 0: psywaveMax = 0, both codes reject everything (infinite loop)
theorem l2_level_zero : ∀ r : BitVec 8,
    impl 0#8 r = false ∧ spec 0#8 r = false := by native_decide

-- Level 171: 8-bit overflow makes psywaveMax = 0 (171 + 85 = 256 ≡ 0 mod 256)
theorem l2_level171_overflow : psywaveMax 171#8 = 0#8 := by native_decide

-- Level 171: overflow causes both codes to reject everything (infinite loop)
theorem l2_level171_looping : ∀ r : BitVec 8,
    impl 171#8 r = false ∧ spec 171#8 r = false := by native_decide

-- Level 170: last non-overflowing level, psywaveMax = 255
theorem l2_level170_max : psywaveMax 170#8 = 255#8 := by native_decide

-- Concrete psywaveMax values confirming the assembly formula
theorem l2_max_level50  : psywaveMax 50#8  = 75#8  := by native_decide
theorem l2_max_level100 : psywaveMax 100#8 = 150#8 := by native_decide

-- ============================================================
-- L3: Verified fix — add zero-rejection to enemy Psywave code
-- ============================================================

/-- Fixed enemy Psywave: add `and a; jr z, .loop` zero-rejection,
    matching the player code path -/
def implFixed (level : BitVec 8) (r : BitVec 8) : Bool :=
  (r != 0#8) && decide (r.toNat < (psywaveMax level).toNat)

-- Fix matches spec for all level/r combinations
theorem l3_fix_correct : ∀ level r : BitVec 8, implFixed level r = spec level r := by
  native_decide

-- Fix is minimal: only changes behavior at r=0
theorem l3_fix_minimal : ∀ level r : BitVec 8,
    r ≠ 0#8 → implFixed level r = impl level r := by
  native_decide

-- Fix always rejects r=0 (no zero damage possible after fix)
theorem l3_fix_rejects_zero : ∀ level : BitVec 8, implFixed level 0#8 = false := by
  native_decide

-- Fix acceptance range is exactly [1, psywaveMax), matching spec
theorem l3_fix_range : ∀ level r : BitVec 8,
    implFixed level r = true ↔ 0 < r.toNat ∧ r.toNat < (psywaveMax level).toNat := by
  native_decide

-- ============================================================
-- L4: Link battle desync formalization
-- Both GBs draw the same RNG value r for Psywave.
-- P1's GB (attacker): runs spec (player code path, rejects r=0)
-- P2's GB (sees P1 as enemy): runs impl (enemy code path, accepts r=0)
-- When r=0: P1 rerolls (advances RNG further), P2 records 0 damage → states diverge
-- ============================================================

-- A desyncing input pair exists
theorem l4_desync_exists : ∃ level r : BitVec 8, impl level r ≠ spec level r :=
  ⟨20#8, 0#8, by native_decide⟩

-- Level 50 desync: psywaveMax=75, enemy records 0 damage, player rerolls
theorem l4_level50_desync : impl 50#8 0#8 = true ∧ spec 50#8 0#8 = false := by
  native_decide

-- Level 100 desync: psywaveMax=150, enemy records 0 damage, player rerolls
theorem l4_level100_desync : impl 100#8 0#8 = true ∧ spec 100#8 0#8 = false := by
  native_decide

-- Every level with positive psywaveMax is desync-vulnerable via r=0
theorem l4_desync_all_valid_levels : ∀ level : BitVec 8,
    0 < (psywaveMax level).toNat → impl level 0#8 ≠ spec level 0#8 := by
  native_decide

-- Desync is one-directional: impl never rejects a value that spec accepts
theorem l4_no_reverse_desync : ∀ level r : BitVec 8,
    spec level r = true → impl level r = true := by
  native_decide

-- A level is desync-vulnerable iff its psywaveMax is positive
theorem l4_vulnerable_iff : ∀ level : BitVec 8,
    (∃ r : BitVec 8, impl level r ≠ spec level r) ↔ 0 < (psywaveMax level).toNat := by
  native_decide

-- After fix: P1's GB and P2's GB always compute identical Psywave outcomes
theorem l4_fix_no_desync : ∀ level r : BitVec 8, implFixed level r = spec level r :=
  l3_fix_correct

-- The fixed code eliminates every possible desyncing configuration
theorem l4_fix_zero_desync_configs : ∀ level r : BitVec 8,
    implFixed level r = spec level r ∧ (implFixed level r = true ↔ spec level r = true) := by
  native_decide

end AutoResearch
