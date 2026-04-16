import SM83

namespace AutoResearch

/-- Psywave damage upper bound: floor(level * 1.5)
    Assembly: ld b, a; srl a; add b; ld b, a  (8-bit wrapping arithmetic) -/
def psywaveMax (level : BitVec 8) : BitVec 8 :=
  level + (level >>> 1)

/-- Enemy's Psywave damage acceptance (BUGGY)
    Lines 4785-4788: cp b; jr nc, .loop
    Accepts r in [0, max) — zero damage is possible -/
def impl (level : BitVec 8) (r : BitVec 8) : Bool :=
  decide (r.toNat < (psywaveMax level).toNat)

/-- Player's Psywave damage acceptance (CORRECT)
    Lines 4664-4666: and a; jr z, .loop
    Accepts r in [1, max) — zero damage is always rejected -/
def spec (level : BitVec 8) (r : BitVec 8) : Bool :=
  (r != 0#8) && decide (r.toNat < (psywaveMax level).toNat)

-- L1: Concrete witness — level 20, random value 0
-- psywaveMax(20) = 20 + 10 = 30 > 0, so enemy accepts 0 but player rejects it
theorem l1_witness : impl 20#8 0#8 ≠ spec 20#8 0#8 := by native_decide

-- L2a: spec (player code) always rejects zero-damage for every level
theorem l2_spec_no_zero_damage : ∀ level : BitVec 8, spec level 0#8 = false := by
  native_decide

-- L2b: impl (enemy code) accepts zero-damage whenever psywaveMax > 0
theorem l2_impl_accepts_zero : ∀ level : BitVec 8,
    impl level 0#8 = true ↔ 0 < (psywaveMax level).toNat := by
  native_decide

-- L2c: For nonzero random values, both player and enemy code agree exactly
theorem l2_nonzero_agree : ∀ level r : BitVec 8,
    r ≠ 0#8 → impl level r = spec level r := by
  native_decide

-- L2d: Complete characterization — the codes differ iff r=0 and max>0
theorem l2_diverge_characterization : ∀ level r : BitVec 8,
    impl level r ≠ spec level r ↔ r = 0#8 ∧ 0 < (psywaveMax level).toNat := by
  native_decide

-- L3: Fix — add the zero-rejection check to the enemy code
def implFixed (level : BitVec 8) (r : BitVec 8) : Bool :=
  (r != 0#8) && decide (r.toNat < (psywaveMax level).toNat)

theorem l3_fix_correct : ∀ level r : BitVec 8, implFixed level r = spec level r := by
  native_decide

-- L4: Link battle desync formalization
-- P1's Game Boy runs "spec" (attacker = player code path)
-- P2's Game Boy runs "impl" (viewing P1's move as enemy = enemy code path)
-- Same RNG state → same r on both GBs → different damage when r=0 → desync

-- There exist inputs that cause a link battle desync
theorem l4_desync_witness : ∃ level r : BitVec 8, impl level r ≠ spec level r :=
  ⟨20#8, 0#8, by native_decide⟩

-- Specific desync scenario: level 10, r=0
-- P2's GB records 0 damage; P1's GB rejects and rerolls → battle states diverge
theorem l4_level10_desync : impl 10#8 0#8 = true ∧ spec 10#8 0#8 = false := by
  native_decide

-- For every level with a positive psywaveMax, r=0 is a desyncing random value
theorem l4_desync_universal : ∀ level : BitVec 8,
    0 < (psywaveMax level).toNat → impl level 0#8 ≠ spec level 0#8 := by
  native_decide

-- The fix eliminates all link battle desyncs for Psywave
theorem l4_fix_no_desync : ∀ level r : BitVec 8, implFixed level r = spec level r := by
  native_decide

end AutoResearch
