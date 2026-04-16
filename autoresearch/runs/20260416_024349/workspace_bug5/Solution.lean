import SM83

namespace AutoResearch

-- Psywave maximum damage formula: b = floor(level * 1.5) = level + (level >> 1)
def psywaveMax (level : BitVec 8) : BitVec 8 :=
  (level >>> 1) + level

-- Enemy Psywave (buggy): accepts damage in range [0, b)
-- Enemy loop: call BattleRandom; if rand >= b, loop → accepts 0
def impl (rand : BitVec 8) (level : BitVec 8) : Bool :=
  decide (rand.toNat < (psywaveMax level).toNat)

-- Player Psywave (correct): accepts damage in range [1, b)
-- Player loop: call BattleRandom; if rand = 0, loop; if rand >= b, loop → never 0
def spec (rand : BitVec 8) (level : BitVec 8) : Bool :=
  (rand != 0) && decide (rand.toNat < (psywaveMax level).toNat)

-- L1: Concrete witness -- level=10, rand=0: enemy accepts 0 damage, player doesn't
theorem l1_witness : impl 0 10 ≠ spec 0 10 := by native_decide

-- L1b: Additional concrete witnesses at different levels
theorem l1_witness_level50 : impl 0 50 ≠ spec 0 50 := by native_decide
theorem l1_witness_level100 : impl 0 100 ≠ spec 0 100 := by native_decide

-- L2a: Enemy always accepts rand=0 when psywaveMax > 0 (core bug)
-- In-game levels 1–100 all satisfy this; note level=171 causes BitVec overflow to 0
theorem l2_enemy_accepts_zero : ∀ level : BitVec 8,
    (psywaveMax level).toNat ≥ 1 → impl 0 level = true := by native_decide

-- L2b: Player (spec) always rejects rand=0 regardless of level
theorem l2_player_rejects_zero : ∀ level : BitVec 8, spec 0 level = false := by native_decide

-- L2c: The two implementations agree on all non-zero random values
theorem l2_nonzero_agree : ∀ rand level : BitVec 8,
    rand ≠ 0 → impl rand level = spec rand level := by native_decide

-- L2d: Enemy's valid damage range is a strict superset of player's valid range
theorem l2_impl_superset : ∀ rand level : BitVec 8,
    spec rand level = true → impl rand level = true := by native_decide

-- L2e: The two implementations can only disagree when rand = 0
theorem l2_diff_only_at_zero : ∀ rand level : BitVec 8,
    impl rand level ≠ spec rand level → rand = 0 := by native_decide

-- L2f: Exact characterization of when the bug triggers
-- (impl accepts, spec rejects) iff (rand=0 and psywaveMax > 0)
theorem l2_bug_characterization : ∀ rand level : BitVec 8,
    (impl rand level = true ∧ spec rand level = false) ↔
    (rand = 0 ∧ (psywaveMax level).toNat ≥ 1) := by native_decide

-- L2g: When psywaveMax = 0 (level=0, or overflow), neither player nor enemy
--       can deal any damage
theorem l2_zero_psywavemax : ∀ rand : BitVec 8,
    impl rand 0 = false ∧ spec rand 0 = false := by native_decide

-- L2h: impl always returns false for rand ≥ psywaveMax
theorem l2_over_max_rejected_impl : ∀ rand level : BitVec 8,
    (psywaveMax level).toNat ≤ rand.toNat → impl rand level = false := by native_decide

-- L2i: spec always returns false for rand ≥ psywaveMax
theorem l2_over_max_rejected_spec : ∀ rand level : BitVec 8,
    (psywaveMax level).toNat ≤ rand.toNat → spec rand level = false := by native_decide

-- L3: Fix -- make enemy Psywave consistent with player (also reject 0)
def implFixed (rand : BitVec 8) (level : BitVec 8) : Bool :=
  (rand != 0) && decide (rand.toNat < (psywaveMax level).toNat)

-- L3a: The fix matches spec for all inputs
theorem l3_fix_correct : ∀ rand level : BitVec 8,
    implFixed rand level = spec rand level := by native_decide

-- L3b: The fix preserves behavior for all non-zero random values
theorem l3_fix_preserves_nonzero : ∀ rand level : BitVec 8,
    rand ≠ 0 → implFixed rand level = impl rand level := by native_decide

-- L3c: The fix correctly rejects zero damage for all levels
theorem l3_fix_rejects_zero : ∀ level : BitVec 8, implFixed 0 level = false := by native_decide

-- L3d: The fix is strictly more restrictive than impl
theorem l3_fix_more_restrictive : ∀ rand level : BitVec 8,
    implFixed rand level = true → impl rand level = true := by native_decide

-- L4: Link Battle Desync
-- Both Game Boys independently compute Psywave damage from a shared (synchronized) RNG.
-- P1's Game Boy (attacker view) uses [1, b): rejects 0, loops again.
-- P2's Game Boy (defender view) uses [0, b): accepts 0, stops immediately.
-- When RNG yields 0: P2 stops with damage=0, P1 discards it and consumes another RNG value.
-- RNG streams diverge → all subsequent calculations differ → desynchronization.

-- Model P1's damage given two consecutive RNG values (one retry when first is rejected)
def p1_damage (rand1 rand2 : BitVec 8) (level : BitVec 8) : BitVec 8 :=
  if (rand1 != 0) && decide (rand1.toNat < (psywaveMax level).toNat) then rand1
  else if (rand2 != 0) && decide (rand2.toNat < (psywaveMax level).toNat) then rand2
  else 0

-- Model P2's damage given two consecutive RNG values
def p2_damage (rand1 rand2 : BitVec 8) (level : BitVec 8) : BitVec 8 :=
  if decide (rand1.toNat < (psywaveMax level).toNat) then rand1
  else if decide (rand2.toNat < (psywaveMax level).toNat) then rand2
  else 0

-- L4a: Concrete desync witness: level=10, rand1=0, rand2=5
-- P1 computes damage=5, P2 computes damage=0
theorem l4_witness : p1_damage 0 5 10 ≠ p2_damage 0 5 10 := by native_decide

-- L4b: Additional concrete witness at level=50
theorem l4_witness_level50 : p1_damage 0 30 50 ≠ p2_damage 0 30 50 := by native_decide

-- L4c: Desync occurs whenever first RNG = 0 and second RNG is a valid player damage value
theorem l4_desync_when_zero_first : ∀ rand2 level : BitVec 8,
    rand2 ≠ 0 → rand2.toNat < (psywaveMax level).toNat →
    p1_damage 0 rand2 level ≠ p2_damage 0 rand2 level := by native_decide

-- L4d: When first RNG = 0, P2 always settles on damage = 0 (when psywaveMax > 0)
-- P2's enemy code accepts rand=0 immediately and exits the loop
theorem l4_p2_zero_when_rand0 : ∀ rand2 level : BitVec 8,
    (psywaveMax level).toNat ≥ 1 → p2_damage 0 rand2 level = 0 := by native_decide

-- L4e: Full desync mechanics: P1 gets rand2 as damage, P2 stuck at 0
-- This shows the RNG streams are now permanently 1 value out of phase
theorem l4_rng_divergence : ∀ rand2 level : BitVec 8,
    rand2 ≠ 0 → rand2.toNat < (psywaveMax level).toNat →
    p1_damage 0 rand2 level = rand2 ∧ p2_damage 0 rand2 level = 0 := by native_decide

-- L4f: Iff characterization: desync ↔ rand2 is a valid non-zero player damage
-- Precisely identifies when the bug causes observable behavioral divergence
theorem l4_desync_iff : ∀ rand2 level : BitVec 8,
    (psywaveMax level).toNat ≥ 1 →
    (p1_damage 0 rand2 level ≠ p2_damage 0 rand2 level ↔
     rand2 ≠ 0 ∧ rand2.toNat < (psywaveMax level).toNat) := by native_decide

-- L4g: The desync damage gap: when it occurs, P1's damage exceeds P2's by exactly rand2
-- (since P2=0 and P1=rand2)
theorem l4_desync_damage_gap : ∀ rand2 level : BitVec 8,
    rand2 ≠ 0 → rand2.toNat < (psywaveMax level).toNat →
    (p1_damage 0 rand2 level).toNat = rand2.toNat + (p2_damage 0 rand2 level).toNat := by
  native_decide

end AutoResearch
