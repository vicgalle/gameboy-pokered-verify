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

-- L2a: Enemy always accepts rand=0 when level ≥ 1 (the core bug)
theorem l2_enemy_accepts_zero : ∀ level : BitVec 8,
    level.toNat ≥ 1 → impl 0 level = true := by native_decide

-- L2b: Player (spec) always rejects rand=0 regardless of level
theorem l2_player_rejects_zero : ∀ level : BitVec 8, spec 0 level = false := by native_decide

-- L2c: The two implementations agree on all non-zero random values
theorem l2_nonzero_agree : ∀ rand level : BitVec 8,
    rand ≠ 0 → impl rand level = spec rand level := by native_decide

-- L3: Fix -- make enemy Psywave consistent with player (also reject 0)
def implFixed (rand : BitVec 8) (level : BitVec 8) : Bool :=
  (rand != 0) && decide (rand.toNat < (psywaveMax level).toNat)

theorem l3_fix_correct : ∀ rand level : BitVec 8,
    implFixed rand level = spec rand level := by native_decide

-- L4: Link Battle Desync
-- Both Game Boys independently compute Psywave damage from a shared (synchronized) RNG.
-- P1's Game Boy (attacker view) uses [1, b): rejects 0, loops again.
-- P2's Game Boy (defender view) uses [0, b): accepts 0, stops.
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

-- L4b: Desync occurs whenever first RNG = 0 and second RNG is a valid player damage value
theorem l4_desync_when_zero_first : ∀ rand2 level : BitVec 8,
    rand2 ≠ 0 → rand2.toNat < (psywaveMax level).toNat →
    p1_damage 0 rand2 level ≠ p2_damage 0 rand2 level := by native_decide

end AutoResearch
