import SM83

namespace AutoResearch

-- The Bide accumulated damage is stored as two consecutive bytes in memory:
--   wPlayerBideAccumulatedDamage     → high byte (address N)
--   wPlayerBideAccumulatedDamage + 1 → low byte  (address N+1)
--
-- FaintEnemyPokemon (buggy) executes only:
--   xor a
--   ld [wPlayerBideAccumulatedDamage], a   ; clears HIGH byte only
-- leaving the low byte intact.
--
-- RemoveFaintedPlayerMon (correct, called by the other Game Boy in link battle)
-- clears BOTH bytes. The two Game Boys therefore end up with different
-- accumulated damage values unless lo ≡ 0 (mod 256).

-- Buggy clear: FaintEnemyPokemon only zeroes the high byte
def impl (hi lo : BitVec 8) : BitVec 8 × BitVec 8 :=
  (0, lo)

-- Correct clear: RemoveFaintedPlayerMon zeroes both bytes
def spec (hi lo : BitVec 8) : BitVec 8 × BitVec 8 :=
  (0, 0)

-- L1: Concrete witness — 322 accumulated damage (0x0142); enemy faints
-- Buggy side keeps lo = 0x42; correct side gives (0, 0)
theorem l1_witness : impl 0x01 0x42 ≠ spec 0x01 0x42 := by native_decide

-- L1b: Worst-case low byte (0xFF)
theorem l1_witness_max_lo : impl 0x00 0xFF ≠ spec 0x00 0xFF := by native_decide

-- L2: The bug triggers precisely when the low byte is non-zero
theorem l2_bug_characterization : ∀ hi lo : BitVec 8,
    impl hi lo ≠ spec hi lo ↔ lo ≠ 0 := by native_decide

-- L2b: The high byte is always correctly cleared even by the buggy code
theorem l2_hi_always_cleared : ∀ hi lo : BitVec 8,
    (impl hi lo).1 = 0 := by native_decide

-- L2c: The low byte is always left unchanged — this is the bug
theorem l2_lo_never_cleared : ∀ hi lo : BitVec 8,
    (impl hi lo).2 = lo := by native_decide

-- L3: Fixed implementation clears both bytes
def implFixed (_hi _lo : BitVec 8) : BitVec 8 × BitVec 8 :=
  (0, 0)

-- L3: The fix matches the correct spec for all inputs
theorem l3_fix_correct : ∀ hi lo : BitVec 8,
    implFixed hi lo = spec hi lo := by native_decide

-- L4: Link battle desynchronization model
-- Game Boy A (enemy fainted from A's perspective): runs FaintEnemyPokemon → impl (buggy)
-- Game Boy B (player fainted from B's perspective): runs RemoveFaintedPlayerMon → spec (correct)
def gbA (hi lo : BitVec 8) : BitVec 8 × BitVec 8 := impl hi lo
def gbB (hi lo : BitVec 8) : BitVec 8 × BitVec 8 := spec hi lo

-- L4: The two Game Boys desync whenever the low byte of accumulated damage ≠ 0
theorem l4_link_desync : ∀ hi lo : BitVec 8,
    gbA hi lo ≠ gbB hi lo ↔ lo ≠ 0 := by native_decide

-- L4b: Concrete desync example — 311 accumulated damage (0x0137)
-- GBA thinks damage remaining = 0x0037 = 55
-- GBB thinks damage remaining = 0x0000 = 0
-- Bide will deal wildly different damage on each console
theorem l4_desync_311_damage : gbA 0x01 0x37 ≠ gbB 0x01 0x37 := by native_decide

-- L4c: Sync occurs if and only if the low byte is zero (damage divisible by 256)
theorem l4_sync_iff_lo_zero : ∀ hi lo : BitVec 8,
    gbA hi lo = gbB hi lo ↔ lo = 0 := by native_decide

-- L4d: The fixed implementation eliminates the desync entirely
theorem l4_fix_eliminates_desync : ∀ hi lo : BitVec 8,
    implFixed hi lo = gbB hi lo := by native_decide

end AutoResearch
