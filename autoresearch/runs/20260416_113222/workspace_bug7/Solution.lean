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

-- L1a: Concrete witness — 322 accumulated damage (0x0142); enemy faints
-- Buggy side keeps lo = 0x42; correct side gives (0, 0)
theorem l1_witness : impl 0x01 0x42 ≠ spec 0x01 0x42 := by native_decide

-- L1b: Worst-case low byte (0xFF)
theorem l1_witness_max_lo : impl 0x00 0xFF ≠ spec 0x00 0xFF := by native_decide

-- L1c: Even when hi = 0, a nonzero lo still causes impl ≠ spec
theorem l1_hi_zero_lo_nonzero : impl 0x00 0x01 ≠ spec 0x00 0x01 := by native_decide

-- L1d: Mid-range example — 200 damage (0x00C8)
theorem l1_witness_200_damage : impl 0x00 0xC8 ≠ spec 0x00 0xC8 := by native_decide

-- L2a: The bug triggers precisely when the low byte is non-zero
theorem l2_bug_characterization : ∀ hi lo : BitVec 8,
    impl hi lo ≠ spec hi lo ↔ lo ≠ 0 := by native_decide

-- L2b: The high byte is always correctly cleared even by the buggy code
theorem l2_hi_always_cleared : ∀ hi lo : BitVec 8,
    (impl hi lo).1 = 0 := by native_decide

-- L2c: The low byte is always left unchanged — this is the bug
theorem l2_lo_never_cleared : ∀ hi lo : BitVec 8,
    (impl hi lo).2 = lo := by native_decide

-- L2d: impl output is completely independent of the high byte input
theorem l2_impl_hi_independent : ∀ hi1 hi2 lo : BitVec 8,
    impl hi1 lo = impl hi2 lo := by native_decide

-- L2e: impl agrees with spec if and only if lo = 0
theorem l2_agree_iff_lo_zero : ∀ hi lo : BitVec 8,
    impl hi lo = spec hi lo ↔ lo = 0 := by native_decide

-- L2f: The impl output encodes exactly the lo byte (no other information)
theorem l2_impl_output_characterization : ∀ hi lo : BitVec 8,
    (impl hi lo).1 = 0 ∧ (impl hi lo).2 = lo := by native_decide

-- L2g: impl applied twice is stable (lo is preserved indefinitely)
theorem l2_impl_stable : ∀ hi lo : BitVec 8,
    impl (impl hi lo).1 (impl hi lo).2 = impl hi lo := by native_decide

-- L3a: Fixed implementation clears both bytes
def implFixed (_hi _lo : BitVec 8) : BitVec 8 × BitVec 8 :=
  (0, 0)

-- L3b: The fix matches the correct spec for all inputs
theorem l3_fix_correct : ∀ hi lo : BitVec 8,
    implFixed hi lo = spec hi lo := by native_decide

-- L3c: The fixed impl always produces (0, 0) regardless of input
theorem l3_implFixed_constant : ∀ hi lo : BitVec 8,
    implFixed hi lo = (0, 0) := by native_decide

-- L3d: The fix is idempotent
theorem l3_fix_idempotent : ∀ hi lo : BitVec 8,
    implFixed (implFixed hi lo).1 (implFixed hi lo).2 = implFixed hi lo := by native_decide

-- L3e: The fix strictly improves on impl: it clears lo when impl doesn't
theorem l3_fix_clears_lo : ∀ hi lo : BitVec 8,
    (implFixed hi lo).2 = 0 := by native_decide

-- L3f: The buggy impl is NOT equivalent to the fix for any nonzero lo
theorem l3_impl_differs_from_fix : ∀ lo : BitVec 8,
    lo ≠ 0 → ∀ hi : BitVec 8, impl hi lo ≠ implFixed hi lo := by native_decide

-- L4: Link battle desynchronization model
-- Game Boy A (enemy fainted from A's perspective): runs FaintEnemyPokemon → impl (buggy)
-- Game Boy B (player fainted from B's perspective): runs RemoveFaintedPlayerMon → spec (correct)
def gbA (hi lo : BitVec 8) : BitVec 8 × BitVec 8 := impl hi lo
def gbB (hi lo : BitVec 8) : BitVec 8 × BitVec 8 := spec hi lo

-- L4a: The two Game Boys desync whenever the low byte of accumulated damage ≠ 0
theorem l4_link_desync : ∀ hi lo : BitVec 8,
    gbA hi lo ≠ gbB hi lo ↔ lo ≠ 0 := by native_decide

-- L4b: Concrete desync — 311 accumulated damage (0x0137)
theorem l4_desync_311_damage : gbA 0x01 0x37 ≠ gbB 0x01 0x37 := by native_decide

-- L4c: Sync occurs if and only if the low byte is zero (damage divisible by 256)
theorem l4_sync_iff_lo_zero : ∀ hi lo : BitVec 8,
    gbA hi lo = gbB hi lo ↔ lo = 0 := by native_decide

-- L4d: The fixed implementation eliminates the desync entirely
theorem l4_fix_eliminates_desync : ∀ hi lo : BitVec 8,
    implFixed hi lo = gbB hi lo := by native_decide

-- L4e: The desync happens for every nonzero lo, regardless of hi
theorem l4_desync_all_hi : ∀ lo : BitVec 8,
    lo ≠ 0 → ∀ hi : BitVec 8, gbA hi lo ≠ gbB hi lo := by native_decide

-- L4f: High byte information is lost entirely on both consoles
theorem l4_hi_info_always_lost : ∀ hi lo : BitVec 8,
    (gbA hi lo).1 = 0 ∧ (gbB hi lo).1 = 0 := by native_decide

-- Model Bide damage: the move deals double the stored accumulated counter
def bide_damage (state : BitVec 8 × BitVec 8) : Nat :=
  2 * (state.1.toNat * 256 + state.2.toNat)

-- L4g: GBA deals 2*lo Bide damage after the faint; GBB correctly deals 0
theorem l4_bide_damage_split : ∀ hi lo : BitVec 8,
    bide_damage (gbA hi lo) = 2 * lo.toNat ∧
    bide_damage (gbB hi lo) = 0 := by native_decide

-- L4h: The Bide damage discrepancy between consoles equals 2 * lo
theorem l4_damage_discrepancy : ∀ hi lo : BitVec 8,
    bide_damage (gbA hi lo) - bide_damage (gbB hi lo) = 2 * lo.toNat := by native_decide

-- L4i: Maximum possible Bide damage discrepancy is 510 (lo = 0xFF → 2*255 = 510)
theorem l4_max_discrepancy : ∀ hi lo : BitVec 8,
    bide_damage (gbA hi lo) ≤ 510 := by native_decide

-- L4j: When lo = 0, both consoles agree and Bide deals 0 damage (no bug triggered)
theorem l4_no_desync_when_lo_zero : ∀ hi : BitVec 8,
    gbA hi 0 = gbB hi 0 ∧ bide_damage (gbA hi 0) = 0 := by native_decide

-- L4k: GBB always deals 0 Bide damage after a faint (both bytes cleared)
theorem l4_gbB_always_zero_damage : ∀ hi lo : BitVec 8,
    bide_damage (gbB hi lo) = 0 := by native_decide

-- L4l: The fix matches GBB's Bide damage for all inputs
theorem l4_fix_matches_gbB_damage : ∀ hi lo : BitVec 8,
    bide_damage (implFixed hi lo) = bide_damage (gbB hi lo) := by native_decide

-- L4m: Desync magnitude is a pure function of the low byte alone (hi is irrelevant)
theorem l4_discrepancy_depends_only_on_lo : ∀ hi1 hi2 lo : BitVec 8,
    bide_damage (gbA hi1 lo) = bide_damage (gbA hi2 lo) := by native_decide

end AutoResearch
