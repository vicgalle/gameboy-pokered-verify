import SM83

namespace AutoResearch

-- Pokemon Red's damage calculation normalizes high stats (>255) by dividing
-- by 4 and keeping only the low byte (mod 256). Values ≥ 1024 wrap to 0.
def shrinkStat (stat : Nat) : Nat :=
  if stat > 255 then (stat / 4) % 256
  else stat

-- BUGGY: Reflect doubles raw defense first, then shrinkStat normalizes.
-- When defense ≥ 512, doubled value ≥ 1024 wraps to 0 (division-by-zero).
-- Even for defense ≥ 128, the result is 4× worse than intended.
def impl (defense : Nat) : Nat :=
  shrinkStat (defense * 2)

-- CORRECT: Normalize the stat first, then double for Reflect.
-- Intended behavior: effective defense = 2 × normalized defense.
def spec (defense : Nat) : Nat :=
  shrinkStat defense * 2

-- L1: Concrete witness — defense=512 maps to 0 under impl but 256 under spec
theorem l1_witness : impl 512 ≠ spec 512 := by native_decide

-- L1b: The catastrophic overflow: impl(512) = 0, causing division-by-zero
-- 512 × 2 = 1024; shrinkStat(1024) = (1024/4) % 256 = 256 % 256 = 0
theorem l1_impl_512_zero : impl 512 = 0 := by native_decide

-- L1c: The correct behavior at defense=512 should give 256 (128 × 2)
theorem l1_spec_512_correct : spec 512 = 256 := by native_decide

-- L2: For all byte-range defenses ≥ 128, Reflect reduces rather than doubles defense
-- impl(x) = x/2 ∈ [64,127], spec(x) = 2x ∈ [256,510]; ~4× worse in this range
theorem l2_byte_range_bug : ∀ x : BitVec 8,
    x.toNat ≥ 128 → impl x.toNat < spec x.toNat := by native_decide

-- L2b: For the overflow range [512, 1023], impl is always strictly below spec
-- impl wraps into [0, 255] while spec stays in [256, 510]
theorem l2_overflow_range_bug : ∀ x : BitVec 10,
    x.toNat ≥ 512 → impl x.toNat < spec x.toNat := by native_decide

-- L2c: For low defense (< 128), the bug is absent — impl equals spec
-- 2× defense < 256, so shrinkStat is a no-op and both code paths agree
theorem l2_no_bug_below_128 : ∀ x : BitVec 7,
    impl x.toNat = spec x.toNat := by native_decide

-- L2d: In the byte range ≥ 128, Reflect makes defense at least 4× worse
-- impl(x) * 4 ≤ spec(x) because x/2 * 4 = 2x ≤ 2x (even) or 2x-2 < 2x (odd)
theorem l2_reflect_inverts : ∀ x : BitVec 8,
    x.toNat ≥ 128 → impl x.toNat * 4 ≤ spec x.toNat := by native_decide

-- L2e: In byte range ≥ 128, buggy Reflect gives exactly half the raw defense
-- The bug doesn't just fail to double — it actively HALVES the raw defense stat!
theorem l2_reflect_halves_raw : ∀ x : BitVec 8,
    x.toNat ≥ 128 → impl x.toNat = x.toNat / 2 := by native_decide

-- L2f: Non-monotonicity: higher defense leads to worse protection under the bug
-- defense=512 gives impl=0, worse than defense=255 which gives impl=127
theorem l2_non_monotone_witness : impl 512 < impl 255 := by native_decide

-- L2g: The bug produces zero effective defense for multiple consecutive values around 512
-- Four consecutive defense values all result in zero effective defense (game freeze)
theorem l2_zero_at_multiple_points :
    impl 512 = 0 ∧ impl 513 = 0 ∧ impl 514 = 0 ∧ impl 515 = 0 := by native_decide

-- L2h: Buggy Reflect gives worse defense than having NO Reflect at all
-- For x ≥ 128: impl(x) < shrinkStat(x), so using Reflect actively harms the user
theorem l2_reflect_worse_than_none : ∀ x : BitVec 8,
    x.toNat ≥ 128 → impl x.toNat < shrinkStat x.toNat := by native_decide

-- L3: Fix — apply shrinkStat normalization before doubling for Reflect
def implFixed (defense : Nat) : Nat :=
  shrinkStat defense * 2

-- L3a: The fixed version matches spec for all defense values in BitVec 10 range
theorem l3_fix_correct : ∀ x : BitVec 10,
    implFixed x.toNat = spec x.toNat := by native_decide

-- L3b: The fixed version always produces a higher (or equal) effective defense
-- compared to the buggy version — it never makes Reflect actively harmful
theorem l3_fixed_at_least_impl : ∀ x : BitVec 8,
    implFixed x.toNat ≥ impl x.toNat := by native_decide

-- L3c: The fix eliminates the zero-defense bug: implFixed > 0 for any positive defense
-- For x ∈ [1, 1023]: shrinkStat(x) ≥ 1 (no multiple of 1024 in range), so result > 0
theorem l3_fixed_never_zero : ∀ x : BitVec 10,
    x.toNat > 0 → implFixed x.toNat > 0 := by native_decide

-- L3d: Fixed version is bounded: implFixed ≤ 510 for all BitVec 10 inputs
-- Ensures the fix never introduces its own overflow (max is 2 × 255 = 510)
theorem l3_fixed_bounded : ∀ x : BitVec 10,
    implFixed x.toNat ≤ 510 := by native_decide

-- L3e: For low defense values (< 128), fix equals direct doubling (no normalization needed)
-- Below the threshold, the correct and buggy code agree, and both equal 2 × defense
theorem l3_fixed_doubles_directly : ∀ x : BitVec 7,
    implFixed x.toNat = x.toNat * 2 := by native_decide

-- L4: Reflect direction reversal — the bug inverts the protective effect of Reflect
-- spec(x) > x (Reflect should increase defense above baseline)
-- impl(x) < x (bug decreases effective defense below even the un-Reflected baseline)
-- Using Reflect with high defense is strictly worse than not using it at all
theorem l4_reflect_direction_reversal : ∀ x : BitVec 8,
    x.toNat ≥ 128 → impl x.toNat < x.toNat ∧ spec x.toNat > x.toNat := by native_decide

end AutoResearch
