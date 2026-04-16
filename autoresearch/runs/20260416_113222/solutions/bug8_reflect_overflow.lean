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
-- impl(x) * 4 ≤ spec(x) because x/2 * 4 = 2x ≤ 2x = spec (even x), or 2x-2 < 2x (odd x)
theorem l2_reflect_inverts : ∀ x : BitVec 8,
    x.toNat ≥ 128 → impl x.toNat * 4 ≤ spec x.toNat := by native_decide

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

end AutoResearch
