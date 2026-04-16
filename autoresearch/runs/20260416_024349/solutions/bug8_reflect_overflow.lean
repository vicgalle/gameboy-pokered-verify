import SM83

namespace AutoResearch

/-- The damage calculation's effective stat formula in Pokemon Red.
    When a stat exceeds 255, the game divides by 4 and takes the low byte.
    This causes the effective value to wrap around at 1024. -/
def effectiveStat (stat : Nat) : Nat :=
  if stat > 255 then (stat / 4) % 256 else stat

/-- Buggy implementation: Reflect doubles the defense stat before the damage
    calculation applies the effective stat formula. For defense ≥ 512, doubling
    causes the effective defense to overflow back to near zero. -/
def impl (defense : Nat) : Nat :=
  effectiveStat (defense * 2)

/-- Correct specification: Reflect should double the Pokemon's effective defense.
    The correct behavior computes the effective stat first, then doubles it. -/
def spec (defense : Nat) : Nat :=
  effectiveStat defense * 2

-- ============================================================
-- L1: Concrete witnesses demonstrating the bug
-- ============================================================

/-- A defense value of 512 (achievable via Barrier spam) causes a game freeze:
    Reflect makes effective defense 0, causing division-by-zero in the damage calc.
    512 * 2 = 1024, and 1024 / 4 = 256, and 256 % 256 = 0. -/
theorem l1_freeze : impl 512 = 0 := by native_decide

/-- The buggy implementation differs from the correct specification at defense = 512.
    impl 512 = 0, but spec 512 = 256. -/
theorem l1_witness : impl 512 ≠ spec 512 := by native_decide

/-- The Reflect paradox: effective defense WITH Reflect (0) is strictly less than
    WITHOUT Reflect (128) at defense = 512. Having Reflect is actively harmful! -/
theorem l1_reflect_backfires : impl 512 < effectiveStat 512 := by native_decide

-- ============================================================
-- L2: Universal characterization of the bug
-- ============================================================

/-- For ALL defense values in [512, 1023], Reflect never increases effective defense.
    The overflow makes Reflect useless-to-harmful for every high-defense Pokemon.
    Proved by enumeration over all 512 cases. -/
theorem l2_reflect_never_helps_high : ∀ d : Fin 512,
    impl (d.val + 512) ≤ effectiveStat (d.val + 512) := by native_decide

/-- For defense values 0–127, Reflect correctly doubles the effective defense stat.
    When 2 * defense ≤ 255, no byte truncation occurs and the formula is exact. -/
theorem l2_reflect_works_low : ∀ d : Fin 128, impl d.val = spec d.val := by native_decide

/-- For defense values 1–511, Reflect never causes a game freeze (effective defense > 0).
    The catastrophic zero only occurs when defense ≥ 512. -/
theorem l2_no_freeze_below_512 : ∀ d : Fin 511, impl (d.val + 1) > 0 := by native_decide

/-- Quantified bug witness: every defense value in [512, 1023] has impl strictly below
    the no-Reflect baseline for at least the canonical case d=0 (defense=512). -/
theorem l2_freeze_is_worst : impl 512 = 0 ∧ effectiveStat 512 = 128 := by native_decide

-- ============================================================
-- L3: Fixed implementation and verification
-- ============================================================

/-- Fixed implementation: compute the effective stat first, then double it for Reflect.
    This avoids the overflow by working with the already-reduced byte-sized value. -/
def implFixed (defense : Nat) : Nat :=
  effectiveStat defense * 2

/-- The fixed implementation is definitionally equal to the specification for all
    defense values — proved by reflexivity since both unfold to the same expression. -/
theorem l3_fix_correct : ∀ d : Fin 1024, implFixed d.val = spec d.val :=
  fun _ => rfl

/-- The fixed implementation always provides equal or greater protection than no Reflect
    for all valid defense values [0, 1023]. -/
theorem l3_fix_always_helps : ∀ d : Fin 1024, implFixed d.val ≥ effectiveStat d.val := by
  native_decide

/-- The fixed implementation never causes a game freeze for any positive defense value.
    implFixed (d+1) = effectiveStat(d+1) * 2 > 0 whenever effectiveStat(d+1) > 0. -/
theorem l3_fix_no_freeze : ∀ d : Fin 1023, implFixed (d.val + 1) > 0 := by native_decide

/-- The fix repairs the specific failure case: implFixed 512 = 256 (correctly doubled),
    while the buggy impl 512 = 0 (freeze). -/
theorem l3_fix_repairs_512 : implFixed 512 = 256 ∧ impl 512 = 0 := by native_decide

end AutoResearch
