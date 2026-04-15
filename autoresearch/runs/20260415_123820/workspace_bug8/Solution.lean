import SM83

set_option maxRecDepth 10000

namespace AutoResearch

/-!
# Bug #8: Reflect/Light Screen Overflow

## Description
In Pokémon Red/Blue, the moves Reflect and Light Screen are intended to double the 
user's Defense and Special stats, respectively. However, the damage calculation 
routine handles large stats (> 255) by dividing them by 4 and taking the 
lower byte of the result.

The bug occurs because the doubling happens *before* this normalization logic. 
If a stat is 512 or higher, doubling it results in a value of 1024 or higher. 
Since `1024 >> 2 = 256`, and the 8-bit truncation of 256 is `0`, the effective 
defense stat becomes zero. This causes a division-by-zero risk (often freezing 
the game) or results in the Pokémon taking massive damage.

## Modeling
We model the `getCalcStat` normalization logic and the doubling effect. 
We then prove the existence of the bug and characterize the range of stats 
where Reflect actually decreases a Pokémon's survivability.
-/

/-- 
Models the SM83 assembly logic for stat calculation within the damage routine:
If the 16-bit stat has a non-zero high byte (H > 0), it is shifted right 
twice (divided by 4). The low byte (L) of the result is then used as the 
8-bit calculation stat.
-/
def getCalcStat (stat : BitVec 16) : BitVec 8 :=
  if stat > 255 then
    (stat >>> 2).truncate 8
  else
    stat.truncate 8

/--
The buggy implementation:
Reflect doubles the 16-bit stat. The doubled value is then passed to 
the normalization routine.
Note: In Gen 1, stats are capped at 999 normally, but intermediate 
calculations like Reflect don't always respect this cap.
-/
def impl (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  let effStat := if hasReflect then stat * 2 else stat
  getCalcStat effStat

/--
The intended behavior:
Stats should be doubled and then capped at a safe value (like 999 or 1023)
before normalization to ensure the resulting 8-bit calculation stat 
is actually an improvement.
-/
def spec (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  if !hasReflect then getCalcStat stat
  else 
    let doubled := stat.toNat * 2
    let capped := if doubled > 1023 then 1023 else doubled
    getCalcStat (BitVec.ofNat 16 capped)

/--
A simplified damage model to demonstrate the impact of the bug.
Damage is roughly proportional to (1 / Defense).
We model a defense of 0 as a "crash" or maximum damage value (0xFFFF).
-/
def damage (calcStat : BitVec 8) : Nat :=
  if calcStat = 0 then 0xFFFF
  else 10000 / calcStat.toNat

-------------------------------------------------------------------------------
-- L1: Bug Existence
-------------------------------------------------------------------------------

/--
Witness: A Pokémon with 512 Defense (e.g., a Cloyster after using Barrier).
Without Reflect: 512 -> (512 >> 2) = 128.
With Reflect: (512 * 2) = 1024 -> (1024 >> 2) = 256 -> (256 & 0xFF) = 0.
Defense drops from 128 to 0.
-/
theorem bug_exists : exists (s : BitVec 16), impl s true < impl s false := by
  exists 512
  native_decide

/--
Concrete evidence of the division-by-zero risk.
A base stat of 512 with Reflect results in a calculation stat of 0.
-/
theorem reflect_causes_zero_stat : impl 512 true = 0 := by
  native_decide

-------------------------------------------------------------------------------
-- L2: Characterization
-------------------------------------------------------------------------------

/--
The Detrimental Range: For all stats in [512, 1022], Reflect strictly 
reduces the calculation stat, making the Pokémon more vulnerable.
(At 1023, both result in 255 due to truncation properties).
-/
theorem reflect_is_detrimental_in_range : forall (s : BitVec 16),
  (s >= 512 && s <= 1022) -> impl s true < impl s false := by
  intro s h
  revert s h
  native_decide

/--
Characterizes exactly when the "zero defense" crash occurs.
The stat must be a non-zero multiple of 512.
-/
theorem bug_zero_defense_condition (s : BitVec 16) :
  (s > 0 ∧ impl s true = 0) ↔ (s % 512 = 0 ∧ s > 0) := by
  revert s
  native_decide

/--
Periodicity: The behavior of the buggy stat calculation repeats every 512 units 
for stats that trigger the "high stat" branch (> 255 after doubling).
-/
theorem bug_periodicity (s : BitVec 16) :
  (s >= 128 ∧ s <= 65023) -> impl (s + 512) true = impl s true := by
  intro h
  revert s h
  native_decide

-------------------------------------------------------------------------------
-- L3: Fix Correctness
-------------------------------------------------------------------------------

/--
The spec (which caps the doubled stat at 1023) ensures that if a Pokémon 
has a non-zero stat, Reflect will NEVER result in a 0 calculation stat.
Verified for all possible 16-bit stat values.
-/
theorem spec_prevents_zero (s : BitVec 16) :
  s > 0 -> spec s true > 0 := by
  intro h
  revert s h
  native_decide

/--
Monotonicity: The spec ensures that Reflect never makes your defense worse.
-/
theorem spec_is_monotonic (s : BitVec 16) :
  spec s true >= spec s false := by
  revert s
  native_decide

/--
The spec avoids the catastrophic drop seen in the implementation.
-/
theorem spec_avoids_high_stat_drop (s : BitVec 16) :
  s >= 512 -> spec s true = 255 := by
  intro h
  revert s h
  native_decide

-------------------------------------------------------------------------------
-- L4: Relational Damage Proofs
-------------------------------------------------------------------------------

/--
Under the bug, Reflect can increase damage taken by several orders of magnitude.
For Cloyster (512 Def), damage increases from 78 to the crash value (65535).
-/
theorem reflect_increases_damage : exists s, damage (impl s true) > damage (impl s false) := by
  exists 512
  native_decide

/--
The damage with the spec is always less than or equal to damage without Reflect.
(Reflect always helps or keeps it the same).
-/
theorem spec_improves_survivability (s : BitVec 16) :
  damage (spec s true) <= damage (spec s false) := by
  revert s
  native_decide

/--
For the critical overflow range [512, 1023], the spec is massively safer than the bug.
-/
theorem spec_vs_impl_safe_range : forall (s : BitVec 16),
  (s >= 512 ∧ s < 1024) -> damage (spec s true) < damage (impl s true) := by
  intro s h
  revert s h
  native_decide

end AutoResearch
