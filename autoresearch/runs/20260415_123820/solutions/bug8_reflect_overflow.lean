import SM83

namespace AutoResearch

/-!
# Bug #8: Reflect/Light Screen Overflow

## Description
In Pokémon Red/Blue, the moves Reflect and Light Screen double the user's Defense
and Special stats respectively. However, the damage calculation routine contains
a flaw in how it handles large stats.

If a stat is greater than 255, the routine divides it by 4 and keeps only the 
lower byte of the result. When a Pokemon's stat is high (>= 512), doubling it 
via Reflect/Light Screen can cause the value to reach or exceed 1024.
Since `1024 / 4 = 256`, and the low byte of 256 is `0`, the stat wraps around
to zero or a very small number, effectively reducing the Pokemon's defense.

This can lead to a game freeze if the resulting defense is 0, causing a 
division-by-zero error in the damage formula.
-/

/--
Models the stat normalization in the Gen 1 damage calculation routine.
If the stat exceeds 255, it is divided by 4 and truncated to 8 bits.
-/
def getCalcStat (stat : BitVec 16) : BitVec 8 :=
  if stat > 255 then
    -- Division by 4, then take low byte (equivalent to mod 256)
    (stat / 4).truncate 8
  else
    stat.truncate 8

/--
The buggy implementation:
Reflect doubles the raw 16-bit stat before it is passed to the 
normalization logic.
-/
def impl (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  let effStat := if hasReflect then stat * 2 else stat
  getCalcStat effStat

/--
The intended behavior (spec):
Reflect should provide a benefit. At minimum, the effective defense
should not be less than the un-boosted defense.
-/
def spec (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  let base := getCalcStat stat
  if hasReflect then
    -- Ideally, the resulting calc stat should be double the base, capped at 255.
    let doubled := base.toNat * 2
    BitVec.ofNat 8 (if doubled > 255 then 255 else doubled)
  else
    base

-------------------------------------------------------------------------------
-- L1: Bug Existence
-------------------------------------------------------------------------------

/--
Witness: A Pokémon with 512 Defense.
Without Reflect: getCalcStat(512) = 128.
With Reflect: getCalcStat(1024) = 0.
0 < 128, so Reflect reduced defense.
-/
theorem bug_exists_reduction : exists (s : BitVec 16), impl s true < impl s false := by
  exists 512
  native_decide

/--
Witness: A Pokémon with 512 Defense results in a 0 calculation stat,
leading to a division-by-zero freeze in the damage formula.
-/
theorem bug_exists_freeze : exists (s : BitVec 16), s > 0 /\ impl s true = 0 := by
  exists 512
  native_decide

-------------------------------------------------------------------------------
-- L2: Characterization
-------------------------------------------------------------------------------

/--
The bug (reduction in effective stat) triggers when the doubled stat 
crosses the 1024 boundary. For stats in the range [512, 1021], 
applying Reflect strictly decreases the resulting calculation stat.
-/
theorem reflect_is_harmful_range : forall (s : BitVec 16),
  (s >= 512 && s <= 1021) -> impl s true < impl s false := by
  intro s h
  revert s h
  native_decide

-------------------------------------------------------------------------------
-- L3: Fix Correctness
-------------------------------------------------------------------------------

/--
A potential fix: Cap the doubled stat at 1023 before normalization.
This ensures (1023 / 4) = 255, which is the maximum possible byte value,
preventing the wrap-around to 0.
-/
def fix (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  let effStat := if hasReflect then stat * 2 else stat
  -- Cap to prevent wrap-around at 1024
  let cappedStat := if effStat >= 1024 then BitVec.ofNat 16 1023 else effStat
  getCalcStat cappedStat

/--
The fix ensures that Reflect never decreases the effective defense 
stat for any stat up to the practical limit (1023).
-/
theorem fix_is_monotonic (s : BitVec 16) : 
  s <= 1023 -> fix s true >= fix s false := by
  intro h
  revert s h
  native_decide

/--
The fix also prevents the division-by-zero freeze for all valid stats.
-/
theorem fix_prevents_freeze (s : BitVec 16) :
  (s > 0 && s <= 1023) -> fix s true > 0 := by
  intro h
  revert s h
  native_decide

end AutoResearch
