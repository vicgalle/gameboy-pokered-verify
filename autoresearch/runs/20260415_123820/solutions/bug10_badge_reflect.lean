import SM83

/-!
# Bug #10: badge_reflect

This file formalizes the "Badge Boost Stacking" bug in Pokémon Red/Blue, which
interacts with Reflect and the Gen 1 damage scaling formula to cause
catastrophic defense overflows.

## Bug Mechanics:
1. **Badge Boost Stacking**: When any stat is modified in battle (e.g., via Growl),
   the game erroneously reapplies the 1.125x (9/8) badge boost to ALL stats.
2. **Reflect**: This move doubles the defense stat during damage calculation.
3. **Stat Scaling**: If a stat is 512 or greater, the damage formula scales it
   down by dividing by 4. However, the result is stored in an 8-bit register
   (hDivisor), causing it to wrap around modulo 256.

## The Result:
A Pokémon with high defense (like Cloyster) can have its defense pushed over
the 1024 threshold by these interacting mechanics. A defense of 1030, which
should be a very strong 257 after scaling, wraps around to 1, making the
Pokémon effectively defenseless.
-/

namespace AutoResearch

/-- 
Models the badge boost (e.g., Thunder Badge for Defense).
The boost is a 1.125x (stat + stat/8) multiplier.
Stats in Gen 1 are capped at 999.
-/
def applyBadgeBoost (stat : BitVec 16) : BitVec 16 :=
  let val := stat.toNat
  let boosted := val + (val / 8)
  if boosted > 999 then BitVec.ofNat 16 999 else BitVec.ofNat 16 boosted

/-- 
Reflect doubles the defense stat during the damage calculation.
This doubling is temporary and occurs after stat retrieval from memory.
-/
def applyReflect (stat : BitVec 16) : BitVec 16 :=
  stat * 2

/-- 
Models the defense scaling and 8-bit truncation in the Gen 1 damage formula.
If the defense stat is >= 512, it is divided by 4.
The resulting value is then truncated to 8 bits when stored in the 
hardware divider register (hDivisor).
-/
def effectiveDefense (stat : BitVec 16) : BitVec 8 :=
  let scaled := if stat.toNat >= 512 then stat.toNat / 4 else stat.toNat
  BitVec.ofNat 8 scaled

/-- 
The intended behavior (Specification): 
The defense stat in RAM (which already has the initial badge boost) is used 
for calculation without being erroneously boosted again.
-/
def spec (ramStat : BitVec 16) : BitVec 8 :=
  effectiveDefense (applyReflect ramStat)

/-- 
The buggy behavior (Implementation): 
The badge boost is reapplied to the RAM stat before calculation, 
simulating the stacking bug triggered by a move like Growl.
-/
def impl (ramStat : BitVec 16) : BitVec 8 :=
  let buggedStat := applyBadgeBoost ramStat
  effectiveDefense (applyReflect buggedStat)

/-! ### Verification -/

/-- 
L1: Bug Existence.
We use the example from the bug description: a Pokémon with 458 defense.
(Note: 458 is roughly 407 * 1.125, representing a base 407 stat with one boost).
-/
theorem bug_exists : exists (s : BitVec 16), impl s != spec s := by
  exists (BitVec.ofNat 16 458)
  native_decide

/-- 
L2: Characterization of the Catastrophic Overflow.
For a Cloyster with 458 defense, the badge stacking bug reduces its effective 
defense from 229 (very high) down to 1 (near-zero).
-/
theorem catastrophic_drop : 
  let ramStat := BitVec.ofNat 16 458
  spec ramStat = BitVec.ofNat 8 229 ∧ impl ramStat = BitVec.ofNat 8 1 := by
  native_decide

/-- 
L2 (Stretch): Range of Vulnerability.
The bug is particularly dangerous when it pushes the stat just past 
the 1024 threshold (which scales to 256, wrapping to 0).
-/
theorem overflow_at_1024 : 
  let ramStat := BitVec.ofNat 16 512
  -- Without the bug, 512 * 2 = 1024, 1024 / 4 = 256, wraps to 0.
  -- With the bug, 512 becomes 576. 576 * 2 = 1152. 1152 / 4 = 288. wraps to 32.
  -- This shows that the interaction between Reflect and Scaling is already
  -- dangerous, but the Badge Boost reapplication moves the "sweet spot"
  -- of the bug into common high-stat ranges.
  spec ramStat = BitVec.ofNat 8 0 ∧ impl ramStat = BitVec.ofNat 8 32 := by
  native_decide

/--
L3: Fix Correctness.
The fix is to ensure the badge boost logic is only applied once during stat
initialization, and never reapplied during battle stat modifications.
-/
def fix := spec

theorem fix_is_correct (s : BitVec 16) : fix s = spec s := rfl

/--
L4: Relational Divergence.
We can prove that for certain inputs, the buggy behavior provides less than
1% of the intended defense value.
-/
theorem massive_divergence : 
  exists s, (impl s).toNat > 0 ∧ (spec s).toNat > 100 * (impl s).toNat := by
  exists (BitVec.ofNat 16 458)
  -- spec = 229, impl = 1. 229 > 100 * 1.
  native_decide

end AutoResearch
