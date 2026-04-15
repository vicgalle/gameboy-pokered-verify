import SM83

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling it

In Pokémon Red/Blue (Gen 1), the move Focus Energy is intended to increase the 
user's critical hit rate. However, a bug in the logic for `CriticalHitTest` in 
`engine/battle/core.asm` causes the rate to be divided by 4 instead.

### The Logic Breakdown:
1.  **Initialization**: The threshold `b` is set to `BaseSpeed / 2`.
2.  **Focus Energy Branch**: 
    - If Focus Energy is **OFF**: `b` is shifted left (`sla b`), effectively `b = BaseSpeed`.
    - If Focus Energy is **ON**: `b` is shifted right (`srl b`), effectively `b = BaseSpeed / 4`.
3.  **Move Type Modifier**:
    - **Normal Move**: `b` is shifted right (`srl b`).
        - Result (No FE): `BaseSpeed / 2`.
        - Result (FE): `BaseSpeed / 8`.
    - **High-Crit Move**: `b` is shifted left twice (`sla b; sla b`).
        - Result (No FE): `BaseSpeed * 4`.
        - Result (FE): `BaseSpeed`.

In all cases, using Focus Energy results in a threshold (and thus probability) 
that is 1/4 of what it would have been without the move.
-/

namespace AutoResearch

/-- 
Models the saturating left shift (sla) behavior in the SM83 assembly.
In `CriticalHitTest`, `sla b` is followed by a jump-if-no-carry; if carry 
is set, the register is capped at `0xFF` (255).
-/
def sla_sat (b : BitVec 8) : BitVec 8 :=
  if b >>> 7 == 1 then 255 else b <<< 1

/-- 
Faithful model of the buggy `CriticalHitTest` threshold calculation.
Returns the 8-bit threshold value compared against a random byte.
-/
def impl (base_speed : BitVec 8) (is_focus_energy : Bool) (is_high_crit : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed]; ld b, a; srl b
  let b0 := base_speed >>> 1
  
  -- bit GETTING_PUMPED, a; jr nz, .focusEnergyUsed
  let b1 := if is_focus_energy then
              -- .focusEnergyUsed: srl b (THE BUG: should have been a shift left)
              b0 >>> 1
            else
              -- Normal: sla b
              sla_sat b0
  
  -- .Loop check for HighCriticalMoves
  if is_high_crit then
    -- .HighCritical: sla b; sla b;
    sla_sat (sla_sat b1)
  else
    -- Normal Move: srl b
    b1 >>> 1

/-- 
Models a fixed version where Focus Energy doubles the critical hit threshold 
instead of quartering it.
-/
def fixed_spec (base_speed : BitVec 8) (is_focus_energy : Bool) (is_high_crit : Bool) : BitVec 8 :=
  let b0 := base_speed >>> 1
  let b1 := if is_focus_energy then
              -- Corrected: Double the threshold relative to the base speed
              sla_sat (sla_sat b0)
            else
              sla_sat b0
  if is_high_crit then
    sla_sat (sla_sat b1)
  else
    b1 >>> 1

---

/-- 
L1: Bug Existence.
Using Jolteon (Base Speed 130) as an example: 
Without Focus Energy, threshold is 65. With Focus Energy, threshold is 16.
-/
theorem bug_exists : ∃ (s : BitVec 8) (h : Bool), impl s true h < impl s false h := by
  -- Witness: Jolteon (130) with a normal move (false)
  exists 130, false
  native_decide

/-- 
L2: Universal Harmfulness.
For any Pokémon with a base speed of at least 4, Focus Energy strictly 
decreases the probability of a critical hit for any move.
-/
theorem bug_is_always_harmful (s : BitVec 8) (h : Bool) : 
  s >= 4 → impl s true h < impl s false h := by
  intro _
  have h_univ := (by native_decide : ∀ (s : BitVec 8) (h : Bool), s >= 4 → impl s true h < impl s false h)
  exact h_univ s h

/-- 
L3: Fix Correctness.
In the fixed implementation, Focus Energy always results in a threshold 
greater than or equal to the case where it is not used.
-/
theorem fix_is_beneficial (s : BitVec 8) (h : Bool) : 
  fixed_spec s true h >= fixed_spec s false h := by
  have h_univ := (by native_decide : ∀ (s : BitVec 8) (h : Bool), fixed_spec s true h >= fixed_spec s false h)
  exact h_univ s h

/-- 
L4: The "Quartering" Property (Normal Moves).
For standard speeds where saturation doesn't occur, the threshold with 
Focus Energy is exactly 1/4 the threshold without it.
-/
theorem focus_energy_quarters_rate_normal (s : BitVec 8) : 
  s >= 8 ∧ s < 128 → (impl s false false).toNat / 4 = (impl s true false).toNat := by
  intro _
  have h_univ := (by native_decide : ∀ (s : BitVec 8), s >= 8 ∧ s < 128 → (impl s false false).toNat / 4 = (impl s true false).toNat)
  exact h_univ s

/-- 
L4: The "Quartering" Property (High-Crit Moves).
The same 1/4 penalty applies to high-critical moves like Slash or Razor Leaf.
-/
theorem focus_energy_quarters_rate_high_crit (s : BitVec 8) : 
  s >= 8 ∧ s < 32 → (impl s false true).toNat / 4 = (impl s true true).toNat := by
  intro _
  have h_univ := (by native_decide : ∀ (s : BitVec 8), s >= 8 ∧ s < 32 → (impl s false true).toNat / 4 = (impl s true true).toNat)
  exact h_univ s

/--
L4: Monotonicity of the bug.
Shows that even as base speed increases, the penalty remains: 
Focus Energy is always worse than doing nothing.
-/
theorem bug_is_monotonically_worse (s : BitVec 8) (h : Bool) :
  impl s true h <= impl s false h := by
  have h_univ := (by native_decide : ∀ (s : BitVec 8) (h : Bool), impl s true h <= impl s false h)
  exact h_univ s h

end AutoResearch
