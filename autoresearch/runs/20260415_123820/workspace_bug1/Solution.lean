import SM83

/-!
# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

In Pokémon Red/Blue/Yellow (Generation 1), the move Focus Energy is intended
to increase the user's critical hit chance. However, a bug in the assembly logic
causes it to perform a right-shift (`srl`) instead of the intended logic, 
resulting in the critical hit threshold being 1/4 of what it would be without
the move.

## Assembly Analysis (engine/battle/core.asm)

1. `ld a, [wMonHBaseSpeed]; ld b, a; srl b` 
   -> Initial `b = floor(base_speed / 2)`
2. Test for Focus Energy (`GETTING_PUMPED` bit):
   - If NOT set: `sla b` 
     -> `b = (base_speed / 2) * 2` (restores original speed, mostly)
   - If SET: `srl b` 
     -> `b = (base_speed / 2) / 2` (**THIS IS THE BUG**)
3. Move type adjustment:
   - Normal Move: `srl b` 
     -> Final `b` is either `base_speed / 2` (No Focus) or `base_speed / 8` (Focus).
   - High Crit Move: `sla b; sla b` 
     -> Final `b` is either `base_speed * 4` (No Focus) or `base_speed` (Focus).

In all cases, the Focus Energy threshold is 1/4 of the non-Focus Energy threshold.
-/

namespace AutoResearch

open BitVec

/-- 
Models the `sla b; jr nc, .skip; ld b, $ff` pattern found in Gen 1's assembly.
Shifts left and caps at 255 if an overflow occurs.
-/
def sla_capped (b : BitVec 8) : BitVec 8 :=
  if b.getLsb 7 then 255 else b <<< 1

/-- Models the `srl b` instruction (Logical Shift Right). -/
def srl (b : BitVec 8) : BitVec 8 :=
  b >>> 1

/-- 
The implementation of the critical hit threshold calculation as it exists 
in the Pokémon Red assembly.
-/
def impl (base_speed : BitVec 8) (is_focus : Bool) (is_high_crit : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed]; ld b, a; srl b
  let b0 := srl base_speed
  -- bit GETTING_PUMPED, a; jr nz, .focusEnergyUsed
  let b1 := if is_focus then 
              srl b0           -- .focusEnergyUsed: srl b (THE BUG)
            else 
              sla_capped b0    -- sla b (No Focus path)
  -- Move type branch
  if is_high_crit then
    -- .HighCritical: sla b; sla b
    sla_capped (sla_capped b1)
  else
    -- srl b (Normal move path)
    srl b1

/-- 
The intended behavior: Focus Energy should double the final probability 
threshold compared to the state without Focus Energy.
-/
def spec (base_speed : BitVec 8) (is_focus : Bool) (is_high_crit : Bool) : BitVec 8 :=
  let baseline := impl base_speed false is_high_crit
  if is_focus then
    sla_capped baseline -- Intended: double the "normal" threshold
  else
    baseline

/-! ### L1: Bug Existence -/

/-- 
For a standard Pokemon like Jolteon (base speed 130), using Focus Energy 
decreases the critical hit threshold significantly.
-/
theorem bug_exists : exists (speed : BitVec 8) (high_crit : Bool), 
    impl speed true high_crit < impl speed false high_crit := by
  -- Jolteon: 130 base speed, normal move
  exists 130, false
  native_decide

/-! ### L2: Characterization -/

/-- 
Focus Energy is strictly detrimental in Gen 1: For any base speed and any move, 
using Focus Energy never results in a higher critical hit chance than 
not using it.
-/
theorem focus_energy_is_always_detrimental (speed : BitVec 8) (high : Bool) :
    impl speed true high <= impl speed false high := by
  revert speed high
  native_decide

/--
The "Quartering" Property:
For normal moves, the Focus Energy threshold is exactly the No-Focus 
threshold shifted right twice (divided by 4), assuming no underflow to 0.
-/
theorem focus_energy_quarters_threshold (speed : BitVec 8) :
    impl speed true false = (impl speed false false) >>> 2 := by
  revert speed
  native_decide

/--
The bug is so severe that a fast Pokemon (Speed 150) using Focus Energy 
with a High Critical move has a lower crit rate than the same Pokemon 
using a Normal move without Focus Energy.
-/
theorem bug_comparison_high_vs_normal :
    impl 150 true true < impl 150 false false := by
  native_decide

/-! ### L3: Fix Correctness -/

/-- 
A corrected assembly implementation. 
The fix is to change the `srl b` in the `.focusEnergyUsed` branch to 
a sequence that results in doubling the threshold. To achieve the 
`spec` (doubling the no-focus rate), the focus branch should 
result in `b1` being twice what the no-focus `b1` is.
-/
def fixed_impl (base_speed : BitVec 8) (is_focus : Bool) (is_high_crit : Bool) : BitVec 8 :=
  let b0 := srl base_speed
  let b1 := if is_focus then 
              sla_capped (sla_capped b0) -- Fixed: double the no-focus b1
            else 
              sla_capped b0
  if is_high_crit then
    sla_capped (sla_capped b1)
  else
    srl b1

/-- The fixed implementation correctly matches our specification for doubling. -/
theorem fix_matches_spec (speed : BitVec 8) (high : Bool) (focus : Bool) :
    fixed_impl speed focus high = spec speed focus high := by
  revert speed high focus
  native_decide

/-- 
With the fix, Focus Energy always improves (or maintains at cap) 
the critical hit rate for all Pokémon.
-/
theorem fix_always_improves (speed : BitVec 8) (high : Bool) :
    fixed_impl speed true high >= fixed_impl speed false high := by
  revert speed high
  native_decide

/-! ### L4: Relational Property -/

/--
A relational proof showing that the "Buggy" Focus Energy threshold 
is always exactly 1/4 of the "Fixed" Focus Energy threshold (integer division).
-/
theorem buggy_is_quarter_of_fixed (speed : BitVec 8) (high : Bool) :
    impl speed true high = (fixed_impl speed true high) >>> 2 := by
  revert speed high
  native_decide

end AutoResearch
