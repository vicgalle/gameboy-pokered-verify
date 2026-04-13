/-
  PokeredBugs/Proofs/OneIn256.lean — Formal verification of the 1/256 miss bugs.

  ## The Bugs
  Two routines in pokered use `cp b; jr/ret nc` to compare a random byte against
  a threshold. The SM83 `cp` instruction sets carry when a < b, so `jr nc` jumps
  when a >= b. This gives a `>=` comparison where `>` (strictly greater) is needed,
  causing the boundary value random == threshold to be a "fail" instead of a "pass".

  ### Bug #2: Accuracy Miss (MoveHitTest, core.asm lines 5321-5326)
    call BattleRandom    ; a = random 0..255
    cp b                 ; compare random to accuracy
    jr nc, .moveMissed   ; miss if random >= accuracy  (BUG: should be >)

  A move hits when random < accuracy. For accuracy=255, this gives 255/256 hit
  chance — even "100% accuracy" moves can miss.

  ### Bug #3: Critical Hit Miss (CriticalHitTest, core.asm lines 4534-4539)
    call BattleRandom
    rlc a; rlc a; rlc a  ; rotate (redistribute bits, still uniform 0..255)
    cp b                  ; compare to crit rate
    ret nc                ; no crit if random >= critRate  (BUG: should be >)

  Same pattern: crit occurs when random < critRate. Max crit rate still fails 1/256.

  ## Evidence of Developer Intent
  The `percent` macro (macros/data.asm) reveals what the developers intended:
      DEF percent EQUS "* $ff / 100"
  So `100 percent = 255`. The denominator is 255, not 256 — the developers thought
  "255 is the max byte, so 255 = 100%." This mental model only works with `<=`:
  threshold 255 gives 256 passing values out of 256 = 100%. The strict `<` breaks it.

  ## What We Prove
  Both bugs share the same arithmetic structure, so we prove it generically:
  1. The bug exists (witness: random = threshold = 255)
  2. Exact characterization: the bug triggers iff random == threshold
  3. The bug affects every threshold value (not just 255)
  4. The probability impact is always exactly 1/256
  5. The fix (using ≤ instead of <) is correct

  Note: for crit rate the evidence of intent is weaker — thresholds come from base
  speed, not the percent macro — but the arithmetic bug is identical.
-/
import SM83

namespace PokeredBugs

/-! ### Generic Model: The cp/jr nc Pattern -/

/-- The buggy comparison: "pass" when random < threshold.
    Models `cp b; jr nc, .fail` — fails when random >= threshold. -/
def checkActual (random threshold : BitVec 8) : Bool :=
  random.toNat < threshold.toNat

/-- The intended comparison: "pass" when random ≤ threshold.
    This ensures threshold=255 gives 256/256 (100%) pass rate. -/
def checkSpec (random threshold : BitVec 8) : Bool :=
  decide (random.toNat ≤ threshold.toNat)

/-- The fixed comparison. -/
def checkFixed (random threshold : BitVec 8) : Bool :=
  decide (random.toNat ≤ threshold.toNat)

/-! ### Concrete Instantiations -/

/-- Accuracy check: does the move hit? -/
def moveHitsActual (random accuracy : BitVec 8) : Bool := checkActual random accuracy
def moveHitsSpec (random accuracy : BitVec 8) : Bool := checkSpec random accuracy

/-- Critical hit check: does the crit happen? -/
def critHitsActual (random critRate : BitVec 8) : Bool := checkActual random critRate
def critHitsSpec (random critRate : BitVec 8) : Bool := checkSpec random critRate

/-! ### Proof 1: The Bug Exists -/

/-- A 100% accuracy move (accuracy=255) can miss. -/
theorem accuracy_bug_exists :
    ∃ random : BitVec 8,
      moveHitsActual random 255 = false ∧ moveHitsSpec random 255 = true := by
  exact ⟨255, by native_decide, by native_decide⟩

/-- Maximum crit rate (255) can fail to crit. -/
theorem crit_bug_exists :
    ∃ random : BitVec 8,
      critHitsActual random 255 = false ∧ critHitsSpec random 255 = true := by
  exact ⟨255, by native_decide, by native_decide⟩

/-! ### Proof 2: Exact Characterization -/

/-- The bug triggers if and only if random == threshold.
    This is the ONLY case where actual and spec disagree. -/
theorem bug_iff_equal (random threshold : BitVec 8) :
    (checkActual random threshold ≠ checkSpec random threshold) ↔
    random = threshold := by
  have := (by native_decide :
    ∀ r t : BitVec 8,
      (checkActual r t ≠ checkSpec r t) ↔ (r = t))
  exact this random threshold

/-! ### Proof 3: Affects Every Threshold -/

/-- For EVERY threshold value (not just 255), there exists a random value
    that triggers the bug — namely, random = threshold itself. -/
theorem bug_at_every_threshold (threshold : BitVec 8) :
    checkActual threshold threshold ≠ checkSpec threshold threshold := by
  have := (by native_decide :
    ∀ t : BitVec 8, checkActual t t ≠ checkSpec t t)
  exact this threshold

/-- But that's the ONLY value that triggers it — for random ≠ threshold,
    the actual and spec agree. -/
theorem no_bug_when_unequal (random threshold : BitVec 8)
    (h : random ≠ threshold) :
    checkActual random threshold = checkSpec random threshold := by
  have := (by native_decide :
    ∀ r t : BitVec 8, r ≠ t →
      checkActual r t = checkSpec r t)
  exact this random threshold h

/-! ### Proof 4: Probability Impact -/

/-- The actual check passes for exactly `threshold` out of 256 random values:
    random ∈ {0, 1, ..., threshold-1}. -/
theorem actual_hits_lt_threshold (random threshold : BitVec 8) :
    checkActual random threshold = true ↔ random.toNat < threshold.toNat := by
  simp [checkActual]

/-- The spec check passes for exactly `threshold + 1` out of 256 random values:
    random ∈ {0, 1, ..., threshold}. -/
theorem spec_hits_le_threshold (random threshold : BitVec 8) :
    checkSpec random threshold = true ↔ random.toNat ≤ threshold.toNat := by
  simp [checkSpec]

/-- The probability difference is always exactly 1/256: the spec accepts one
    more value (random == threshold) than the actual check. -/
theorem exactly_one_extra_hit (threshold : BitVec 8) :
    checkSpec threshold threshold = true ∧
    checkActual threshold threshold = false := by
  have := (by native_decide :
    ∀ t : BitVec 8, checkSpec t t = true ∧ checkActual t t = false)
  exact this threshold

/-! ### Proof 5: Fix Correctness -/

/-- The fix matches the spec for all inputs. -/
theorem fix_correct (random threshold : BitVec 8) :
    checkFixed random threshold = checkSpec random threshold := by
  rfl

/-! ### Interesting Consequence -/

/-- The actual check with threshold=0 NEVER passes — every move with
    accuracy=0 always misses, as expected. -/
theorem zero_threshold_never_passes (random : BitVec 8) :
    checkActual random 0 = false := by
  have := (by native_decide : ∀ r : BitVec 8, checkActual r 0 = false)
  exact this random

/-- The spec check with threshold=255 ALWAYS passes — this is the fix for
    "100% accuracy should never miss". -/
theorem max_threshold_always_passes (random : BitVec 8) :
    checkSpec random 255 = true := by
  have := (by native_decide : ∀ r : BitVec 8, checkSpec r 255 = true)
  exact this random

/-! ### CPU-Level Version -/

/-- Model the buggy accuracy check at the SM83 opcode level.
    cp b; jr nc, .miss — miss when a >= b (no carry). -/
def accuracyCheckSM83 (s : SM83.CPUState) : Bool :=
  let s' := SM83.execCp s s.b  -- cp b: sets flags based on a - b
  !s'.cFlag                     -- jr nc: taken when carry not set (a >= b)

/-- The buggy SM83 check says "miss" iff random >= accuracy. -/
theorem sm83_accuracy_matches_model :
    ∀ random accuracy : BitVec 8,
      let s := (SM83.defaultState.setA random).setB accuracy
      accuracyCheckSM83 s = !checkActual random accuracy := by
  native_decide

end PokeredBugs
