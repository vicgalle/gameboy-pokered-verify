import SM83
import Harness

namespace AutoResearch

/-!
# Bug: bide_desync

When an enemy Pokémon faints, `FaintEnemyPokemon` executes:

    xor a
    ld [wPlayerBideAccumulatedDamage], a    ; high byte only!

The correct handler `RemoveFaintedPlayerMon` zeros **both** bytes:

    xor a
    ld [wPlayerBideAccumulatedDamage], a
    ld [wPlayerBideAccumulatedDamage+1], a

In a link battle the two Game Boys call different handlers for the same faint
event.  Console A (running `FaintEnemyPokemon`) retains the low byte of the Bide
counter while Console B (running `RemoveFaintedPlayerMon`) clears it entirely.
Any subsequent Bide attack deals different damage on each side — the battle state
permanently diverges unless the accumulated damage was a multiple of 256.
-/

-- ============================================================
-- Memory addresses
-- ============================================================

/-- High byte of `wPlayerBideAccumulatedDamage` -/
def bideDmgHi : BitVec 16 := 0xD058

/-- Low byte of `wPlayerBideAccumulatedDamage` -/
def bideDmgLo : BitVec 16 := 0xD059

-- ============================================================
-- Core models
-- ============================================================

/-- **impl** — buggy `FaintEnemyPokemon`: clears only the high byte.
    Assembly: `xor a; ld [wPlayerBideAccumulatedDamage], a` -/
def impl (s : SM83.CPUState) : SM83.CPUState :=
  writeMem (s.setA 0) bideDmgHi 0

/-- **spec** — correct `RemoveFaintedPlayerMon`: clears both bytes.
    Assembly: `xor a; ld [wPlayerBideAccumulatedDamage], a; ld [wPlayerBideAccumulatedDamage+1], a` -/
def spec (s : SM83.CPUState) : SM83.CPUState :=
  writeMem (writeMem (s.setA 0) bideDmgHi 0) bideDmgLo 0

/-- **fixImpl** — the one-instruction patch: also clear the low byte. -/
def fixImpl (s : SM83.CPUState) : SM83.CPUState :=
  writeMem (writeMem (s.setA 0) bideDmgHi 0) bideDmgLo 0

/-- Console A: processes the enemy faint with the buggy `FaintEnemyPokemon`. -/
def consoleA (s : SM83.CPUState) : SM83.CPUState := impl s

/-- Console B: sees the same faint as a player faint, runs correct `RemoveFaintedPlayerMon`. -/
def consoleB (s : SM83.CPUState) : SM83.CPUState := spec s

-- ============================================================
-- Helper: 16-bit Bide damage model
-- ============================================================

/-- The 16-bit Bide accumulated damage counter as a natural number (hi × 256 + lo). -/
def bideCounter (s : SM83.CPUState) : Nat :=
  (readMem s bideDmgHi).toNat * 256 + (readMem s bideDmgLo).toNat

/-- Bide deals double the accumulated damage. -/
def bideDamageDealt (s : SM83.CPUState) : Nat := 2 * bideCounter s

-- ============================================================
-- L1: Concrete witness — impl ≠ spec
-- ============================================================

/-- State with 0x0037 accumulated Bide damage (high byte = 0, low byte = 0x37). -/
def s0 : SM83.CPUState := writeMem SM83.defaultState bideDmgLo 0x37

/-- After the faint: impl leaves low byte = 0x37; spec writes 0.
    The two handlers produce observably different memory. -/
theorem l1_impl_ne_spec :
    readMem (impl s0) bideDmgLo ≠ readMem (spec s0) bideDmgLo := by
  native_decide

-- ============================================================
-- L2: Universal characterization — when and why the bug fires
-- ============================================================

/-- impl always zeros the high byte (the write it does do is correct). -/
theorem l2_impl_zeros_hi :
    ∀ v : BitVec 8,
      readMem (impl (writeMem SM83.defaultState bideDmgHi v)) bideDmgHi = 0 := by
  native_decide

/-- impl never modifies the low byte — this is the bug. -/
theorem l2_impl_preserves_lo :
    ∀ v : BitVec 8,
      readMem (impl (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo = v := by
  native_decide

/-- spec zeros both bytes regardless of their prior values. -/
theorem l2_spec_zeros_both :
    ∀ hi lo : BitVec 8,
      readMem (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgHi = 0 ∧
      readMem (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgLo = 0 := by
  native_decide

/-- The two handlers disagree on the low byte iff the low byte is non-zero.
    The bug is silent precisely when accumulated damage is a multiple of 256. -/
theorem l2_desync_iff :
    ∀ v : BitVec 8,
      (readMem (impl (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo ≠
       readMem (spec (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo) ↔ v ≠ 0 := by
  native_decide

/-- Full characterization of impl's effect on both counter bytes:
    hi is zeroed, lo is preserved exactly regardless of hi's initial value. -/
theorem l2_residual_damage :
    ∀ hi lo : BitVec 8,
      readMem (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgHi = 0 ∧
      readMem (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgLo = lo := by
  native_decide

/-- The buggy clear gives the counter a modular-residue semantics:
    after impl, the 16-bit Bide counter equals the original low byte (damage mod 256). -/
theorem l2_buggy_modular_semantics :
    ∀ hi lo : BitVec 8,
      bideCounter (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) = lo.toNat := by
  native_decide

/-- impl is idempotent on the Bide counter: applying the buggy clear twice equals once. -/
theorem l2_impl_idempotent :
    ∀ hi lo : BitVec 8,
      readMem (impl (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo))) bideDmgHi =
      readMem (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgHi ∧
      readMem (impl (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo))) bideDmgLo =
      readMem (impl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgLo := by
  native_decide

/-- spec is idempotent on the Bide counter: applying the correct clear twice equals once. -/
theorem l2_spec_idempotent :
    ∀ hi lo : BitVec 8,
      readMem (spec (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo))) bideDmgHi =
      readMem (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgHi ∧
      readMem (spec (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo))) bideDmgLo =
      readMem (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgLo := by
  native_decide

/-- spec is strictly stronger than impl: for any nonzero lo,
    impl leaves lo intact while spec zeros it. -/
theorem l2_spec_strictly_stronger :
    ∀ lo : BitVec 8, lo ≠ 0 →
      readMem (impl (writeMem SM83.defaultState bideDmgLo lo)) bideDmgLo ≠ 0 ∧
      readMem (spec (writeMem SM83.defaultState bideDmgLo lo)) bideDmgLo = 0 := by
  native_decide

-- ============================================================
-- L3: Fix — zero both bytes, matching spec
-- ============================================================

/-- The patched implementation is definitionally equal to spec for all inputs. -/
theorem l3_fix_correct : ∀ s : SM83.CPUState, fixImpl s = spec s :=
  fun _ => rfl

/-- The fix correctly resets the full 16-bit Bide counter to zero. -/
theorem l3_fix_resets_counter :
    ∀ hi lo : BitVec 8,
      bideCounter (fixImpl (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) = 0 := by
  native_decide

/-- Without the fix, the buggy clear can leave a non-zero Bide counter,
    meaning future Bide damage calculations will be wrong. -/
theorem l3_impl_can_leave_nonzero :
    ∃ s : SM83.CPUState,
      readMem s bideDmgHi = 0 ∧
      bideCounter (impl s) ≠ 0 :=
  ⟨writeMem SM83.defaultState bideDmgLo 1, by native_decide, by native_decide⟩

-- ============================================================
-- L4: Link battle desynchronization — two consoles diverge
-- ============================================================

/-- For every non-zero low-byte damage value, the two consoles disagree
    on the Bide counter after the faint — the desync is not an edge case. -/
theorem l4_desync_all_nonzero :
    ∀ v : BitVec 8, v ≠ 0 →
      readMem (consoleA (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo ≠
      readMem (consoleB (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo := by
  native_decide

/-- A concrete state demonstrating the full desynchronization:
    both consoles agree the high byte is 0, but only Console B clears the low byte. -/
theorem l4_desync_exists :
    ∃ s : SM83.CPUState,
      readMem (consoleA s) bideDmgHi = 0 ∧
      readMem (consoleA s) bideDmgLo ≠ 0 ∧
      readMem (consoleB s) bideDmgHi = 0 ∧
      readMem (consoleB s) bideDmgLo = 0 := by
  refine ⟨s0, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Quantified damage desync: Console A retains lo-byte amount as Bide counter,
    Console B has zero. The divergence is exactly lo.toNat for every lo. -/
theorem l4_damage_desync_magnitude :
    ∀ lo : BitVec 8,
      bideCounter (consoleA (writeMem SM83.defaultState bideDmgLo lo)) = lo.toNat ∧
      bideCounter (consoleB (writeMem SM83.defaultState bideDmgLo lo)) = 0 := by
  native_decide

/-- Maximum desync: lo = 0xFF causes Console A to deal 510 Bide damage
    while Console B deals 0 — a difference of 510 HP. -/
theorem l4_max_damage_desync :
    bideDamageDealt (consoleA (writeMem SM83.defaultState bideDmgLo 0xFF)) = 510 ∧
    bideDamageDealt (consoleB (writeMem SM83.defaultState bideDmgLo 0xFF)) = 0 := by
  native_decide

/-- The consoles have identical Bide counters after faint iff the low byte is zero.
    This is the exact condition under which the link battle remains synchronized. -/
theorem l4_sync_iff_zero_lo :
    ∀ lo : BitVec 8,
      bideCounter (consoleA (writeMem SM83.defaultState bideDmgLo lo)) =
      bideCounter (consoleB (writeMem SM83.defaultState bideDmgLo lo)) ↔
      lo = 0 := by
  native_decide

/-- The fix applied to both consoles restores full agreement on the Bide counter. -/
theorem l4_fix_restores_sync :
    ∀ lo : BitVec 8,
      bideCounter (fixImpl (writeMem SM83.defaultState bideDmgLo lo)) =
      bideCounter (spec (writeMem SM83.defaultState bideDmgLo lo)) := by
  native_decide

end AutoResearch
