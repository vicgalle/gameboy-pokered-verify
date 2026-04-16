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
event.  After the faint, Console A retains the low byte of the Bide counter
while Console B clears it.  Any subsequent Bide attack deals different damage
on each side — the battle state permanently diverges unless the accumulated
damage happened to be a multiple of 256.
-/

/-- High byte of `wPlayerBideAccumulatedDamage` (base address in WRAM) -/
def bideDmgHi : BitVec 16 := 0xD058

/-- Low byte of `wPlayerBideAccumulatedDamage` (base + 1) -/
def bideDmgLo : BitVec 16 := 0xD059

-- ============================================================
-- Core models
-- ============================================================

/-- **impl** — buggy `FaintEnemyPokemon`: clears only the high byte.
    Assembly:
      xor a
      ld [wPlayerBideAccumulatedDamage], a   ; ← only high byte! -/
def impl (s : SM83.CPUState) : SM83.CPUState :=
  writeMem (s.setA 0) bideDmgHi 0

/-- **spec** — correct `RemoveFaintedPlayerMon`: clears both bytes.
    Assembly:
      xor a
      ld [wPlayerBideAccumulatedDamage], a
      ld [wPlayerBideAccumulatedDamage+1], a -/
def spec (s : SM83.CPUState) : SM83.CPUState :=
  writeMem (writeMem (s.setA 0) bideDmgHi 0) bideDmgLo 0

-- ============================================================
-- L1: Concrete witness — impl ≠ spec
-- ============================================================

/-- A concrete state where Bide has accumulated 0x0037 damage.
    The high byte is zero, so impl's write is a no-op there,
    but the low byte 0x37 is left intact. -/
def s0 : SM83.CPUState :=
  writeMem SM83.defaultState bideDmgLo 0x37

/-- After the faint: impl leaves low byte = 0x37; spec writes 0.
    The two handlers produce observably different memory. -/
theorem l1_impl_ne_spec :
    readMem (impl s0) bideDmgLo ≠ readMem (spec s0) bideDmgLo := by
  native_decide

-- ============================================================
-- L2: Universal characterization — when and why the bug fires
-- ============================================================

/-- impl always zeros the high byte (the write it does do is correct) -/
theorem l2_impl_zeros_hi :
    ∀ v : BitVec 8,
      readMem (impl (writeMem SM83.defaultState bideDmgHi v)) bideDmgHi = 0 := by
  native_decide

/-- impl never modifies the low byte — this is the bug -/
theorem l2_impl_preserves_lo :
    ∀ v : BitVec 8,
      readMem (impl (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo = v := by
  native_decide

/-- spec zeros both bytes regardless of their prior values -/
theorem l2_spec_zeros_both :
    ∀ hi lo : BitVec 8,
      readMem (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgHi = 0 ∧
      readMem (spec (writeMem (writeMem SM83.defaultState bideDmgHi hi) bideDmgLo lo)) bideDmgLo = 0 := by
  native_decide

/-- The two handlers disagree on the low byte **if and only if** the low byte is non-zero.
    Equivalently: the bug is silent precisely when accumulated damage is a multiple of 256. -/
theorem l2_desync_iff :
    ∀ v : BitVec 8,
      (readMem (impl (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo ≠
       readMem (spec (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo) ↔ v ≠ 0 := by
  native_decide

-- ============================================================
-- L3: Fix — zero both bytes, matching spec
-- ============================================================

/-- The one-line patch: also write 0 to the low byte address -/
def fixImpl (s : SM83.CPUState) : SM83.CPUState :=
  writeMem (writeMem (s.setA 0) bideDmgHi 0) bideDmgLo 0

/-- The patched implementation is definitionally equal to spec for all inputs -/
theorem l3_fix_correct : ∀ s : SM83.CPUState, fixImpl s = spec s :=
  fun _ => rfl

-- ============================================================
-- L4: Link battle desynchronization — two consoles diverge
-- ============================================================

/-- Console A: processes the enemy faint with the buggy `FaintEnemyPokemon` -/
def consoleA (s : SM83.CPUState) : SM83.CPUState := impl s

/-- Console B: same faint event is seen as a player faint, runs correct handler -/
def consoleB (s : SM83.CPUState) : SM83.CPUState := spec s

/-- For **every** non-zero low-byte damage value, the two consoles will disagree
    on the Bide counter after the faint — the desync is not an edge case -/
theorem l4_desync_all_nonzero :
    ∀ v : BitVec 8, v ≠ 0 →
      readMem (consoleA (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo ≠
      readMem (consoleB (writeMem SM83.defaultState bideDmgLo v)) bideDmgLo := by
  native_decide

/-- There exists a concrete game state that fully demonstrates the desynchronization:
    · Both consoles agree the high byte is 0 (both clear it)
    · Console A still sees non-zero Bide damage (low byte preserved)
    · Console B sees zero Bide damage (low byte cleared)
    Any Bide use after this will deal different damage on each side. -/
theorem l4_desync_exists :
    ∃ s : SM83.CPUState,
      readMem (consoleA s) bideDmgHi = 0 ∧
      readMem (consoleA s) bideDmgLo ≠ 0 ∧
      readMem (consoleB s) bideDmgHi = 0 ∧
      readMem (consoleB s) bideDmgLo = 0 := by
  refine ⟨s0, ?_, ?_, ?_, ?_⟩ <;> native_decide

end AutoResearch
