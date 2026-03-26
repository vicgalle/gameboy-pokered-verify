/-
  SM83/RNG.lean — Random Number Generator models for the Game Boy.

  The Game Boy Pokémon Red uses three RNG mechanisms:
  1. Random_ : hardware DIV register mixed with hRandomAdd/hRandomSub (nondeterministic)
  2. BattleRandom (non-link): delegates to Random_
  3. BattleRandom (link): deterministic shared list + LCG regeneration

  This file formalizes the deterministic link battle PRNG (mechanism 3),
  proves key properties of its underlying Linear Congruential Generator,
  and provides an abstract model of the overworld RNG (mechanism 1).

  ## Assembly Reference
  The link battle PRNG (engine/battle/core.asm) uses a 10-element shared list
  (wLinkBattleRandomNumberList). When the index reaches 9 after a draw,
  elements 0–8 are regenerated via: x ← 5·x + 1 (mod 256).
  This is a Linear Congruential Generator with multiplier 5 and increment 1.
-/
import SM83.Basic

namespace SM83

/-! ### Linear Congruential Generator -/

/-- LCG step: x ↦ 5·x + 1 (mod 256).
    Matches the pokered regeneration loop (engine/battle/core.asm):
      ld c, a ; add a ; add a ; add c ; inc a
    which computes a = 4a + a + 1 = 5a + 1. -/
def lcgStep (x : BitVec 8) : BitVec 8 := 5 * x + 1

/-- Iterate the LCG step n times from a seed. -/
def lcgIter (seed : BitVec 8) : Nat → BitVec 8
  | 0 => seed
  | n + 1 => lcgStep (lcgIter seed n)

/-! ### Link Battle RNG -/

/-- The link battle RNG: a shared 10-element list with a current index.
    SERIAL_RNS_LENGTH = 10 in the pokered source. -/
structure LinkBattleRNG where
  list : Fin 10 → BitVec 8
  index : Fin 10

/-- Regenerate the link battle list: apply one LCG step to elements 0–8.
    Element 9 is unchanged. Matches the assembly loop (core.asm) which runs
    SERIAL_RNS_LENGTH - 1 = 9 iterations, each independently updating one element.

    Note: each element is stepped INDEPENDENTLY through the same LCG.
    The assembly reads [hl], computes 5·[hl]+1, writes back, then advances hl.
    So list[0] ← lcgStep(list[0]), list[1] ← lcgStep(list[1]), etc. -/
def regenerateList (list : Fin 10 → BitVec 8) : Fin 10 → BitVec 8 :=
  fun i => if i.val < 9 then lcgStep (list i) else list i

/-- Draw the next random number from the link battle RNG.
    Returns the drawn value and the updated RNG state.
    When the incremented index reaches 9, the list is regenerated
    and the index resets to 0 for the next draw. -/
def battleRandomDraw (rng : LinkBattleRNG) : BitVec 8 × LinkBattleRNG :=
  let val := rng.list rng.index
  let nextIdx := rng.index.val + 1
  if h : nextIdx < 10 then
    (val, { rng with index := ⟨nextIdx, h⟩ })
  else
    let newList := regenerateList rng.list
    (val, { list := newList, index := ⟨0, by omega⟩ })

/-- Convert a LinkBattleRNG to a list representation. -/
def LinkBattleRNG.toList (rng : LinkBattleRNG) : List (BitVec 8) :=
  List.ofFn rng.list

/-! ### Overworld RNG (Abstract Model) -/

/-- The overworld RNG state: two 8-bit accumulators mixed with the hardware
    DIV register on each call to Random_.

    In non-link battles, BattleRandom delegates to Random_, which reads the
    free-running DIV register (0xFF04) — making it effectively nondeterministic
    from the software perspective. -/
structure OverworldRNG where
  hRandomAdd : BitVec 8
  hRandomSub : BitVec 8
  deriving Repr

/-- One step of the overworld RNG. Parameters div1/div2 represent two reads
    of the hardware DIV register (may differ between reads since DIV increments
    at 16384 Hz). The carry/borrow flags depend on the calling context.

    Assembly (engine/math/random.asm):
      ldh a, [rDIV] ; ld b, a ; ldh a, [hRandomAdd] ; adc b ; ldh [hRandomAdd], a
      ldh a, [rDIV] ; ld b, a ; ldh a, [hRandomSub] ; sbc b ; ldh [hRandomSub], a -/
def overworldRNGStep (rng : OverworldRNG)
    (div1 div2 : BitVec 8) (carryIn borrowIn : Bool) : OverworldRNG × BitVec 8 :=
  let c : BitVec 8 := if carryIn then 1 else 0
  let b : BitVec 8 := if borrowIn then 1 else 0
  let newAdd := rng.hRandomAdd + div1 + c
  let newSub := rng.hRandomSub - div2 - b
  ({ hRandomAdd := newAdd, hRandomSub := newSub }, newAdd)

/-! ### LCG Algebraic Properties -/

/-- The LCG has full period 256: after 256 steps, every seed returns to itself.
    This follows from the Hull-Dobell theorem: for x ↦ ax + c (mod m),
    full period iff (1) gcd(c,m)=1, (2) a≡1 mod p for all primes p|m,
    (3) if 4|m then a≡1 mod 4. Here a=5, c=1, m=256: all conditions hold.
    We verify computationally over all 256 seeds. -/
theorem lcg_period_256 (seed : BitVec 8) :
    lcgIter seed 256 = seed := by
  have := (by native_decide :
    ∀ s : BitVec 8, lcgIter s 256 = s)
  exact this seed

/-- The LCG step is injective: distinct inputs produce distinct outputs.
    Equivalently, the map x ↦ 5x + 1 is a permutation on Z/256Z. -/
theorem lcg_step_injective :
    ∀ x y : BitVec 8, lcgStep x = lcgStep y → x = y := by
  native_decide

/-- The LCG step is surjective: every byte is the image of some input. -/
theorem lcg_step_surjective :
    ∀ target : BitVec 8, ∃ x : BitVec 8, lcgStep x = target := by
  native_decide

/-- Zero is always reachable from any seed within 256 LCG steps.
    This guarantees that the Psywave desync trigger (a zero in the
    random list) is inevitable. Proved by exhaustive search over all
    256 seeds. -/
theorem lcg_zero_reachable (seed : BitVec 8) :
    ∃ n : Fin 256, lcgIter seed n.val = 0 := by
  have := (by native_decide :
    ∀ s : BitVec 8, ∃ n : Fin 256, lcgIter s n.val = 0)
  exact this seed

/-! ### Regeneration Properties -/

/-- Apply regeneration n times. -/
def regenerateN (list : Fin 10 → BitVec 8) : Nat → Fin 10 → BitVec 8
  | 0 => list
  | n + 1 => regenerateList (regenerateN list n)

/-- Each regeneration independently advances elements 0–8 by one LCG step.
    After n regenerations, element i equals lcgIter(original_i, n). -/
theorem regenerateN_is_lcgIter (list : Fin 10 → BitVec 8)
    (i : Fin 10) (hi : i.val < 9) (n : Nat) :
    regenerateN list n i = lcgIter (list i) n := by
  induction n with
  | zero => simp [regenerateN, lcgIter]
  | succ k ih =>
    unfold regenerateN regenerateList
    rw [if_pos hi, ih]; rfl

/-- Element 9 is never modified by regeneration. -/
theorem regenerateN_last_unchanged (list : Fin 10 → BitVec 8) (n : Nat) :
    regenerateN list n ⟨9, by omega⟩ = list ⟨9, by omega⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold regenerateN regenerateList
    have h : ¬((⟨9, by omega⟩ : Fin 10).val < 9) := by decide
    rw [if_neg h]
    exact ih

/-! ### Overworld RNG Properties -/

/-- The overworld RNG can produce any target byte: choosing div1 = target - hRandomAdd
    with no carry yields the target exactly. This captures the hardware DIV register's
    ability to provide any needed entropy. -/
theorem overworld_rng_reaches_any_byte (rng : OverworldRNG) (target : BitVec 8) :
    ∃ div1 : BitVec 8,
      (overworldRNGStep rng div1 0 false false).2 = target := by
  refine ⟨target - rng.hRandomAdd, ?_⟩
  simp only [overworldRNGStep]
  have : ∀ a t : BitVec 8, a + (t - a) + 0 = t := by native_decide
  exact this rng.hRandomAdd target

/-- The hRandomAdd and hRandomSub updates are independent: changing div2
    does not affect the returned random value (which comes from hRandomAdd). -/
theorem overworld_add_independent_of_sub (rng : OverworldRNG)
    (d1 d2a d2b : BitVec 8) (c b : Bool) :
    (overworldRNGStep rng d1 d2a c b).2 = (overworldRNGStep rng d1 d2b c b).2 := by
  simp [overworldRNGStep]

/-! ### #eval Validation Tests -/

-- LCG step: 0 ↦ 1, 1 ↦ 6, 255 ↦ 252 (5·255 + 1 = 1276 ≡ 252 mod 256)
#eval (lcgStep 0, lcgStep 1, lcgStep 255)

-- LCG orbit from 0: first 10 values
#eval (List.range 10).map (fun n => lcgIter 0 n)

-- Full period: lcgIter seed 256 = seed
#eval (lcgIter 0 256, lcgIter 42 256, lcgIter 255 256)

-- Seed 51 → 0: 5 × 51 + 1 = 256 ≡ 0 mod 256
#eval lcgStep 51

-- Regeneration of a list [0, 1, 2, ..., 9]
-- Elements 0–8 get 5·x+1, element 9 stays as 9
#eval
  let list : Fin 10 → BitVec 8 := fun i => ⟨i.val, by omega⟩
  let regen := regenerateList list
  List.ofFn regen

-- Three draws from a sample RNG
#eval
  let list : Fin 10 → BitVec 8 := fun i => ⟨i.val * 17 + 3, by omega⟩
  let rng : LinkBattleRNG := ⟨list, ⟨0, by omega⟩⟩
  let (v1, rng1) := battleRandomDraw rng
  let (v2, rng2) := battleRandomDraw rng1
  let (v3, _) := battleRandomDraw rng2
  (v1, v2, v3)

end SM83
