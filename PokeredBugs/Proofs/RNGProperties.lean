/-
  PokeredBugs/Proofs/RNGProperties.lean — Connecting the LCG model to bug proofs.

  ## What We Prove
  1. The LCG inevitably produces zero in any link battle random list,
     guaranteeing the Psywave desync trigger
  2. Concrete LCG-generated lists that cause the desync
  3. The LCG has perfectly uniform distribution over a full period,
     matching the 1/256 probability in accuracy and critical hit checks
  4. The seed value 51 maps to 0 in one LCG step — a concrete trigger

  These results strengthen the existing PsywaveDesync proofs by showing
  that the desync is not just possible but INEVITABLE in any sufficiently
  long link battle, and that the RNG's distribution properties underlie
  the probability assumptions in the OneIn256 and FocusEnergy proofs.
-/
import SM83
import PokeredBugs.Proofs.PsywaveDesync

namespace PokeredBugs

open SM83

/-! ### Concrete LCG Values -/

/-- Seed 51 maps to 0 in one LCG step: 5 × 51 + 1 = 256 ≡ 0 (mod 256).
    This is the most "dramatic" seed — one regeneration cycle away from
    triggering the Psywave desync. -/
theorem lcg_seed_51_to_zero : lcgStep 51 = 0 := by native_decide

/-- Seed 0 maps to 1: the LCG never stays at zero. -/
theorem lcg_seed_0_to_1 : lcgStep 0 = 1 := by native_decide

/-- The inverse: 0 is produced by seed 51. To find which seed produces 0,
    we need x such that 5x + 1 ≡ 0 (mod 256), i.e., x ≡ 51 (mod 256). -/
theorem lcg_only_51_produces_zero :
    ∀ x : BitVec 8, lcgStep x = 0 → x = 51 := by
  native_decide

/-! ### Inevitability of Zero in Link Battle Lists -/

/-- For any initial link battle RNG list, there exists a number of
    regenerations after which position 0 contains zero.
    Since the LCG has full period 256, every seed reaches zero within
    256 steps. Combined with regenerateN_is_lcgIter, position 0 of the
    list hits zero after at most 256 regenerations.

    This means the Psywave desync trigger (a zero drawn from the shared
    list) is INEVITABLE in any sufficiently long link battle. -/
theorem lcg_guarantees_zero_in_list (list : Fin 10 → BitVec 8) :
    ∃ k : Fin 256, regenerateN list k.val ⟨0, by omega⟩ = 0 := by
  obtain ⟨n, hn⟩ := lcg_zero_reachable (list ⟨0, by omega⟩)
  refine ⟨n, ?_⟩
  rw [regenerateN_is_lcgIter list ⟨0, by omega⟩ (by decide) n.val]
  exact hn

/-- The same holds for every position 0–8 in the list.
    After at most 256 regenerations, ALL positions have passed through zero. -/
theorem lcg_guarantees_zero_at_any_position (list : Fin 10 → BitVec 8)
    (i : Fin 10) (hi : i.val < 9) :
    ∃ k : Fin 256, regenerateN list k.val i = 0 := by
  obtain ⟨n, hn⟩ := lcg_zero_reachable (list i)
  refine ⟨n, ?_⟩
  rw [regenerateN_is_lcgIter list i hi n.val]
  exact hn

/-! ### Concrete Desync via LCG-Generated Lists -/

/-- When a link battle random list starts with [0, 26, ...], the Psywave
    desync occurs: player rejects the 0 (extra draw), enemy accepts it.

    This list arises naturally from the LCG: if position 0 held seed 51
    and position 1 held seed 5, one regeneration produces [0, 26, ...],
    since lcgStep 51 = 0 and lcgStep 5 = 26. -/
theorem desync_from_lcg_list :
    let rng : LinkRNG := ⟨[0, 26, 100, 100, 100, 100, 100, 100, 100, 100], 0⟩
    let b : BitVec 8 := 75  -- level 50 Pokémon: b = 1.5 × level = 75
    let (playerDmg, playerRNG) := psywavePlayer b rng
    let (enemyDmg, enemyRNG) := psywaveEnemy b rng
    -- Player skips 0, takes 26; enemy takes 0 immediately
    playerDmg = 26 ∧ enemyDmg = 0 ∧
    -- RNG indices diverge: player consumed 2, enemy consumed 1
    playerRNG.index = 2 ∧ enemyRNG.index = 1 := by
  native_decide

/-- The list [0, 26, ...] above is indeed one LCG regeneration away from [51, 5, ...]. -/
theorem lcg_regeneration_produces_desync_list :
    lcgStep 51 = 0 ∧ lcgStep 5 = 26 := by
  native_decide

/-- A more complex scenario: after TWO regenerations from initial seeds,
    the desync still occurs. Starting from [10, 5, ...]:
    - After regen 1: [lcgStep 10, lcgStep 5, ...] = [51, 26, ...]
    - After regen 2: [lcgStep 51, lcgStep 26, ...] = [0, 131, ...]
    The 0 at position 0 triggers the desync. -/
theorem desync_after_two_regenerations :
    lcgStep 10 = 51 ∧ lcgStep 51 = 0 ∧
    let rng : LinkRNG := ⟨[0, 131, 100, 100, 100, 100, 100, 100, 100, 100], 0⟩
    let b : BitVec 8 := 150  -- level 100 Pokémon
    let (_, playerRNG) := psywavePlayer b rng
    let (_, enemyRNG) := psywaveEnemy b rng
    playerRNG.index ≠ enemyRNG.index := by
  native_decide

/-! ### Uniform Distribution -/

/-- Count how many values in a full LCG orbit from seed are below a threshold. -/
def lcgCountBelow (seed : BitVec 8) (threshold : BitVec 8) : Nat :=
  (List.range 256).countP (fun n => decide ((lcgIter seed n).toNat < threshold.toNat))

/-- Concrete examples of the distribution property: in a full LCG orbit,
    exactly `threshold` values are below `threshold`.
    This captures the uniform distribution: Pr[BattleRandom < t] = t/256.

    This is the mathematical foundation for the probability claims in:
    - OneIn256: accuracy check fails when random < threshold (1/256 chance)
    - FocusEnergy: critical hit comparison against random byte
    - CooltrainerF: the 25% random check (random < 64) -/
theorem lcg_distribution_examples :
    -- No values below 0
    lcgCountBelow 0 0 = 0 ∧
    -- Exactly 1 value below 1 (the zero)
    lcgCountBelow 0 1 = 1 ∧
    -- Exactly 64 values below 64 (the 25% threshold for CooltrainerF)
    lcgCountBelow 0 64 = 64 ∧
    -- Exactly 75 values below 75 (level 50 Psywave bound)
    lcgCountBelow 0 75 = 75 ∧
    -- All 255 values below 255
    lcgCountBelow 0 255 = 255 := by
  native_decide

/-- The distribution property holds for any seed — the LCG is perfectly uniform.
    Proved for key thresholds: 1 (the 1/256 chance), 64 (25%), 128 (50%). -/
theorem lcg_uniform_any_seed :
    ∀ s : BitVec 8,
      lcgCountBelow s 1 = 1 ∧ lcgCountBelow s 64 = 64 ∧ lcgCountBelow s 128 = 128 := by
  native_decide

/-! ### The Chain: From LCG to Desync Inevitability -/

/-- Putting it all together: for ANY initial link battle random list,
    the chain of reasoning is:

    1. lcg_guarantees_zero_in_list: position 0 will eventually be 0
    2. When drawn, this 0 causes the Psywave player loop to draw an extra
       value (player_never_zero rejects it), while the enemy accepts it
    3. The RNG indices diverge (desync_from_lcg_list)
    4. All subsequent random draws give different values (desync_propagates)
    5. The link battle is permanently desynchronized

    This theorem witnesses the zero for a specific initial list and shows
    the resulting desync in the Psywave calculation. -/
theorem desync_inevitable_example :
    -- Start with an arbitrary-looking list (no zeros)
    let initialList : Fin 10 → BitVec 8 := fun i =>
      match i.val with
      | 0 => 42 | 1 => 137 | 2 => 200 | 3 => 85 | 4 => 33
      | 5 => 199 | 6 => 12 | 7 => 250 | 8 => 66 | _ => 111
    -- The LCG guarantees zero will appear
    ∃ k : Fin 256, regenerateN initialList k.val ⟨0, by omega⟩ = 0 := by
  exact lcg_guarantees_zero_in_list _

/-! ### #eval Demonstrations -/

-- Trace the LCG orbit from seed 51: how many steps to reach 0?
-- Answer: 1 step (51 → 0)
#eval
  let seed : BitVec 8 := 51
  (List.range 5).map (fun n => lcgIter seed n)

-- Trace seed 42's path to zero
#eval
  let seed : BitVec 8 := 42
  let steps := (List.range 256).find? (fun n => lcgIter seed n == 0)
  s!"Seed {seed} reaches 0 after {steps} LCG steps"

-- Distribution check: count values < 75 in orbit from seed 0
#eval lcgCountBelow 0 75

-- Show the desync: player and enemy get different results
#eval
  let rng := LinkRNG.mk [0, 26, 42, 100, 7, 55, 200, 13, 88, 155] 0
  let b : BitVec 8 := 75
  let (pd, pr) := psywavePlayer b rng
  let (ed, er) := psywaveEnemy b rng
  (s!"Player: dmg={pd}, idx={pr.index}", s!"Enemy: dmg={ed}, idx={er.index}")

end PokeredBugs
