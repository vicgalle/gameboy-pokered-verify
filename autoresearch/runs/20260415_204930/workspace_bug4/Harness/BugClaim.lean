/-
  Harness/BugClaim.lean — Structured type for bug claims.

  Each verified bug fills in a BugClaim, providing:
  - The buggy implementation (translated from asm)
  - The intended specification
  - A witness that demonstrates the bug
  - Optionally: a full characterization and a verified fix
-/

namespace Harness

/-- Difficulty level of a bug verification. -/
inductive DifficultyLevel where
  | L1  -- Concrete witness: spec w ≠ impl w
  | L2  -- Complete characterization: ∀ x, bug triggers ↔ condition
  | L3  -- Fix correctness: ∀ x, fixed x = spec x
  | L4  -- Relational (desync): ∀ s, host s = guest s
  deriving Repr, DecidableEq

/-- Bug category classification. -/
inductive BugCategory where
  | wrongBitwiseOp      -- e.g., srl instead of sla
  | offByOne            -- e.g., < vs ≤
  | arithmeticUnderflow -- e.g., subtraction wraps to 0
  | integerTruncation   -- e.g., division loses information
  | deadCode            -- e.g., missing branch/early return
  | missingPrecondition -- e.g., missing HP check
  | symmetryViolation   -- e.g., host vs guest mismatch
  | staleState          -- e.g., state not cleared between turns
  | arithmeticOverflow  -- e.g., stat boost uncapped
  deriving Repr, DecidableEq

/-- A structured claim about a bug in pokered, parameterized over input/output types.

    The LLM agent fills in this structure. Lean's type checker verifies it.
    - `impl` and `spec` must be provided
    - `witness` and `witnessProof` must be provided (L1 minimum)
    - `characterization` and `fixVerification` are optional (L2+, L3+) -/
structure BugClaim (α β : Type) where
  /-- Human-readable name for the bug. -/
  name : String
  /-- Description of what the bug does. -/
  description : String
  /-- Source file in pret/pokered. -/
  source : String
  /-- Bug category. -/
  category : BugCategory
  /-- Difficulty levels achieved. -/
  levels : List DifficultyLevel
  /-- The actual (buggy) implementation, translated from assembly. -/
  impl : α → β
  /-- The intended specification (what the code should do). -/
  spec : α → β

/-- A verified bug witness: a concrete input where impl ≠ spec. -/
structure BugWitness (α β : Type) [DecidableEq β] (claim : BugClaim α β) where
  /-- The witness input that triggers the bug. -/
  witness : α
  /-- Proof that the spec and impl disagree on the witness. -/
  witnessProof : claim.spec witness ≠ claim.impl witness

/-- A verified bug fix: a replacement implementation that matches spec everywhere. -/
structure BugFix (α β : Type) (claim : BugClaim α β) where
  /-- The fixed implementation. -/
  fix : α → β
  /-- Proof that the fix matches the spec for all inputs. -/
  fixCorrect : ∀ x, fix x = claim.spec x

end Harness
