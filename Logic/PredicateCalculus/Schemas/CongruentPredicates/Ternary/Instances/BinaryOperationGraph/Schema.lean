import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND


-- # BinaryOperationGraph — a left-total and right-determined congruent ternary predicate
--
-- A `BinaryOperationGraph U₁ U₂ U₃` IS a `CongruentTernaryPredicate U₁ U₂ U₃`
-- (via structure extension) refined with two additional proof obligations:
-- `ltot` and `rdet`, certifying that the predicate represents the graph of a
-- total function from `U₁ × U₂` to `U₃`, and therefore can be used to
-- construct a `BinaryOperation U₁ U₂ U₃`.
--
-- - **left-totality**: ∀ x y, ∃ z, pred x y z — every input pair has at least one output.
-- - **right-determinacy**: ∀ x y z₁ z₂, pred x y z₁ ∧ pred x y z₂ → z₁ =₍U₃₎ z₂ — outputs are unique.
--
-- Making `BinaryOperationGraph` a refinement of `CongruentTernaryPredicate`
-- gates the introduction of a `BinaryOperation` behind discharged proofs of
-- left-totality and right-determinacy, so no silently inconsistent operation
-- can be declared.
structure BinaryOperationGraph (U₁: Universal) (U₂: Universal) (U₃: Universal): Type extends CongruentTernaryPredicate U₁ U₂ U₃ where
  ltot: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∃ (z: U₃.Particular), pred x y z
  rdet: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular), pred x y z₁ ∧ pred x y z₂ → z₁ =₍U₃₎ z₂


-- # Smart constructor: extend a `CongruentTernaryPredicate` with totality and
-- right-determinacy obligations to produce a `BinaryOperationGraph`.
--
-- Architecturally honest: `BinaryOperationGraph` IS a `CongruentTernaryPredicate`
-- refined with two extra proof obligations. This constructor takes the parent
-- struct directly plus the two obligations and bundles them.
--
-- The constructor is agnostic to HOW the `CongruentTernaryPredicate` was
-- obtained: typeclass-driven auto-cong via `CoeDep`, or manual construction
-- with an explicit cong proof — both are valid inputs.
--
-- At call sites, implicit universe parameters must be propagated explicitly
-- (`<thm> (U := U)`) so Lean can unify theorem signatures with the
-- constructor's expected types for `ltot` and `rdet`.
noncomputable def BinaryOperationGraph.fromCongPred {U₁ U₂ U₃: Universal}
    (ctp: CongruentTernaryPredicate U₁ U₂ U₃)
    (ltot: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∃ (z: U₃.Particular), ctp.pred x y z)
    (rdet: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular), ctp.pred x y z₁ ∧ ctp.pred x y z₂ → z₁ =₍U₃₎ z₂)
    : BinaryOperationGraph U₁ U₂ U₃ := {
      toCongruentTernaryPredicate := ctp
      ltot := ltot
      rdet := rdet
    }


-- # Fiber: specialise a binary graph to a unary graph at a fixed first argument.
--
-- Given a `BinaryOperationGraph U₁ U₂ U₃` and `x : U₁.Particular`, the
-- specialisation `y, z ↦ pred x y z` is itself a `UnaryOperationGraph U₂ U₃`:
-- - pred y z := original `pred x y z`
-- - cong: derived from the ternary cong with `=₍U₁₎`-reflexivity on x
-- - ltot: original ltot restricted to fixed x
-- - rdet: original rdet restricted to fixed x
--
-- This is the framework primitive that lets a binary operation produce
-- a unary operation per first argument (curried form).
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
noncomputable def BinaryOperationGraph.fiber {U₁ U₂ U₃: Universal} (G: BinaryOperationGraph U₁ U₂ U₃) (x: U₁.Particular): UnaryOperationGraph U₂ U₃ :=
  let pred: U₂.Particular → U₃.Particular → Prop := (y: U₂.Particular, z: U₃.Particular ↦ G.pred x y z)
  let cong: ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular), y₁ =₍U₂₎ y₂ → z₁ =₍U₃₎ z₂ → (G.pred x y₁ z₁ ↔ G.pred x y₂ z₂) := by forall_intro
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    variable(z₁: U₃.Particular)
    variable(z₂: U₃.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    assume(h₂: z₁ =₍U₃₎ z₂)
    -- Combined ternary cong, instantiated with reflexivity on the first arg.
    have h₃: x =₍U₁₎ x → y₁ =₍U₂₎ y₂ → z₁ =₍U₃₎ z₂ → (G.pred x y₁ z₁ ↔ G.pred x y₂ z₂) := by forall_elim G.cong, x, x, y₁, y₂, z₁, z₂
    have h₄: x =₍U₁₎ x := by forall_elim U₁.eq.refl, x
    have h₅: y₁ =₍U₂₎ y₂ → z₁ =₍U₃₎ z₂ → (G.pred x y₁ z₁ ↔ G.pred x y₂ z₂) := by modus_ponens h₃, h₄
    have h₆: z₁ =₍U₃₎ z₂ → (G.pred x y₁ z₁ ↔ G.pred x y₂ z₂) := by modus_ponens h₅, h₁
    have h₇: G.pred x y₁ z₁ ↔ G.pred x y₂ z₂ := by modus_ponens h₆, h₂
    iterate h₇
  let ltot: ∀ (y: U₂.Particular), ∃ (z: U₃.Particular), G.pred x y z := by forall_intro
    variable(y: U₂.Particular)
    have h₁: ∃ (z: U₃.Particular), G.pred x y z := by forall_elim G.ltot, x, y
    iterate h₁
  let rdet: ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular), G.pred x y z₁ ∧ G.pred x y z₂ → z₁ =₍U₃₎ z₂ := by forall_intro
    variable(y: U₂.Particular)
    variable(z₁: U₃.Particular)
    variable(z₂: U₃.Particular)
    have h₁: G.pred x y z₁ ∧ G.pred x y z₂ → z₁ =₍U₃₎ z₂ := by forall_elim G.rdet, x, y, z₁, z₂
    iterate h₁
  { pred := pred, cong := cong, ltot := ltot, rdet := rdet }


end PC₁

end Logic
