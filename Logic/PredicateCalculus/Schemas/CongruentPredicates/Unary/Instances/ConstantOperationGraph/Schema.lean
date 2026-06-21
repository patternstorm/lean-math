import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals

namespace Logic

namespace PC₁


-- # ConstantOperationGraph — a congruent unary predicate refined with existence and uniqueness
--
-- A `ConstantOperationGraph U` IS a `CongruentUnaryPredicate U`
-- (via structure extension) refined with two additional proof obligations:
-- `existence` and `uniqueness`, which together ensure the predicate
-- characterizes a single particular of `U`, and therefore can be used to
-- construct a `ConstantOperation U`.
--
-- ## Why this layer exists
--
-- The `ConstantOperation` schema introduces, as an axiom, the defining equation
--
--   op =₍U₎ c  ↔  graph.pred c
--
-- This axiom is consistent only when `graph.pred` is satisfied by exactly one
-- particular of `U` — i.e., the predicate characterizes a unique constant:
--
-- - `ltot` — left-totality at 0-arity collapses to bare existence: ∃ c, pred c.
-- - `rdet` — right-determinacy at 0-arity collapses to uniqueness:
--   ∀ c₁ c₂, pred c₁ ∧ pred c₂ → c₁ =₍U₎ c₂.
--
-- Names `ltot` and `rdet` are kept for symmetry with `UnaryOperationGraph` /
-- `BinaryOperationGraph` — the 0-input collapse of the same obligation shape.
--
-- If either property fails, the axiom derives a contradiction:
--
-- - `ltot` failure: reflexivity gives `op =₍U₎ op`, so the forward direction
--   of the axiom forces `graph.pred op`. If no witness exists, this is
--   impossible.
-- - `rdet` failure: if `graph.pred c₁` and `graph.pred c₂` both hold with
--   `¬(c₁ =₍U₎ c₂)`, the backward direction forces `op =₍U₎ c₁` and
--   `op =₍U₎ c₂`; `sym + trans` then collapses `c₁ =₍U₎ c₂`, merging
--   originally distinct particulars.
--
-- Making `ConstantOperationGraph` a refinement of `CongruentUnaryPredicate`
-- gates the introduction of a `ConstantOperation` behind discharged proofs of
-- `ltot` and `rdet`, so no silently inconsistent constant can be declared.
--
-- ## Relationship with `CongruentUnaryPredicate`
--
-- A constant operation graph **is** a congruent unary predicate — `pred` and
-- `cong` are inherited — with two extra well-formedness obligations. Anywhere
-- a `CongruentUnaryPredicate U` is expected, a `ConstantOperationGraph U` is
-- accepted via Lean coercion.
structure ConstantOperationGraph (U: Universal): Type extends CongruentUnaryPredicate U where
  ltot: ∃ (x: U.Particular), pred x
  rdet: ∀ (x₁: U.Particular), ∀ (x₂: U.Particular), pred x₁ ∧ pred x₂ → x₁ =₍U₎ x₂


-- # Smart constructor: extend a `CongruentUnaryPredicate` with left-totality
-- and right-determinacy obligations to produce a `ConstantOperationGraph`.
--
-- Architecturally honest: `ConstantOperationGraph` IS a `CongruentUnaryPredicate`
-- refined with two extra proof obligations. This constructor takes the parent
-- struct directly plus the two obligations and bundles them — no need for
-- callers to manually plumb `pred` and `cong` fields.
--
-- The constructor is agnostic to HOW the `CongruentUnaryPredicate` was
-- obtained: the typeclass-driven auto-cong machinery (via `CoeDep`) is one
-- common path, but manually-built CUPs with explicit cong proofs are equally
-- valid inputs.
--
-- At call sites, implicit universe parameters must be propagated explicitly
-- (`<thm> (U := U)`) so Lean can unify the theorem signatures with the
-- constructor's expected types for `ltot` and `rdet`.
noncomputable def ConstantOperationGraph.fromCongPred {U: Universal}
    (cup: CongruentUnaryPredicate U)
    (ltot: ∃ (c: U.Particular), cup.pred c)
    (rdet: ∀ (c₁: U.Particular), ∀ (c₂: U.Particular), cup.pred c₁ ∧ cup.pred c₂ → c₁ =₍U₎ c₂)
    : ConstantOperationGraph U := {
      toCongruentUnaryPredicate := cup
      ltot := ltot
      rdet := rdet
    }


end PC₁

end Logic
