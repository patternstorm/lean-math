import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals

namespace Logic

namespace PC₁

/-!
# UnaryOperationGraph — a left-total and right-determined congruent binary predicate

A `UnaryOperationGraph U₁ U₂` **is** a `CongruentBinaryPredicate U₁ U₂`
(via structure extension) refined with two additional proof obligations:
`ltot` and `rdet`, which ensures the predicate represents the graph of a total function from `U₁` to `U₂`,
and therefore can be used to construct a `UnaryOperation U₁ U₂`.

## Why this layer exists

The `UnaryOperation` schema introduces, as an axiom, the defining equation

  op x =₍U₂₎ y  ↔  (graph.pred x).pred y

This axiom is consistent only when graph.pred is left-total and right-determined,
and therefore encodes a total function from `U₁` to `U₂` — i.e., for every input `x`:

- **left-totality**: there exists at least one `y` such that `(ext.pred x).pred y`.
- **right-determinacy**: any two such `y`s are equal in `U₂`.

If either property fails, the axiom derives a contradiction:

- Left-totality failure: reflexivity gives `op x =₍U₂₎ op x`, so the forward
  direction of the axiom forces `(ext.pred x).pred (op x)`. If no witness
  exists, this is impossible.
- Right-determinacy failure: if `(ext.pred x).pred y₁` and `(ext.pred x).pred y₂`
  both hold with `y₁ ≠₍U₂₎ y₂`, the backward direction forces
  `op x =₍U₂₎ y₁` and `op x =₍U₂₎ y₂`; `sym + trans` then collapses
  `y₁ =₍U₂₎ y₂`, merging originally distinct particulars.

Making `UnaryOperationGraph` a refinement of `CongruentBinaryPredicate`
gates the introduction of a `UnaryOperation` behind discharged proofs of
left-totality and right-determinacy, so no silently inconsistent operation can be
declared.

## Relationship with `CongruentBinaryPredicate`

A unary operation graph **is** a congruent binary predicate — `pred` and `cong` are
inherited — with two extra well-formedness obligations. Anywhere a
`CongruentBinaryPredicate U₁ U₂` is expected, a `UnaryOperationGraph U₁ U₂` is accepted via
Lean coercion.
-/
structure UnaryOperationGraph (U₁: Universal) (U₂: Universal): Type extends CongruentBinaryPredicate U₁ U₂ where
  ltot: ∀ (x: U₁.Particular), ∃ (y: U₂.Particular), pred x y
  rdet: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), pred x y₁ ∧ pred x y₂ → y₁ =₍U₂₎ y₂


-- # Smart constructor: extend a `CongruentBinaryPredicate` with totality and
-- right-determinacy obligations to produce a `UnaryOperationGraph`.
--
-- Architecturally honest: `UnaryOperationGraph` IS a `CongruentBinaryPredicate`
-- refined with two extra proof obligations. This constructor takes the parent
-- struct directly plus the two obligations and bundles them — no need for
-- callers to manually plumb `pred` and `cong` fields.
--
-- The constructor is agnostic to HOW the `CongruentBinaryPredicate` was
-- obtained: the typeclass-driven auto-cong machinery (via `CoeDep`) is one
-- common path, but manually-built CBPs with explicit cong proofs are equally
-- valid inputs.
--
-- At call sites, implicit universe parameters must be propagated explicitly
-- (`<thm> (U := U)`) so Lean can unify the theorem signatures with the
-- constructor's expected types for `ltot` and `rdet`.
noncomputable def UnaryOperationGraph.fromCongPred {U₁ U₂: Universal}
    (cbp: CongruentBinaryPredicate U₁ U₂)
    (ltot: ∀ (x: U₁.Particular), ∃ (y: U₂.Particular), cbp.pred x y)
    (rdet: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), cbp.pred x y₁ ∧ cbp.pred x y₂ → y₁ =₍U₂₎ y₂)
    : UnaryOperationGraph U₁ U₂ := {
      toCongruentBinaryPredicate := cbp
      ltot := ltot
      rdet := rdet
    }


end PC₁

end Logic
