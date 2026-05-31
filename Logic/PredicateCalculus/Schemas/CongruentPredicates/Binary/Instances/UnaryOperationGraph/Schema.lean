import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema

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

end PC₁

end Logic
