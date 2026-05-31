# Relation Subsumption — Design

## Context

This design assumes the `Relation` refactor from
[`relation-as-primitive-universal.md`](./relation-as-primitive-universal.md)
is in place: `Rel U₁ U₂ := CongruentBinaryPredicate U₁ U₂`. A relation is a
binary predicate; the set-of-dyads view (if needed) is a separate registered
isomorphism via `dyad_extension`.

This document specifies how **sub-universal embeddings on the component
universals lift to a sub-universal embedding on relations** — i.e., given
embeddings `e₁ : U₁' <: U₁` and `e₂ : U₂' <: U₂`, how to register
`Rel U₁' U₂' <: Rel U₁ U₂`.

## Why subsumption matters

Sub-universal embeddings propagate through composite universals. The framework
already handles propagation for:

- Refined universals (`(U ↾ P) <: U`)
- Dyads (if `U₁' <: U₁` and `U₂' <: U₂`, then `U₁' ⧓ U₂' <: U₁ ⧓ U₂`)
- Arrows (analogously)
- Sets (via the generic CoeDep on `SubUniversal`)

Relations are no longer derived from sets-of-dyads, so they need their own
propagation rule. Without it, downstream proofs that operate on relations
across sub-universals can't use coercion — they'd have to manually translate
between `Rel U₁' U₂'` and `Rel U₁ U₂`.

## The shape of the lift

Given:
- `e₁ : U₁' <: U₁`
- `e₂ : U₂' <: U₂`
- `R' : Rel U₁' U₂'` (a binary predicate on the sub-universals)

The natural lift `R : Rel U₁ U₂` says: *R holds at `(x, y)` exactly when
`(x, y)` is the image of some `(a', b')` under the embeddings, with `R'(a', b')`
holding there.*

In framework syntax (the pointwise characterization):
```
(R.pred x).pred y ↔ ∃ (a' : U₁'.Particular), ∃ (b' : U₂'.Particular),
                      x =₍U₁₎ e₁.embedding a' ∧
                      y =₍U₂₎ e₂.embedding b' ∧
                      (R'.pred a').pred b'
```

R is false at any `(x, y)` not in the image of the embeddings, and tracks `R'`
exactly on the image.

## Comparison with the pre-refactor approach

Before the primitive-universal refactor, relations were sets of dyads:
`Rel U₁ U₂ = Set (U₁ ⧓ U₂)`. Subsumption was a two-step composition:

1. **Dyad subsumption** — `U₁' ⧓ U₂' <: U₁ ⧓ U₂` (lift dyads via `e₁`, `e₂`).
2. **Set subsumption** — `Set (U₁' ⧓ U₂') <: Set (U₁ ⧓ U₂)` (generic CoeDep
   on `SubUniversal`).

The composition produced `Rel U₁' U₂' <: Rel U₁ U₂` indirectly. Each step had
its own existential structure (dyads ranging over components; sets ranging
over dyads). The composition stacked them.

After the refactor, with `Rel = CongruentBinaryPredicate`:

- **One step** — direct binary-predicate lift via the existential above.

The existential content is similar to the old dyad-then-set composition, but
expressed directly on binary predicates without routing through an
intermediate representation. The result is conceptually cleaner — and proofs
about `subsume R'` reason about a binary predicate's behavior, not a set of
dyads' extension.

| | Pre-refactor (Set of Dyads) | Post-refactor (Binary Predicate) |
|---|---|---|
| Intermediate types | Dyad universal + Set universal | None |
| Composition steps | 2 (dyad lift + set lift) | 1 (direct binary lift) |
| Mathematical content | "Lift the underlying dyads, then the set containing them" | "Lift the binary predicate by existential preimage" |
| Reasoning style | Dyad decomposition + set membership | Binary predicate application |
| `R'(a',b') ⟹ R(e₁ a', e₂ b')` | Indirect (via dyad decomposition) | Direct (witnesses `a := a'`, `b := b'`) |

## Construction — the three-layer ADT pattern

This follows the same three-layer pattern as `Dyads.subsume` (see
`Universals/Dyads/Predicates/Binary/SubsumptionGraph/`,
`Universals/Dyads/Operations/Unary/Subsumption/`,
`Universals/Dyads/Properties/Subsumptivity.lean`) and the
`dyad_extension` construction described in
[`relation-as-primitive-universal.md`](./relation-as-primitive-universal.md).

### Layer 1 — the subsumption graph

A `CongruentBinaryPredicate (Rel U₁' U₂') (Rel U₁ U₂)` paired with
left-totality and right-determinacy.

File: `Universals/Relations/Predicates/Binary/SubsumptionGraph/Predicate.lean`.

```lean
@[reducible] private def subsumption_graph_pred
    {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    Rel U₁' U₂' → Rel U₁ U₂ → Prop :=
  (R' : Rel U₁' U₂', R : Rel U₁ U₂ ↦
     ∀ (x : U₁.Particular), ∀ (y : U₂.Particular),
       (R.pred x).pred y ↔ ∃ (a' : U₁'.Particular), ∃ (b' : U₂'.Particular),
                              x =₍U₁₎ e₁.embedding a' ∧
                              y =₍U₂₎ e₂.embedding b' ∧
                              (R'.pred a').pred b')

noncomputable def subsumption_graph
    {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    UnaryOperationGraph (Rel U₁' U₂') (Rel U₁ U₂) :=
  let graph : CongruentBinaryPredicate (Rel U₁' U₂') (Rel U₁ U₂) := subsumption_graph_pred e₁ e₂
  let ltot  := subsume_left_totality e₁ e₂
  let rdet  := subsume_right_determinacy e₁ e₂
  { pred := graph.pred, cong := graph.cong, ltot := ltot, rdet := rdet }
```

Plus `Properties/LeftTotality.lean` and `Properties/RightDeterminacy.lean`:

- **Left-totality**: for every `R'`, some `R` satisfies the graph. Construction:
  define `R.pred x .pred y := ∃ a' b', x =₍U₁₎ e₁ a' ∧ y =₍U₂₎ e₂ b' ∧ R'.pred a' .pred b'`
  and prove congruence (auto-derivable or via `e₁.preserves_eq`/`e₂.preserves_eq`
  and `R'.cong`).
- **Right-determinacy**: if `R₁` and `R₂` both satisfy the graph for `R'`,
  then `R₁ =ᵣₑₗ R₂`. By extensional equality of binary predicates: both
  agree pointwise on every `(x, y)` by the graph, so they're equal.

### Layer 2 — the subsumption operation

File: `Universals/Relations/Operations/Unary/Subsumption/Operation.lean`.

```lean
axiom subsume_sym
    {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    Rel U₁' U₂' → Rel U₁ U₂

axiom subsume_def
    {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    ∀ (R' : Rel U₁' U₂'), ∀ (R : Rel U₁ U₂),
      (subsume_sym e₁ e₂ R' =ᵣₑₗ R) ↔ ((subsumption_graph e₁ e₂).pred R').pred R

noncomputable def subsume
    {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    Rel U₁' U₂' ⟴ Rel U₁ U₂ :=
  { graph := subsumption_graph e₁ e₂,
    op := subsume_sym e₁ e₂,
    «def» := subsume_def e₁ e₂ }
```

Standard ADT pattern: opaque function symbol, defining axiom tying it to the
graph, bundled `UnaryOperation`. Downstream proofs see `subsume R'` only
through `subsume_def` (or via the pointwise corollary below).

### Pointwise corollary

File: `Universals/Relations/Operations/Unary/Subsumption/Properties/Equations.lean`.

The form most downstream proofs will actually use:

```lean
theorem subsume_pair
    {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    ∀ (R' : Rel U₁' U₂'), ∀ (x : U₁.Particular), ∀ (y : U₂.Particular),
      ((subsume e₁ e₂ R').pred x).pred y ↔
        ∃ (a' : U₁'.Particular), ∃ (b' : U₂'.Particular),
          x =₍U₁₎ e₁.embedding a' ∧
          y =₍U₂₎ e₂.embedding b' ∧
          (R'.pred a').pred b'
```

Proved from `subsume_def` instantiated at `subsume e₁ e₂ R'` and unfolded
through `subsumption_graph_pred`.

### Layer 3 — the subsumptivity instance

File: `Universals/Relations/Properties/Subsumptivity.lean`.

```lean
noncomputable instance subsumptivity
    {U₁' U₁ U₂' U₂: Universal}
    [e₁: U₁' <: U₁] [e₂: U₂' <: U₂]:
    Rel U₁' U₂' <: Rel U₁ U₂ :=
  let subsume : Rel U₁' U₂' ⟴ Rel U₁ U₂ := subsume e₁ e₂
  let preserves_eq:
      ∀ (R₁' : Rel U₁' U₂'), ∀ (R₂' : Rel U₁' U₂'),
        R₁' =ᵣₑₗ R₂' ↔ (subsume R₁' =ᵣₑₗ subsume R₂') := by ...
  { embedding := subsume, preserves_eq := preserves_eq }
```

The `preserves_eq` proof:

- **Forward** (congruence, supplied by `UnaryOperation`): if `R₁' =ᵣₑₗ R₂'`,
  then `subsume R₁' =ᵣₑₗ subsume R₂'` by `subsume.cong`.
- **Backward** (injectivity): assume `subsume R₁' =ᵣₑₗ subsume R₂'`. Extensional
  equality on binary predicates: for every `(x, y)`, `(subsume R₁').pred x .pred y
  ↔ (subsume R₂').pred x .pred y`. Instantiate at `(e₁.embedding a', e₂.embedding b')`
  for arbitrary `a', b'`. By `subsume_pair`, this reduces to:
  ```
  ∃ ..., e₁.embedding a' =₍U₁₎ e₁.embedding _ ∧ e₂.embedding b' =₍U₂₎ e₂.embedding _ ∧ R₁'.pred ... ↔
  ∃ ..., e₁.embedding a' =₍U₁₎ e₁.embedding _ ∧ e₂.embedding b' =₍U₂₎ e₂.embedding _ ∧ R₂'.pred ...
  ```
  Pick the witness `a'` for the left existential; by `e₁.preserves_eq` backward
  (and similarly for `e₂`), this gives `R₁'.pred a' .pred b' ↔ R₂'.pred a' .pred b'`
  for arbitrary `a', b'`. That's the extensional equality of `R₁'` and `R₂'`,
  i.e., `R₁' =ᵣₑₗ R₂'`.

The injectivity of `e₁` and `e₂` (encoded in their `preserves_eq`) is what
makes the backward direction work — it's where bi-embedded sub-universals
distinguish their elements.

## File layout

```
Universals/Relations/
├── Predicates/Binary/SubsumptionGraph/
│   ├── Predicate.lean                       -- subsumption_graph_pred + UnaryOperationGraph bundle
│   └── Properties/
│       ├── LeftTotality.lean                -- existence of a lifted R
│       └── RightDeterminacy.lean            -- uniqueness up to =ᵣₑₗ
├── Operations/Unary/Subsumption/
│   ├── Operation.lean                       -- subsume_sym (axiom) + subsume_def (axiom) + bundled UnaryOperation
│   └── Properties/
│       └── Equations.lean                   -- subsume_pair (pointwise characterization)
└── Properties/
    └── Subsumptivity.lean                   -- subsumptivity instance
```

This mirrors `Universals/Dyads/`'s subsumption layout exactly. Reading one
explains the other.

## Verification

- `Test/RelationSubsumptionCoercion.lean` (or similar): construct a binary
  predicate on `(U₁', U₂')`, register sub-universal instances `U₁' <: U₁`
  and `U₂' <: U₂`, and verify that the resulting `Rel U₁' U₂' <: Rel U₁ U₂`
  fires CoeDep coercion automatically. Verify that membership of an embedded
  pair `(e₁ a', e₂ b')` in `subsume R'` reduces (via `subsume_pair`) to
  `R'.pred a' .pred b'`.

## When to build this

When a downstream proof needs to use a relation across sub-universals — most
likely when migrating something in `Universals/Correspondences/` that depends
on `Universals/Relations/` and expects sub-universal propagation. Until then,
this design sits documented; the construction recipe is here for when the
need arises.

## Out of scope

- **Lifting binary predicates that aren't relations** (i.e., directly working
  with `CongruentBinaryPredicate U₁ U₂` without the Relation universal wrapper).
  The above operates on `Rel`, the wrapped form. If a use case for the
  unwrapped form arises, it would follow the same construction.
- **N-ary relation subsumption** (ternary and higher). Follow-up work, same
  pattern.
- **Subsumption of correspondences**. Likely follows from `Correspondences`
  being refactored to a primitive universal in its own right (a future design
  decision), at which point its subsumption would be a separate document
  parallel to this one.

## Summary

Relation subsumption fits naturally in the post-refactor architecture: a
single binary-predicate lift via existential preimage, packaged into the
standard three-layer ADT structure (graph + operation + subsumptivity
instance). Same machinery as `Dyads.subsume`, just at one level higher in
the predicate-arity hierarchy.

The construction is cleaner than the pre-refactor approach because it
eliminates the dyad-then-set composition — but no new framework
infrastructure is needed. Build it when the first downstream proof actually
exercises a relation across sub-universals.
