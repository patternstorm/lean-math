# Relation as a Primitive Universal — Refactor Plan

## Motivation

### What we discovered

The framework's principle is that all logical reasoning is propositional: every
equivalence between two propositions used in a proof must appear as a named
biconditional (or implication) inside that proof. Lean's kernel-level
reduction of `def`s — silently bridging propositions during unification — is
*not* an admissible inference step. If a proof's correctness depends on the
kernel performing that bridge, the proof has skipped a step.

### Where the framework violated its own principle

The current architecture identifies `Relation U₁ U₂` with `Set (U₁ ⧓ U₂)` — a
set of dyads. To create a relation from a binary predicate, the framework
provides `relation_from`, which performs an **element-pattern construction**
with an existential body:

```lean
def relation_from (P : CongruentBinaryPredicate U₁ U₂) : Set (U₁ ⧓ U₂) :=
  { d | ∃ a b, d =₍U₁⧓U₂₎ (a ⋈ b) ∧ P.pred a b }
```

The body's specific shape (existential) is incidental to the mathematical
meaning. Proofs about relations built this way — like the
`co_classification_unfold` proof in
`Universals/Correspondences/Operations/Unary/CoClassification/Operation.lean` —
were silently coupled to the body's syntactic form via Lean's reduction. When
the body was refactored (e.g., from `uncurry`-based to existential-based),
those proofs broke. They had been relying on a propositional bridge that was
never stated.

This is a violation of the framework's principle. The proofs followed the
letter of the rules (no forbidden tactics) but appealed to kernel reduction
to short-circuit propositional steps that should have been explicit.

### The architectural mistake

The deeper issue is that **`Relation` should not be a derived universal at
all**. Mathematically, a relation is a binary predicate. The set-of-dyads view
is one possible *representation* — useful for some operations, but not
foundational. The current framework treats the set-of-dyads representation as
the relation's *definition*, which:

1. Forces every relation-producing operation to construct an element-pattern
   predicate over dyads, with the resulting existential gymnastics.
2. Couples proofs to that construction's body shape.
3. Conflates two distinct universals: "binary predicate as a relational object"
   and "set of dyads".

A relation is a binary predicate (with congruence). Period. That a relation
*can be viewed as* a set of dyads is a separate, optional fact — to be
expressed as a registered sub-universal embedding, not as the relation's
identity.

## The new architecture

### Bootstrap universals: one per predicate arity

The framework recognizes two distinct ways a `def` interacts with predicates
and particulars:

1. **Reification** — the canonical map from "predicate" to "particular" at a
   bootstrap universal. `set_from P := P` is the canonical example for `Set`.
   This is identity-like at the data level; no logical work is done; the def
   is `@[reducible]`.

2. **Construction** — building a new predicate or particular from existing
   material via real computation. Operations like `intersection`, `union`,
   `singleton_of`, `compl`, `l2r_correspondence`, etc. fall here. The body's
   shape is incidental; the meaningful content is the propositional
   characterization. These defs are `@[irreducible]` and ship with a
   characterization theorem (`_def`).

Under this view, the framework has a small set of **bootstrap universals**,
one per arity of fundamental predicate:

- `Set U` reifies `CongruentUnaryPredicate U` (already exists).
- `Relation U₁ U₂` reifies `CongruentBinaryPredicate U₁ U₂` (this refactor).
- (Future) `TernaryRelation U₁ U₂ U₃` reifies `CongruentTernaryPredicate U₁ U₂ U₃`.

Each bootstrap universal:
- Has Particulars = the appropriate `CongruentNaryPredicate`.
- Has extensional equality on the underlying predicate.
- Provides a reification primitive (`set_from`, `relation_from`, etc.) — `@[reducible]`, identity.

### The set-of-dyads view becomes a registered embedding

Once `Relation U₁ U₂` is its own universal, the relationship "a relation can
be viewed as a set of dyads" is expressed via the framework's existing
sub-universal embedding pattern. This is exactly the same three-layer
construction used by, e.g., `Dyads.subsume` (see
`Universals/Dyads/Predicates/Binary/SubsumptionGraph/`,
`Universals/Dyads/Operations/Unary/Subsumption/`,
`Universals/Dyads/Properties/Subsumptivity.lean`):

1. **The dyad extension graph** — a `CongruentBinaryPredicate (Relation U₁ U₂) (Set (U₁ ⧓ U₂))`
   plus its left-totality and right-determinacy properties.
2. **The dyad extension operation** — an axiomatic function symbol with a
   defining axiom that ties it to the graph, then bundled into a
   `UnaryOperation (Relation U₁ U₂) ⟴ Set (U₁ ⧓ U₂)`.
3. **The dyad extensibility instance** — the `SubUniversal` registration, using
   the bundled operation, with a `preserves_eq` proof.

#### Layer 1 — the dyad extension graph

Mathematical content: a relation `R` corresponds to a set of dyads `S` iff
for every dyad `d`, `d` is in `S` exactly when `d` decomposes as `(a ⋈ b)`
and `R.pred a b` holds. Or equivalently, in constructor-pattern form:
for every `a, b`, `(a ⋈ b) ∈ S ↔ R.pred a b`.

Files to create under `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/`:

```lean
-- Predicate.lean
@[reducible] private def dyad_extension_graph_pred {U₁ U₂: Universal}:
    Relation U₁ U₂ → Set (U₁ ⧓ U₂) → Prop :=
  (R : Relation U₁ U₂, S : Set (U₁ ⧓ U₂) ↦
     ∀ (a : U₁.Particular), ∀ (b : U₂.Particular),
       (a ⋈ b) ∈ₛₑₜ S ↔ R.pred a b)

noncomputable def dyad_extension_graph {U₁ U₂: Universal}:
    UnaryOperationGraph (Relation U₁ U₂) (Set (U₁ ⧓ U₂)) :=
  let graph : CongruentBinaryPredicate (Relation U₁ U₂) (Set (U₁ ⧓ U₂)) := dyad_extension_graph_pred
  let ltot := dyad_extension_left_totality
  let rdet := dyad_extension_right_determinacy
  { pred := graph.pred, cong := graph.cong, ltot := ltot, rdet := rdet }
```

Plus `Properties/LeftTotality.lean` and `Properties/RightDeterminacy.lean`,
proving:

- **Left-totality**: for every relation `R`, there exists a set of dyads `S`
  satisfying the graph. (Construction: take the set comprehension
  `{ d | ∃ a b, d =₍U₁⧓U₂₎ (a ⋈ b) ∧ R.pred a b }`. The framework's
  set comprehension machinery provides congruence; the membership of
  `(a ⋈ b)` follows from existential intro with witnesses `a, b` plus dyad
  reflexivity.)
- **Right-determinacy**: if `S₁` and `S₂` both satisfy the graph for `R`,
  then `S₁ =ₛₑₜ S₂`. (By set extensionality on the dyad universal: both
  agree on every constructor-pattern dyad `(a ⋈ b)` by the graph; by dyad
  exhaustiveness they agree on every dyad; therefore extensionally equal.)

#### Layer 2 — the dyad extension operation

Files to create under `Universals/BinaryRelations/Operations/Unary/DyadExtension/`:

```lean
-- Operation.lean
namespace Universe
namespace BinaryRelations

axiom dyad_extension_sym {U₁ U₂: Universal}: Relation U₁ U₂ → Set (U₁ ⧓ U₂)

axiom dyad_extension_def {U₁ U₂: Universal}:
  ∀ (R : Relation U₁ U₂), ∀ (S : Set (U₁ ⧓ U₂)),
    (dyad_extension_sym R =ₛₑₜ S) ↔ (dyad_extension_graph.pred R).pred S

noncomputable def dyad_extension {U₁ U₂: Universal}:
    Relation U₁ U₂ ⟴ Set (U₁ ⧓ U₂) :=
  { graph := dyad_extension_graph,
    op := dyad_extension_sym,
    «def» := dyad_extension_def }

end BinaryRelations
end Universe
```

This is the standard ADT pattern: an opaque function symbol, a defining
axiom that ties it propositionally to the graph, and the bundled
`UnaryOperation`. Downstream proofs reason about `dyad_extension R` only
through `dyad_extension_def` (or its pointwise corollary, see below) — they
never see a body. The bridge from "relation" to "set of dyads" is fully
propositional.

A pointwise corollary should also be proven (in
`Operations/Unary/DyadExtension/Properties/Equations.lean`):

```lean
theorem dyad_extension_mem {U₁ U₂: Universal}:
    ∀ (R : Relation U₁ U₂), ∀ (a : U₁.Particular), ∀ (b : U₂.Particular),
      (a ⋈ b) ∈ₛₑₜ (dyad_extension R) ↔ R.pred a b
```

This is the form most downstream proofs will actually use. It follows from
`dyad_extension_def` instantiated at the result of `dyad_extension R` and
unfolded through `dyad_extension_graph_pred`.

#### Layer 3 — the dyad extensibility instance

File to create at `Universals/BinaryRelations/Properties/DyadExtensibility.lean`:

```lean
noncomputable instance dyad_extensibility {U₁ U₂: Universal}:
    Relation U₁ U₂ <: Set (U₁ ⧓ U₂) :=
  let extension: Relation U₁ U₂ ⟴ Set (U₁ ⧓ U₂) := dyad_extension
  let preserves_eq:
      ∀ (R₁ R₂ : Relation U₁ U₂),
        R₁ =₍Relation U₁ U₂₎ R₂ ↔ (extension R₁ =ₛₑₜ extension R₂) := by ...
  { embedding := extension, preserves_eq := preserves_eq }
```

The `preserves_eq` proof:

- **Forward** (the embedding's congruence, already supplied by `UnaryOperation`):
  if `R₁ = R₂` as binary predicates (pointwise), then `dyad_extension R₁ = dyad_extension R₂` by `extension.cong`.
- **Backward** (injectivity): assume `extension R₁ =ₛₑₜ extension R₂`. Then by set
  extensionality, the two dyad sets agree on every dyad. In particular at every
  constructor-pattern `(a ⋈ b)`, by `dyad_extension_mem`:
  `R₁.pred a b ↔ R₂.pred a b`. That is exactly the equality of binary
  predicates (i.e., `R₁ =₍Relation U₁ U₂₎ R₂`, given that `Relation`'s equality
  is defined extensionally on the binary predicate).

#### Result

With this three-layer construction in place, the framework's existing
generic `CoeDep` instance on `SubUniversal` fires automatically. Anywhere a
`Set (U₁ ⧓ U₂)` is expected and a `Relation U₁ U₂` is supplied, Lean inserts
the embedding silently. Set operations on relations "just work" through
coercion — and at no point does any proof reach through a `def` body, because
there is no body to reach through: `dyad_extension_sym` is an axiom, its
behavior is defined propositionally by `dyad_extension_def` (with
`dyad_extension_mem` as the convenient constructor-pattern form).

### What disappears

- The old `relation_from` as a construction-with-existential — gone.
- The existential gymnastics in `co_classification_unfold` and similar
  proofs — gone, because the relation's "membership" is now just `R.pred a b`,
  with no constructor-pattern bridge needed.
- The conflation of "relation" with "set of dyads" — gone; they're two
  separate universals related by a registered embedding.

## Migration Strategy

A direct in-place refactor would break too many dependents at once. Instead,
we build the new universal alongside the old, migrate dependents
incrementally, verify each step, and only remove the old code once everything
is on the new one.

### Phase 0 — Preparation

1. Confirm `SubUniversal` and `CoeDep` machinery is healthy (already verified
   earlier in the session via the `subsume_sym` def refactor).
2. Audit current `Universals/Relations/` to enumerate operations and
   theorems that depend on `Relations.Particular = Set (U₁ ⧓ U₂)`.

### Phase 1 — Build the new universal alongside

Create a parallel directory `Universals/BinaryRelations/` (or similar
namespace) containing the new bootstrap universal. Old `Universals/Relations/`
stays intact.

Files to create (following the same three-layer pattern that `Dyads`
uses for `subsume`):

**Bootstrap universal:**

- `Universals/BinaryRelations/Particular.lean` — declares
  `BinaryRelations.Particular U₁ U₂ := CongruentBinaryPredicate U₁ U₂`.
- `Universals/BinaryRelations/Universal.lean` — defines
  `BinaryRelationsUniversal U₁ U₂` with extensional equality on the binary
  predicate.
- `Universals/BinaryRelations/Definitions/RelationFrom/Definition.lean` —
  the bootstrap reification primitive `relation_from R := R`. Marked
  `@[reducible]`. Parallel to `set_from`.

**Layer 1 — dyad extension graph (to Set of Dyads):**

- `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/Predicate.lean`
  — defines `dyad_extension_graph_pred` and bundles into
  `dyad_extension_graph : UnaryOperationGraph (Relation U₁ U₂) (Set (U₁ ⧓ U₂))`.
- `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/Properties/LeftTotality.lean`
  — proves that for every `R`, some `S` satisfies the graph.
- `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/Properties/RightDeterminacy.lean`
  — proves that two such `S` are extensionally equal.

**Layer 2 — dyad extension operation:**

- `Universals/BinaryRelations/Operations/Unary/DyadExtension/Operation.lean`
  — declares `dyad_extension_sym` as axiom, `dyad_extension_def` as defining
  axiom referring to the graph, and bundles into
  `dyad_extension : Relation U₁ U₂ ⟴ Set (U₁ ⧓ U₂)`.
- `Universals/BinaryRelations/Operations/Unary/DyadExtension/Properties/Equations.lean`
  — proves the pointwise corollary `dyad_extension_mem`.

**Layer 3 — dyad extensibility instance:**

- `Universals/BinaryRelations/Properties/DyadExtensibility.lean` — registers
  `Relation U₁ U₂ <: Set (U₁ ⧓ U₂)` via the bundled `dyad_extension`
  operation, with `preserves_eq` proof using `dyad_extension_mem` and dyad
  exhaustiveness.

**Verification:**

`Test/BinaryRelationsCoercion.lean` — exercises the registered coercion:
constructs a relation from a `CongruentBinaryPredicate`, uses it where a
`Set (U₁ ⧓ U₂)` is expected, and verifies the resulting membership reduces
(propositionally, via the pointwise equation) to the underlying binary
predicate application.

### Phase 2 — Migrate one operation at a time

For each operation in `Universals/Relations/Operations/` that produces or
consumes relations, create a parallel version under
`Universals/BinaryRelations/Operations/` that operates on the new
universal. Examples:

- `l2r_fiber` — was `Rel U₁ U₂ → U₁.Particular → Set U₂`. New version:
  `PrimRelation U₁ U₂ → U₁.Particular → Set U₂`. The implementation
  becomes: "the set of `b` such that `R.pred a b`" — direct, no existentials.
- `l2r_correspondence` — was `Rel U₁ U₂ → U₁ ⭢ᶜ U₂`. New version operates on
  binary relations.
- `co_classification` and friends — analogous.

For each migrated operation:
1. Implement the new version.
2. Write its `_def` characterization theorem.
3. Mark the def `@[irreducible]`.
4. Verify the operation typechecks and the characterization is provable.

### Phase 3 — Migrate proofs

For each proof in the framework that uses an operation on relations, port it
to use the new binary-relations version. Proofs should now go through:

- The `_def` characterization theorem of the operation, OR
- Direct `R.pred a b` lookups on the binary predicate.

No proof should reach through any operation's body. Where the old proof did
(via reduction), the new proof should use the characterization explicitly.

Particular attention:
- `co_classification_unfold` and `co_classification_cong` in
  `Universals/Correspondences/Operations/Unary/CoClassification/Operation.lean`
  — these should become substantially simpler in the new world (no existentials
  to unpack, no dyad-equality decomposition).
- Any proof that involved `uncurry_def`, `subsume_def` reductions through
  relation bodies — these go through the characterization theorems instead.

### Phase 4 — Switchover

Once all operations and proofs are migrated:

1. Rename `Universals/BinaryRelations/` to replace `Universals/Relations/`
   (or alternatively, keep both names and have `Relations` re-export from
   `BinaryRelations`).
2. Update any downstream code that imported from the old `Relations` namespace.
3. Remove the obsolete files (old `Relations/Operations/...` that have been
   replaced).
4. Run full build verification.

### Phase 5 — Cleanup

1. Remove dead code: the old `relation_from` construction, any unused
   `uncurry`-based proof machinery, the bridging theorems whose job is
   now done by the SubUniversal embedding.
2. Update `docs/design/relations.md` to reflect the new architecture.
3. Update `CLAUDE.md` and any per-universal skills to describe the bootstrap
   pattern uniformly.

## File-by-file change list

### New files (Phase 1)

| File | Purpose |
|---|---|
| `Universals/BinaryRelations/Particular.lean` | Reification: Particular = CongruentBinaryPredicate |
| `Universals/BinaryRelations/Universal.lean` | Universal with extensional equality |
| `Universals/BinaryRelations/Definitions/RelationFrom/Definition.lean` | Bootstrap reification (`@[reducible]`) |
| `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/Predicate.lean` | Dyad extension graph + `UnaryOperationGraph` bundle |
| `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/Properties/LeftTotality.lean` | Graph left-totality |
| `Universals/BinaryRelations/Predicates/Binary/DyadExtensionGraph/Properties/RightDeterminacy.lean` | Graph right-determinacy |
| `Universals/BinaryRelations/Operations/Unary/DyadExtension/Operation.lean` | `dyad_extension_sym` (axiom) + `dyad_extension_def` (axiom) + bundled `UnaryOperation` |
| `Universals/BinaryRelations/Operations/Unary/DyadExtension/Properties/Equations.lean` | Pointwise corollary `dyad_extension_mem` |
| `Universals/BinaryRelations/Properties/DyadExtensibility.lean` | `dyad_extensibility` instance: `Relation U₁ U₂ <: Set (U₁ ⧓ U₂)` |
| `Test/BinaryRelationsCoercion.lean` | Verify coercion works |

### Files to be migrated (Phase 2)

For each of the following, port to operate on `BinaryRelations.Particular`:

- `Universals/Relations/Operations/Unary/L2RFiber/Operation.lean`
- `Universals/Relations/Operations/Unary/R2LFiber/Operation.lean` (if exists)
- `Universals/Relations/Operations/Unary/L2RCorrespondence/Operation.lean`
- `Universals/Relations/Operations/Unary/R2LCorrespondence/Operation.lean` (if exists)
- `Universals/Relations/Predicates/Unary/*` (Symmetric, Transitive, Reflexive, PER, EquivalenceRelation, etc.)
- `Universals/Relations/Universals/*` (the universals defined as relations satisfying predicates)
- Any other operation in `Universals/Relations/Operations/`

### Files to be touched in dependents (Phase 3)

- `Universals/Correspondences/Operations/Unary/CoClassification/Operation.lean`
  — major simplification expected.
- `Universals/Correspondences/Predicates/Ternary/CoClassification/Predicate.lean` — adjust.
- Anywhere `Universals.Relations.Universal` is imported and `Rel` is used.

### Files to delete (Phase 4-5)

- The old `Universals/Relations/Particular.lean` (its content moves to
  `BinaryRelations`).
- Old `relation_from` definition and any proofs that depended on its
  existential body.
- Any `uncurry_def`-based bridge proofs that the SubUniversal embedding
  obviates.

## Verification at each step

- After Phase 1: `Test/BinaryRelationsCoercion.lean` compiles and
  demonstrates automatic coercion of a binary predicate (as a relation) into a
  set of dyads.
- After each Phase 2 migration: the migrated operation compiles, its `_def`
  theorem is proven, and an example using it works.
- After Phase 3: full `lake build` passes (modulo unrelated pre-existing
  errors). All proofs go through `_def` theorems, none through bodies.
- After Phase 4: old `Universals.Relations.*` removed; everything that used it
  now uses `BinaryRelations.*`.
- After Phase 5: documentation reflects new architecture.

## Risks and mitigations

| Risk | Mitigation |
|---|---|
| Breaking many proofs at once | Build new universal in parallel; migrate one operation at a time. |
| SubUniversal coercion not firing where expected | Phase 1 test verifies coercion before any migration begins. |
| Forgotten dependents | Phase 0 audit enumerates all operations and downstream uses. |
| Hidden definitional coupling elsewhere | Phase 3 proofs are required to use `_def` theorems explicitly; this surfaces hidden couplings as compile errors. |
| Loss of equational reasoning that was implicitly relying on bodies | Each `_def` theorem provides the propositional alternative; proofs translate cleanly when honest. |

## Open questions for during the refactor

1. **Namespace name**: `BinaryRelations`, `BinaryRelations`, or keep
   `Relations` and rename old to e.g. `LegacyRelations`? Decision to be made
   when Phase 4 (switchover) is reached.
2. **Reification primitive name**: `relation_from`, `bin_relation_from`, or
   directly `relation`? Parallel naming with `set_from` argues for
   `relation_from`. The old `relation_from` will be deleted, so the name is
   reusable.
3. **How many characterizations** does `dyad_extension` need? A
   minimal core is the pointwise one (`dyad_extension_mem`). Curried,
   uncurried, destructor-based variants can be added if downstream proofs
   benefit.

## Out of scope (follow-up work)

- Ternary and higher-arity primitive relations. Same pattern, same machinery,
  done as needed.
- Other "view as set" embeddings (e.g., function as relation, equivalence
  relation as partition). These follow the same SubUniversal pattern.
- A general `@[irreducible]` audit across the rest of the framework —
  separate piece of work, motivated by the same principle.

## Summary

This refactor isn't adding architecture. It's removing an incorrect
identification — that `Relation` is `Set of Dyads` — and restoring the
foundational parallelism that should always have been there: bootstrap
universals are reifications of n-ary predicates, one per arity, with the
inter-universal relationships expressed as registered SubUniversal embeddings.

The framework's principle of propositional-only reasoning, which has always
been the intent, becomes actually delivered: no proof depends on a `def`'s
body, because every defined object ships with the propositional
characterization it needs.

The cost is a substantial migration; the result is an architecture that
matches the math and a proof discipline that's enforceable rather than
aspirational.
