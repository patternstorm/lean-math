# Isomorphism Schema

## Motivation

Predicate associativity proves that `(a ⋈ b) ⋈ c` and `a ⋈ (b ⋈ c)` are predicatively indistinguishable — no predicate can tell them apart. The framework's philosophy says: equal means predicatively indistinguishable. But we can't state this equality because the terms live in different types (`((U₁ ⋈ U₂) ⋈ U₃).Particular` vs `(U₁ ⋈ (U₂ ⋈ U₃)).Particular`). Current equality (`=₍U₎`) only works within a single Universal.

**Goal**: Add a concept of cross-type equality between Universals — an Isomorphism schema.

## The Schema

```
structure Isomorphism (U₁: Universal) (U₂: Universal) where
  forward: CongruentUnaryOperation U₁ U₂
  backward: CongruentUnaryOperation U₂ U₁
  round_trip_forward: ∀ (x: U₁.Particular), backward.op (forward.op x) =₍U₁₎ x
  round_trip_backward: ∀ (y: U₂.Particular), forward.op (backward.op y) =₍U₂₎ y
```

Four fields: congruent forward/backward maps and round-trip proofs. Equality preservation is guaranteed by the `CongruentUnaryOperation` type — each bundles an `op` with a `cong` proof that `x₁ =₍U₁₎ x₂ → op x₁ =₍U₂₎ op x₂`. So forward and backward both respect equality by construction. Cross-type equality is a derived concept, not a primitive field — it is fully determined by the maps and the within-universal equalities.

## Properties

Given `iso: Isomorphism U₁ U₂`, the four fields yield all of the following. Nothing else needs to be added to the schema.

### Equality Preservation

The core property of the isomorphism. The maps preserve equality as a full biconditional:

- `x₁ =₍U₁₎ x₂ ↔ forward.op x₁ =₍U₂₎ forward.op x₂`
- `y₁ =₍U₂₎ y₂ ↔ backward.op y₁ =₍U₁₎ backward.op y₂`

The forward direction (congruence) is given by `CongruentUnaryOperation`. The backward direction (reflection) is derived: apply the inverse map to both sides (congruence), then use the round-trip + transitivity.

### Predicate Transport

Every predicate on one universal has a corresponding predicate on the other with the same extension. Given congruent `P` on U₁, construct congruent `P'` on U₂ via `P'(y) := P(backward.op y)`. Then `P'(forward.op x) ↔ P(x)` — the elements that satisfy P in U₁ correspond exactly to the elements that satisfy P' in U₂ via the forward/backward mapping. Symmetrically for the other direction.

This follows from equality preservation: since all predicates are congruent and the maps preserve equality, predicate transport is automatic.

The `CongruentPredicate` architecture stays unchanged — cross-universal congruence can't even be stated (a predicate on U₁ can't accept U₂-elements), so it's not an obligation. Instead, when a proof needs to apply a U₁-predicate to a U₂-element, it explicitly uses backward to bridge: write `P.pred (backward.op y)` instead of `P.pred y`. For example, given `P` on `(U₁ ⋈ U₂) ⋈ U₃` and `d : (U₁ ⋈ (U₂ ⋈ U₃)).Particular`, you can't write `P.pred d` (wrong type) — you write `P.pred (backward.op d)`. This is exactly what `reassoc` does in the predicate associativity proof.

**Why this move is justified**: `y` in U₂ cannot be classified differently than `backward.op y` in U₁ — every predicate satisfied by one has a corresponding predicate satisfied by the other. This is guaranteed by predicate transport, which follows from how we define the Isomorphism structure (round-trip + congruence).

### Cross-Type Equality Predicate

A separate predicate, defined outside the Isomorphism structure, that derives cross-type equality from any isomorphism. Following the framework's axiom + axiom_def pattern:

```
axiom eq (iso: Isomorphism U₁ U₂): U₁.Particular → U₂.Particular → Prop
axiom eq_def₁ (iso: Isomorphism U₁ U₂):
  ∀ (x: U₁.Particular), ∀ (y: U₂.Particular),
    eq iso x y ↔ x =₍U₁₎ iso.backward.op y
axiom eq_def₂ (iso: Isomorphism U₁ U₂):
  ∀ (x: U₁.Particular), ∀ (y: U₂.Particular),
    eq iso x y ↔ iso.forward.op x =₍U₂₎ y
```

The equality is not part of the isomorphism — it's derived from any isomorphism. `eq_def₁` unfolds it into U₁, `eq_def₂` unfolds it into U₂. In proofs, you pick whichever characterization matches the universal you're working in.

## Prerequisites: Dyad Projections

The Dyad ADT currently has exhaustiveness (`∀ d, ∃ a, ∃ b, d 🟰 (a ⋈ b)`) but no explicit projections. To construct the forward/backward maps for dyad reassociation, we need:

- `fst: (U₁ ⋈ U₂).Particular → U₁.Particular` with `fst_def: fst (a ⋈ b) =₍U₁₎ a`
- `snd: (U₁ ⋈ U₂).Particular → U₂.Particular` with `snd_def: snd (a ⋈ b) =₍U₂₎ b`

These are declared as operations following the standard ADT pattern (axiom + axiom_def + congruence + bundle).

## The Dyad Associativity Isomorphism

With projections, we can construct:

- **forward**: `((U₁ ⋈ U₂) ⋈ U₃).Particular → (U₁ ⋈ (U₂ ⋈ U₃)).Particular`
  - `d ↦ fst(fst d) ⋈ (snd(fst d) ⋈ snd d)`
- **backward**: `(U₁ ⋈ (U₂ ⋈ U₃)).Particular → ((U₁ ⋈ U₂) ⋈ U₃).Particular`
  - `d ↦ (fst d ⋈ fst(snd d)) ⋈ snd(snd d)`

Then: `Isomorphism ((U₁ ⋈ U₂) ⋈ U₃) (U₁ ⋈ (U₂ ⋈ U₃))` — dyad associativity as a cross-type equality.

## Relationship to Existing Predicate Associativity

The current `reassoc` + `predicate_associativity` proof in `Test/PredicateAssociativity.lean` works purely at the predicate level via uncurry. The Isomorphism schema works at the term level via forward/backward maps, with predicate transport derived for free from congruence. Both express the same mathematical fact from different angles.

## Implementation Plan

1. Add `fst`/`snd` projection operations to `Universals/Dyads/`
2. Add Isomorphism schema to `Logic/PredicateCalculus/Schemas/Isomorphism/Schema.lean`
3. Prove derived properties (predicate transport, equality reflection, cross-type equality properties)
4. Construct the dyad associativity isomorphism as the first instance

## Changes Made This Session

- **Notation refactoring** (from previous context): `⋈` now used for both `DyadUniversal` (between Universals) and `bind` (between Particulars), both at precedence 35, disambiguated by type.
- **Curry/uncurry axiom signatures**: Changed from named parameter style `(R: ...) :` to arrow style `: (...) →`, matching other operations. The `_def` axioms now use `∀ (R: ...)`.
- **Curry/uncurry comments**: Clarified that "saying something about a and b separately is the same as saying it about their dyad."
- **Predicate associativity proof**: Fixed term-mode `uncurry_def outer_R` to `by forall_elim uncurry_def, outer_R`. Added `(reassoc P)` parenthesization for clarity.
