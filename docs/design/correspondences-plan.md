# Correspondences: Properties, Operations, and Definitions

## Context

A correspondence `C: U₁ ⭢ᶜ U₂` is a **classification mapping** — it maps
classifications (sets) in one universal to classifications in another.

A particular of a correspondence is a set of arrows from individuals to
sets — arrows of type `U₁ ⭢ᵃ 𝐒𝐞𝐭 U₂`. This set of arrows IS the
**basis** of the correspondence: each arrow `a ⭢ᵃ T` records that source
particular `a` maps to class `T` in the target. The basis determines
everything — apply, domain, range, and co-classification all derive from it.

This basis creates a **base classification** on the range of the
correspondence, characterized by the co-classification relation: two
target particulars are co-classified iff they belong to the same class
in the basis.

The primary operation of a correspondence maps a source classification
to the corresponding target classification:

```
C(S) = { b : U₂ | ∃ a : U₁, a ∈ₛₑₜ S ∧ b ∈ₛₑₜ C a }
```

This set-to-set apply (Set U₁ → Set U₂) is the external behavior.
Querying with a singleton `{a}` recovers the element-level class `C(a)`.

### Why element-level, not set-of-sets?

A correspondence looks syntactically like a function `U₁ → Set U₂`,
which would suggest the image should be a set of sets (the collection
of classes). But correspondences are classification mappings, not
functions. The "output" of a correspondence is not "the value C(a)"
but "the particulars co-classified by a." A classification mapping
applied to a set of inputs produces a classification of outputs —
not a collection of classes, but a single classification.

This is confirmed by composition: for `C₂ ∘ C₁` to produce another
correspondence of the same kind (U₁ ⭢ᶜ U₃), the result must be a
set of elements, not a set of sets. And at the set level, composition
is simply function composition: `(C₂ ∘ C₁)(S) = C₂(C₁(S))`.

## Notation Convention

Sets can be treated as universals via `set_as_universal`
(see `Sets/Definitions/SetsAsTypes/Definition.lean`). With dot
notation (`S.Particular`), this allows quantifying over elements
of a set directly:

```
∀ a : S.Particular, P ↑a
```

instead of the FOL-style:

```
∀ a : U.Particular, a ∈ₛₑₜ S → P a
```

The `↑` coercion lifts a sub-universal element back to `U.Particular`
when needed (e.g., for predicates defined on U).

## Terminology

- **Source / Target**: The universals U₁ and U₂. Restriction happens
  at the type level (by constructing a correspondence over
  sub-universals).
- **Basis**: The set of arrows that constitutes the correspondence
  particular. Each arrow `a ⭢ᵃ T` maps a source particular to its
  class in the target.
- **Class**: The set `C({a})` — the target particulars co-classified
  by source particular `a`.
- **Base classification**: The classification on the range created by
  the basis, characterized by the co-classification relation.
- **Apply**: The classification mapping operator. Given a classification
  S : Set U₁, produces the classification of all target particulars
  co-classified by any source particular in S.
- **Domain**: The set of source particulars whose class is non-empty.
- **Range**: The set of target particulars co-classified by at least
  one source particular — the part of the target on which the base
  classification lives.
## Definitions

### Apply (set-level)

The classification mapping: given a source classification, produce the
corresponding target classification.

```
apply C S = { b : U₂ | ∃ a : U₁, a ∈ₛₑₜ S ∧ b ∈ₛₑₜ C a }
```

Takes `C : Corr U₁ U₂` and `S : Set U₁`, returns `Set U₂`.

The element-level class `C(a)` is the special case of applying to
a singleton `{a}ₛₑₜ`.

### Domain

The set of source particulars whose class is non-empty:

```
domain C = { a : U₁ | ∃ b : U₂, b ∈ₛₑₜ C a }
```

Lives in `Set U₁`.

### Range

The set of target particulars co-classified by at least one source particular:

```
range C = { b : U₂ | ∃ a : U₁, b ∈ₛₑₜ C a }
```

Lives in `Set U₂`. (Theorem: `range C =ₛₑₜ apply C (universal_set U₁)`.)

### Total

A correspondence is **total** if every source particular has a non-empty class:

```
total C ↔ ∀ a : U₁.Particular, a ∈ₛₑₜ domain C
```

Equivalently: `∀ a : U₁.Particular, ∃ b : U₂.Particular, b ∈ₛₑₜ C a`.

A correspondence that is not total is **partial** — some source
particulars have empty classes.

### Surjective

Every target element is in the range:

```
surjective C ↔ ∀ b : U₂.Particular, b ∈ₛₑₜ range C
```

(Theorem: `surjective C ↔ range C =ₛₑₜ universal_set U₂`.)

### Co-Classification Relation (induced by a correspondence)

A correspondence `C: U₁ ⭢ᶜ U₂` induces a binary relation **on its
range**: two target particulars are **co-classified** iff they belong
to the same class in the basis — some source particular co-classifies
both.

```
co_classification C : Rel (range C : Universal) (range C : Universal)

(co_classification C).pred (b₁ ⋈ b₂)  ↔  ∃ a : U₁.Particular, ↑b₁ ∈ₛₑₜ C(↑{a}ₛₑₜ) ∧ ↑b₂ ∈ₛₑₜ C(↑{a}ₛₑₜ)
```

where `b₁ b₂ : (range C).Particular` and `↑b₁, ↑b₂ : U₂.Particular`.

The relation lives on the range — the part of the target universal on
which the base classification lives. This is the correct type: the
co-classification relation is inherently about elements that are
co-classified by some source particular, i.e. elements in the range.

This relation is always **reflexive** and always **symmetric**.
However, it is **not always transitive**. Transitivity fails when
classes overlap without being identical: if `b₁` is co-classified by
`a₁`, and `b₂` is co-classified by both `a₁` and `a₂`, and `b₃` is
co-classified only by `a₂`, then `b₁ ~_C b₂` and `b₂ ~_C b₃` but not
`b₁ ~_C b₃`.

**Implementation note**: The `Set → Universal` coercion (via `CoeDep`)
allows writing `(range C : Universal)` instead of
`set_as_universal (range C)`. See
`Sets/Definitions/SetsAsUniversals/Definition.lean`.

The ternary predicate layers (`co_classified_with`, `co_classified_by`,
`co_classification_predicate`) remain defined on U₂ — they capture
the *condition* for co-classification. The operation
`co_classification` wraps this condition as a relation on the range.

### Injective

A correspondence is **injective** iff its co-classification relation is an
equivalence relation.

```
injective C ↔ is_equivalence_relation (co_classification C)
```

This is now well-typed: `co_classification C` is a
`Rel (range C : Universal) (range C : Universal)`, so
`is_equivalence_relation` unfolds with `is_reflexive` quantifying
over `(range C).Particular` — exactly reflexivity on the range, which
is always satisfied.

Ontologically, an injective correspondence partitions its range into
equivalence classes, each indexed by a domain element. The classes
`C(a)` *are* the equivalence classes. Pairwise disjointness of
classes — the classical formulation — is a *consequence* of this
partition structure, not the definition.

**Note for proofs**: Since reflexivity and symmetry are always
satisfied, the only condition that can fail is transitivity. So in
practice, proving injectivity reduces to proving transitivity of the
co-classification relation.

**Theorem (pairwise disjointness follows)**: If C is injective, then
for all `a₁ a₂` in the domain, if `apply C (↑{a₁}ₛₑₜ)` and
`apply C (↑{a₂}ₛₑₜ)` share any element, then `a₁ =₍U₁₎ a₂`.

The same theorems hold:

1. **Composition**: injective C₁ ∧ injective C₂ → injective (C₂ ∘ C₁)
2. **Left-inverse**: C is injective ↔ ∃ C⁻¹, C⁻¹ ∘ C is the partial
   identity on domain(C)
3. **Cancellation (monomorphism)**: injective C → (C ∘ F =ₛₑₜ C ∘ G
   on domain(C) → F = G on relevant parts)
4. **Distributive law**: injective C → apply C (S₁ ∩ S₂) =ₛₑₜ
   apply C S₁ ∩ apply C S₂
5. **Inverse-image equivalence**: for injective C, direct image of the
   relational inverse equals the pre-image
6. **Idempotent round-trip**: C⁻¹ ∘ C is idempotent (projection onto
   domain)

### Inverse

Given `C : Corr U₁ U₂`, the inverse `C⁻¹ : Corr U₂ U₁` is defined by:

```
C⁻¹(b) = { a : U₁ | b ∈ₛₑₜ C a }
```

(Theorem: for a correspondence arising from a relation R,
`inverse(l2r R) =ₛₑₜ r2l R`.)

### Bijective

A correspondence is **bijective** if it is total, injective, and
surjective.

### Functional

A correspondence is **functional** if singleton inputs produce
singleton outputs:

```
functional C ↔ ∀ a : (domain C).Particular,
               ∃! b : U₂.Particular, C(↑a) =ₛₑₜ {b}
```

When C is functional, it is isomorphic to a function U₁ → U₂ (on the
domain). A bijective functional correspondence is a bijective function.

### Composition

Given `C₁: U₁ ⭢ᶜ U₂` and `C₂: U₂ ⭢ᶜ U₃`, their composition at
the set level is function composition:

```
(C₂ ∘ C₁)(S) = C₂(C₁(S))
```

At the element level, the class of `a` under `C₂ ∘ C₁` is:

```
(C₂ ∘ C₁)(a) = { c : U₃ | ∃ b : U₂, b ∈ₛₑₜ C₁ a ∧ c ∈ₛₑₜ C₂ b }
```

Composition is associative — it is function composition at the set
level, which is inherently associative.

Composition needs to be shown congruent in both arguments (C₁ and C₂).

## Implementation Order

0. **S.Particular dot notation + Set → Universal coercion** —
   `Sets/Definitions/SetsAsUniversals/Definition.lean`. **Implemented.**
   `Set.Particular` for the type, `CoeDep` coercion so `(S : Universal)`
   works wherever a Universal is expected.
1. **Apply** (modify to set-level) — new definition + congruence. **Implemented.**
   `apply : Corr U₁ U₂ → Set U₁ → Set U₂` with `apply_def` using arrows directly.
   No element-level operation — element-level class recovered via `apply C (↑{a}ₛₑₜ)`.
   Congruence in both arguments. Functional predicate updated accordingly.
2. **Domain** — definition + congruence. **Implemented.**
   `domain C = { a : U₁ | ∃ b, b ∈ₛₑₜ apply C (↑{a}ₛₑₜ) }`.
   Functional predicate updated to quantify over domain elements.
3. **Range** — definition + congruence. **Implemented.**
   `range C = { b : U₂ | ∃ a, b ∈ₛₑₜ apply C (↑{a}ₛₑₜ) }`.
4. **Total** — predicate definition. **Implemented.**
   `is_total C ↔ ∀ a, a ∈ₛₑₜ domain C`. Congruence via `domain_cong`.
5. **Surjective** — predicate definition. **Implemented.**
   `is_surjective C ↔ ∀ b, b ∈ₛₑₜ range C`. Congruence via `range_cong`.
6. **Co-classification ternary predicate** — three-layer predicate on U₂.
   **Implemented.** `co_classified_with`, `co_classified_by`,
   `co_classification_predicate`.
7. **Co-classification operation** — **refactoring in progress.**
   Current signature returns `Rel U₂ U₂`. Must be changed to return
   `Rel (range C : Universal) (range C : Universal)` — the relation
   lives on the range, not on the whole target. This is required for
   injectivity to be well-typed (`is_equivalence_relation` uses
   `is_reflexive`, which quantifies over all particulars of the
   relation's universal — so the universal must be the range).
   Properties: reflexivity (proved), symmetry (proved), both need
   updating after the signature change.
8. **Equivalence relation predicates** (in Relations). **Implemented.**
   `is_reflexive`, `is_symmetric`, `is_transitive`,
   `is_equivalence_relation` with congruence proofs.
9. **Injective** — co-classification is an equivalence relation
10. **Inverse** — definition + congruence + theorem (inverse = dual)
11. **Bijective** — conjunction of total + injective + surjective
12. **Functional** — predicate definition (singleton → singleton)
13. **Composition** — definition + congruence proofs. **Implemented.**
    `compose C₂ C₁` with `compose_def` characterizing arrow membership:
    `(a ⭢ᵃ W) ∈ₛₑₜ (compose C₂ C₁) ↔ W =ₛₑₜ apply C₂ (apply C₁ (↑{a}ₛₑₜ))`.
    Congruence in both arguments via `apply_cong_first` + `apply_cong_second`.
    Binary operation wrapper `compose_operation`.

## Equivalence Relation Predicates (Relations)

Prerequisite for the structural definition of correspondence
injectivity. These predicates only apply to **endo-relations**
(`Rel U U`) — relations where source and target are the same
universal.

### Definitions

All three properties are predicates on `Rel U U`, defined via dyad
membership. Given `R: Rel U U`:

**Reflexive**:
```
is_reflexive R ↔ ∀ a : U.Particular, (a ⋈ a) ∈ₛₑₜ R
```

**Symmetric**:
```
is_symmetric R ↔ ∀ a b : U.Particular, (a ⋈ b) ∈ₛₑₜ R → (b ⋈ a) ∈ₛₑₜ R
```

**Transitive**:
```
is_transitive R ↔ ∀ a b c : U.Particular,
  (a ⋈ b) ∈ₛₑₜ R → (b ⋈ c) ∈ₛₑₜ R → (a ⋈ c) ∈ₛₑₜ R
```

**Equivalence relation**:
```
is_equivalence_relation R ↔ is_reflexive R ∧ is_symmetric R ∧ is_transitive R
```

### Congruence

Each predicate must be shown congruent: if `R₁ =ᵣₑₗ R₂` (set
equality of dyad sets), then `is_P R₁ ↔ is_P R₂`. This follows
from set extensionality — equal relations have identical dyad
membership, so all membership-based properties transfer.

### File Organization

```
Universals/Relations/
├── Predicates/
│   └── Unary/
│       ├── Reflexive/Predicate.lean
│       ├── Symmetric/Predicate.lean
│       ├── Transitive/Predicate.lean
│       └── EquivalenceRelation/Predicate.lean
│   └── Unary.lean            (barrel)
├── Predicates.lean            (barrel)
```

### Implementation Order

1. **Reflexive** — simplest; one universal quantifier
2. **Symmetric** — two quantifiers + implication
3. **Transitive** — three quantifiers + two implications
4. **Equivalence relation** — conjunction of the three; congruence
   follows from the congruence of each component

## Existing Infrastructure

- **Singleton sets**: `singleton_of : U.Particular → SingletonSet U`
  with notation `{x}ₛₑₜ` and defining axiom
  `y ∈ₛₑₜ ↑{x}ₛₑₜ ↔ y =₍U₎ x`. Already a congruent operation.
  (See `Sets/Universals/Singleton/`)

## Theorems

### 0. Apply preserves empty set

`apply C ∅ =ₛₑₜ ∅` — the image of the empty set is the empty set.

### 1. Composition preserves injectivity

If `C₁: U₁ ⭢ᶜ U₂` and `C₂: U₂ ⭢ᶜ U₃` are both injective on their
respective domains, then `C₂ ∘ C₁` is injective on its domain.

### 2. Left-inverse (retraction)

`C: U₁ ⭢ᶜ U₂` is injective if and only if there exists a
correspondence `C⁻¹: U₂ ⭢ᶜ U₁` such that `C⁻¹ ∘ C` is the partial
identity on the domain of C.

Partial identity: `(C⁻¹ ∘ C)(a) =ₛₑₜ {a}ₛₑₜ` for all
`a : (domain C).Particular`.

### 3. Cancellation law (monomorphism)

If `C: U₁ ⭢ᶜ U₂` is injective, then for any two correspondences
`F, G: U₀ ⭢ᶜ U₁`, if `C ∘ F = C ∘ G`, then F and G are identical on
the parts of their range that fall within the domain of C.

### 4. Distributive law over set intersection

If `C: U₁ ⭢ᶜ U₂` is injective, then it preserves set intersections:

```
apply C (S₁ ∩ S₂) =ₛₑₜ apply C S₁ ∩ apply C S₂
```

for all `S₁ S₂ : Set U₁`. (Non-injective correspondences only satisfy
`apply C (S₁ ∩ S₂) ⊆ₛₑₜ apply C S₁ ∩ apply C S₂`.)

### 5. Inverse-image equivalence

For an injective correspondence C, the direct image of the relational
inverse equals the pre-image in the functional sense.

### 6. Idempotent round-trip

The round-trip `C⁻¹ ∘ C` is an idempotent correspondence:
`(C⁻¹ ∘ C) ∘ (C⁻¹ ∘ C) = C⁻¹ ∘ C`. This confirms the correspondence
acts as a projection onto its own domain.
