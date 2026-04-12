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

A correspondence `C: U₁ ⭢ᶜ U₂` induces a binary relation on the
target universal U₂: two target particulars are **co-classified** iff
a **unique** source particular co-classifies both.

```
co_classification C : Rel U₂ U₂

(co_classification C).pred (b₁ ⋈ b₂)  ↔  ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C(↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C(↑{a}ₛₑₜ)
```

The `∃!` (unique existence) is essential. With plain `∃`, the relation
would be reflexive on the entire range and always an equivalence
relation — making injectivity trivial. With `∃!`, co-classification
encodes that `b₁` and `b₂` belong to the **same class and no other**.
This is the correct semantics: co-classification means belonging to
exactly one shared class.

The relation lives on U₂ (not on the range sub-universal). This avoids
dependent type complications — see the Injectivity section below.

This relation is always **symmetric** (swap the conjuncts under the
same unique witness). It is **not reflexive in general**: `b ⋈ b`
requires a unique `a` with `b ∈ C({a})`, which fails if `b` belongs
to multiple classes. It is **not transitive in general**: transitivity
fails when classes overlap without being identical.

The ternary predicate layers (`co_classified_with`, `co_classified_by`,
`co_classification_predicate`) capture the condition on U₂. The
operation `co_classification` wraps this as a `Rel U₂ U₂` via
`relation_from`, with a defining axiom and bridge theorem
`co_classification_unfold`.

### Injective

**Core insight**: A correspondence is injective when its base
classification on the range is proper — each target particular belongs
to exactly one class. In other words, co-classification is an
equivalence relation on the range.

#### The problem: expressing "equivalence relation on the range"

The natural definition is:

```
injective C ↔ is_equivalence_relation_on (co_classification C) (range C)
```

where `is_equivalence_relation_on R S` means R is an equivalence
relation when restricted to elements of S. But expressing this
cleanly in the framework has proven non-trivial.

#### Why PER alone is too weak

The initial attempt defined injectivity as "co-classification is a
partial equivalence relation (symmetric + transitive)." This is
**wrong** — an empty relation is vacuously a PER:

> Counterexample: `C({a₁}) = {b₁}, C({a₂}) = {b₁}, C({a₃}) = {b₂}`.
> The co-classification relation (with `∃!`) relates nothing — every
> pair fails uniqueness since `b₁` belongs to both `C({a₁})` and
> `C({a₂})`. The empty relation is a PER, yet classes are not disjoint.

Adding "non-empty" doesn't help either:

> Counterexample: `C({a₁}) = {b₁, b₂}, C({a₂}) = {b₁, b₃}`.
> Co-classification relates `(b₁, b₂)` uniquely via `a₁` and
> `(b₁, b₃)` uniquely via `a₂`. The relation is non-empty and a PER
> (symmetric, vacuously transitive). But `b₁` is in two classes.

#### Equivalent correct definitions

Three equivalent formulations, all correct:

1. **Pairwise disjoint classes**:
   ```
   ∀ a₁ a₂ : U₁, ∀ b : U₂, b ∈ₛₑₜ C({a₁}) → b ∈ₛₑₜ C({a₂}) → a₁ =₍U₁₎ a₂
   ```

2. **Reflexive on range** (co-classification is reflexive on range):
   ```
   ∀ b : U₂, b ∈ₛₑₜ range C → (co_classification C).pred (b ⋈ b)
   ```
   This requires that every element in the range belongs to exactly
   one class (the uniqueness in `∃!` is what makes reflexivity
   non-trivial).

3. **Equivalence relation on range**: co-classification restricted to
   `range C` is reflexive, symmetric, and transitive.

**Key theorem**: Reflexive on range alone implies transitivity (and
hence full equivalence on range), because: given `b₁ ~ b₂` and
`b₂ ~ b₃`, the unique witnesses must be equal (both are the unique
source for `b₂`), giving `b₁ ~ b₃` via the shared witness.

#### Solution: Restriction + sub-universal quantifier bridge

**Sub-universal subtyping principle**: If `V = set_as_universal S`
(V <: U), then `V.Particular` embeds into `U.Particular` via `.val`.
This embedding extends to compound structures: `Rel V V` embeds into
`Rel U U` because any statement about V-elements can be expressed as
a guarded statement about U-elements. When output types depend on an
input (as with restriction), congruence is expressed by comparing at
the parent-universal level.

**Sub-universal quantifier bridge** (verified in
`Test/SubUniversalBridge.lean`):

```
(∀ v : V.Particular, P v.val) ↔ (∀ x : U.Particular, x ∈ₛₑₜ S → P x)
```

Proved using element-level coercion (`v.val : U.Particular`) and
subtype construction (`⟨x, h⟩ : V.Particular`), with `mem_def`
bridging `∈ₛₑₜ` to `S.pred`. No `propext`, no `funext`, no Lean `=`.
Stays within first-order logic.

**Restriction operation**: Given `R : Rel U U` and `S : Set U`,
restriction produces `Rel V V` where `V = set_as_universal S`:

```
(restrict R S).pred (v₁ ⋈ v₂) ↔ R.pred (v₁.val ⋈ v₂.val)
```

Constructed via `relation_from` with binary predicate
`fun v₁ v₂ => R.pred (v₁.val ⋈ v₂.val)` — no new axioms needed.

**Congruence of `restrict`** in both R and S. The output type
`Rel V V` depends on S, but `Rel V V <: Rel U U` — so when S varies,
congruence is expressed at the parent level:

```
R₁ =ᵣₑₗ R₂ → S₁ =ₛₑₜ S₂ →
  ∀ x y : U.Particular, x ∈ₛₑₜ S₁ → y ∈ₛₑₜ S₁ →
    (restrict R₁ S₁).pred (⟨x, _⟩ ⋈ ⟨y, _⟩) ↔
    (restrict R₂ S₂).pred (⟨x, _⟩ ⋈ ⟨y, _⟩)
```

This unfolds to `R₁.pred (x ⋈ y) ↔ R₂.pred (x ⋈ y)`, which follows
directly from `R₁ =ᵣₑₗ R₂`. The dependent type dissolves when
comparing through the parent universal.

**Injectivity definition**:

```
is_injective C ↔ is_equivalence_relation (restrict (co_classification C) (range C))
```

Reads transparently: co-classification restricted to the range is an
equivalence relation. The `is_reflexive` component quantifies over
`(range C).Particular` — exactly the range elements.

**Congruence of `is_injective`**: Uses the bridge to unfold past the
dependent type, then compares at the parent-universal level:

```
is_injective C₁
↔ is_equivalence_relation (restrict (co_classification C₁) (range C₁))
↔ ∀ x : U₂, x ∈ₛₑₜ range C₁ → (co_classification C₁).pred (x ⋈ x) ∧ ...
                                                    [bridge for range C₁]
↔ ∀ x : U₂, x ∈ₛₑₜ range C₂ → (co_classification C₂).pred (x ⋈ x) ∧ ...
                                   [range_cong + co_classification_cong]
↔ is_equivalence_relation (restrict (co_classification C₂) (range C₂))
                                                    [bridge for range C₂]
↔ is_injective C₂
```

Each bridge application works for a fixed S. The comparison happens
at U₂ where `=ᵣₑₗ` and `=ₛₑₜ` work normally.

#### Current implementation (stale, needs update)

The file `Predicates/Unary/Injective/Predicate.lean` currently uses the
PER-based definition. Must be updated to use restriction + equivalence
relation.

#### Expected theorems

1. **Pairwise disjointness**: injective ↔ classes are pairwise disjoint
2. **Composition**: injective C₁ ∧ injective C₂ → injective (C₂ ∘ C₁)
3. **Left-inverse**: C is injective ↔ ∃ C⁻¹, C⁻¹ ∘ C is the partial
   identity on domain(C)
4. **Cancellation (monomorphism)**: injective C → (C ∘ F =ₛₑₜ C ∘ G
   on domain(C) → F = G on relevant parts)
5. **Distributive law**: injective C → apply C (S₁ ∩ S₂) =ₛₑₜ
   apply C S₁ ∩ apply C S₂
6. **Inverse-image equivalence**: for injective C, direct image of the
   relational inverse equals the pre-image
7. **Idempotent round-trip**: C⁻¹ ∘ C is idempotent (projection onto
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
7. **Co-classification operation** — **Implemented.**
   Signature: `(C: U₁ ⭢ᶜ U₂) → Rel U₂ U₂` (lives on U₂, not range).
   Uses `∃!₍U₁₎` (unique existence). Constructed via `relation_from`
   with axiom + defining equality. Wrapped as `CongruentUnaryOperation`.
   Bridge theorem `co_classification_unfold` recovers pointwise iff.
   Properties: symmetry (proved). Reflexivity deleted (no longer holds
   in general with `∃!` — requires injectivity).
8. **Equivalence relation predicates** (in Relations). **Implemented.**
   `is_reflexive`, `is_symmetric`, `is_transitive`,
   `is_equivalence_relation` with congruence proofs.
9. **Injective** — co-classification is an equivalence relation on range.
   **In progress.** Definition approach undecided — see Injectivity section.
   Current PER-based definition in code is stale.
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
