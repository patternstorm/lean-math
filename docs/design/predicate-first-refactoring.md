# Predicate-First Axiomatic Definitions: Refactoring Plan

## Problem

Operations returning Sets or Relations are currently defined with
membership-based axioms — the defining axiom characterizes what
elements belong to the result, but never constructs the actual
congruent predicate underlying the result. The axiom describes
the object's behaviour without providing the object itself.

For example, the domain operation's axiom says:

```
axiom domain_def: ∀ C, ∀ a, a ∈ₛₑₜ domain C ↔ ∃ b, b ∈ₛₑₜ C (↑{a}ₛₑₜ)
```

This tells us *what* is in the domain, but the congruent predicate
`a ↦ ∃ b, b ∈ₛₑₜ C (↑{a}ₛₑₜ)` — the real object — is never
explicitly constructed or equated to. The congruence proof for
the operation is then proved ad hoc, re-deriving from membership
what should have been immediate from the predicate's own congruence.

## Solution

The **predicate-first** (or **new**) pattern, already used by
co-classification and l2r_fiber, works as follows:

1. **Prove predicate congruence** — prove that the predicate
   underlying the result respects the relevant equality.

2. **Construct the object** — build the result (set, relation,
   correspondence) from that predicate.

3. **Axiom via equality** — the defining axiom equates the
   operation's result to the constructed object using the
   appropriate equality (`=ₛₑₜ`, `=ᵣₑₗ`, `=→ᶜ`).

4. **Bridge theorem** — recover the pointwise membership form
   as a theorem derived from the equality axiom. This preserves
   the useful old characterization while grounding it in the
   real object.

### Construction approach

Every operation gets its predicate defined as a first-class
`CongruentUnaryPredicate` (or Binary) in a separate **Predicate.lean**
file under the appropriate Predicates folder, mirroring the operation's
location in the project tree. This applies to all operations regardless
of predicate complexity — consistency over minimalism. A reader should
always find the predicate in the same place.

In **Operation.lean**, the equality axiom uses **set comprehension**
referencing the predicate's `.cong`:

```lean
-- Predicate.lean: defines the congruent predicate
def <op>_predicate (...): CongruentUnaryPredicate U :=
  { pred := (x: U.Particular ↦ ...), cong := <proof> }

-- Operation.lean: equality axiom via set comprehension
axiom <op>_def: ∀ ...,
  <op> ... =ₛₑₜ { x : T | (<op>_predicate ...).pred x } with (<op>_predicate ...).cong
```

Always use set comprehension notation — never `set_from` directly.

The heavier approach — using `relation_from` with `uncurry` — is
only needed when the result is a Relation (e.g. co-classification).
For Sets (which covers all 9 operations in this refactoring), always
use set comprehension.

### Example: L2R Fiber (already in new pattern, set comprehension)

```lean
-- Congruence for the predicate (inline)
theorem l2r_fiber_pred_cong (R: Rel U₁ U₂) (a: U₁.Particular) :
  ∀ x y, x =₍U₂₎ y → (R.pred (a ⋈ x) ↔ R.pred (a ⋈ y)) := ...

-- Axiom: equality to constructed set via comprehension
axiom l2r_fiber_def: ∀ R, ∀ a,
  l2r_fiber R a =ₛₑₜ { y : U₂ | R.pred (a ⋈ y) } with l2r_fiber_pred_cong R a
```

### Example: Co-Classification (already in new pattern, separate predicate)

This uses the heavier approach because the predicate is ternary
and the result is a Relation (requiring `relation_from` + `uncurry`):

```lean
-- Predicate defined in Predicate.lean (three layers)
noncomputable def co_classified_by (C): CongruentBinaryPredicate U₂ U₂ := ...

-- Constructed object
noncomputable def co_classification_rel (C): Rel U₂ U₂ :=
  relation_from (co_classified_by C)

-- Axiom: equality to constructed relation
axiom co_classification_def: ∀ C, co_classification C =ᵣₑₗ co_classification_rel C

-- Bridge: recovers pointwise form
theorem co_classification_unfold: ∀ C, ∀ b₁, ∀ b₂,
  (co_classification C).pred (b₁ ⋈ b₂) ↔ ∃ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := ...
```

## Identification Criterion

An operation needs refactoring if its defining axiom returns a set
and the axiom does **not** use equality (`=ₛₑₜ`, `=ᵣₑₗ`, `=→ᶜ`)
with a set comprehension (or `relation_from`) on the RHS. If the
axiom instead characterizes the result via `∈ₛₑₜ` or `.pred`, the
underlying congruent predicate is never constructed, and the
congruence proof for the operation is missing.

## Classification of All Operations

### Already correct — no changes needed

| Operation | File | Pattern used |
|-----------|------|-------------|
| L2R Fiber | `Relations/Operations/Unary/L2RFiber/Operation.lean` | `=ₛₑₜ` with set comprehension |
| R2L Fiber | `Relations/Operations/Unary/R2LFiber/Operation.lean` | `=ₛₑₜ` with set comprehension |
| Co-Classification | `Correspondences/Operations/Unary/CoClassification/Operation.lean` | `=ᵣₑₗ` with `relation_from` |

### Already using set comprehension — no changes needed

| Operation | File | How defined |
|-----------|------|-------------|
| Empty Set | `Sets/Operations/Constants/EmptySet/Constant.lean` | `{ x | False } with (false U).cong` |
| Universal Set | `Sets/Operations/Constants/UniversalSet/Constant.lean` | `{ x | True } with (true U).cong` |

### Need refactoring — 9 operations

| # | Operation | File | Current axiom form |
|---|-----------|------|--------------------|
| 1 | SingletonOf | `Sets/Universals/Singleton/Operations/Unary/SingletonOf/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 2 | Powerset | `Sets/Operations/Unary/Powerset/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 3 | Union | `Sets/Operations/Binary/Union/Operation.lean` | `.pred` / `↔` |
| 4 | Apply | `Correspondences/Operations/Unary/Application/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 5 | Domain | `Correspondences/Operations/Unary/Domain/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 6 | Range | `Correspondences/Operations/Unary/Range/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 7 | L2R Correspondence | `Relations/Operations/Unary/L2RCorrespondence/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 8 | R2L Correspondence | `Relations/Operations/Unary/R2LCorrespondence/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 9 | Compose | `Correspondences/Operations/Binary/Composition/Operation.lean` | `∈ₛₑₜ` / `↔` |

## Per-Operation Sketches

### 1. SingletonOf

**Current**:
```lean
axiom singleton_of_def: ∀ x, ∀ y, y ∈ₛₑₜ ↑{x}ₛₑₜ ↔ y =₍U₎ x
```

**New**:
- Prove `singleton_pred_cong x`: `∀ y₁ y₂, y₁ =₍U₎ y₂ → (y₁ =₍U₎ x ↔ y₂ =₍U₎ x)`.
  Uses `U.eq.sym` and `U.eq.trans`.
- Construct: `noncomputable def singleton_set (x: U.Particular): Set U :=`
  `{ y : U.Particular | y =₍U₎ x } with singleton_pred_cong x`
  (Note: needs to be cast/coerced to `SingletonSet U` if the type requires it,
  or the axiom type may need adjusting.)
- New axiom: `axiom singleton_of_def: ∀ x, ↑{x}ₛₑₜ =ₛₑₜ singleton_set x`
- Bridge: `theorem singleton_of_unfold: ∀ x, ∀ y, y ∈ₛₑₜ ↑{x}ₛₑₜ ↔ y =₍U₎ x`

**Downstream**: Heavily used — domain_def, range_def, co-classification
all reference singletons. The bridge theorem preserves the interface.

### 2. Powerset

**Current**:
```lean
axiom powerset_def: ∀ S, ∀ S', S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S
```

**New**:
- The predicate `S' ↦ S' ⊆ₛₑₜ S` already has congruence via `supersets_of`.
  Specifically, `(supersets_of S').cong` provides
  `∀ S₁ S₂, S₁ =ₛₑₜ S₂ → (... ⊆ S₁ ↔ ... ⊆ S₂)` — but we need
  congruence in the *predicate variable* (the thing being tested for
  membership), not the parameter. So the congruence we need is:
  `∀ S'₁ S'₂, S'₁ =ₛₑₜ S'₂ → (S'₁ ⊆ₛₑₜ S ↔ S'₂ ⊆ₛₑₜ S)`.
  This is `(subsets_of S).cong` if it exists, or needs proving.
- Construct: `noncomputable def powerset_set (S: Set U): Set (𝐒𝐞𝐭 U) :=`
  `{ S' : (𝐒𝐞𝐭 U).Particular | S' ⊆ₛₑₜ S } with powerset_pred_cong S`
- New axiom: `axiom powerset_def: ∀ S, (𝒫 S) =ₛₑₜ powerset_set S`
- Bridge: `theorem powerset_unfold: ∀ S, ∀ S', S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S`

### 3. Union

**Current**:
```lean
axiom union_def: ∀ A, ∀ B, ∀ x, (A ∪ₛₑₜ B).pred x ↔ A.pred x ∨ B.pred x
```

**New**:
- Prove `union_pred_cong A B`: `∀ x y, x =₍U₎ y → (A.pred x ∨ B.pred x ↔ A.pred y ∨ B.pred y)`.
  Uses `A.cong` and `B.cong`.
- Construct: `noncomputable def union_set (A: Set U) (B: Set U): Set U :=`
  `{ x : U.Particular | A.pred x ∨ B.pred x } with union_pred_cong A B`
- New axiom: `axiom union_def: ∀ A, ∀ B, (A ∪ₛₑₜ B) =ₛₑₜ union_set A B`
- Bridge: `theorem union_unfold: ∀ A, ∀ B, ∀ x, (A ∪ₛₑₜ B).pred x ↔ A.pred x ∨ B.pred x`

### 4. Apply

**Current**:
```lean
axiom apply_def: ∀ C, ∀ S, ∀ b,
  b ∈ₛₑₜ (C S) ↔ ∃ a, a ∈ₛₑₜ S ∧ ∃ T, (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T
```

**New**:
- Prove `apply_pred_cong C S`: congruence of
  `b ↦ ∃ a, a ∈ₛₑₜ S ∧ ∃ T, (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T` in `b`.
  The key step: when `b₁ =₍U₂₎ b₂`, transfer `b ∈ₛₑₜ T` via `T.cong`.
- Construct: `noncomputable def apply_set (C: U₁ ⭢ᶜ U₂) (S: Set U₁): Set U₂ :=`
  `{ b : U₂.Particular | ∃ a, a ∈ₛₑₜ S ∧ ∃ T, (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T } with apply_pred_cong C S`
- New axiom: `axiom apply_def: ∀ C, ∀ S, C S =ₛₑₜ apply_set C S`
- Bridge: `theorem apply_unfold: ∀ C, ∀ S, ∀ b, b ∈ₛₑₜ (C S) ↔ ∃ a, a ∈ₛₑₜ S ∧ ∃ T, (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T`
- Update: `apply_cong_first`, `apply_cong_second`, `apply_with`, `apply_operation`

**Downstream**: This is the most impactful refactoring — `apply_cong_first`
and `apply_cong_second` are used by Domain, Range, Compose, CoClassification
predicate, and Functional predicate. The bridge theorem preserves the interface.

### 5. Domain

**Current**:
```lean
axiom domain_def: ∀ C, ∀ a, a ∈ₛₑₜ domain C ↔ ∃ b, b ∈ₛₑₜ C (↑{a}ₛₑₜ)
```

**New**:
- Prove `domain_pred_cong C`: congruence of
  `a ↦ ∃ b, b ∈ₛₑₜ C (↑{a}ₛₑₜ)` in `a`.
  Key steps: `a₁ =₍U₁₎ a₂` → `↑{a₁}ₛₑₜ =ₛₑₜ ↑{a₂}ₛₑₜ` (singleton congruence)
  → `C (↑{a₁}ₛₑₜ) =ₛₑₜ C (↑{a₂}ₛₑₜ)` (apply_cong_second) → membership transfer.
- Construct: `noncomputable def domain_set (C: U₁ ⭢ᶜ U₂): Set U₁ :=`
  `{ a : U₁.Particular | ∃ b, b ∈ₛₑₜ C (↑{a}ₛₑₜ) } with domain_pred_cong C`
- New axiom: `axiom domain_def: ∀ C, domain C =ₛₑₜ domain_set C`
- Bridge: `theorem domain_unfold: ∀ C, ∀ a, a ∈ₛₑₜ domain C ↔ ∃ b, b ∈ₛₑₜ C (↑{a}ₛₑₜ)`

### 6. Range

**Current**:
```lean
axiom range_def: ∀ C, ∀ b, b ∈ₛₑₜ range C ↔ ∃ a, b ∈ₛₑₜ C (↑{a}ₛₑₜ)
```

**New**:
- Prove `range_pred_cong C`: congruence of
  `b ↦ ∃ a, b ∈ₛₑₜ C (↑{a}ₛₑₜ)` in `b`.
  Key: `b₁ =₍U₂₎ b₂` → for each witness `a`, transfer `b ∈ₛₑₜ C (↑{a}ₛₑₜ)`
  via `(C (↑{a}ₛₑₜ)).cong`.
- Construct: `noncomputable def range_set (C: U₁ ⭢ᶜ U₂): Set U₂ :=`
  `{ b : U₂.Particular | ∃ a, b ∈ₛₑₜ C (↑{a}ₛₑₜ) } with range_pred_cong C`
- New axiom: `axiom range_def: ∀ C, range C =ₛₑₜ range_set C`
- Bridge: `theorem range_unfold: ∀ C, ∀ b, b ∈ₛₑₜ range C ↔ ∃ a, b ∈ₛₑₜ C (↑{a}ₛₑₜ)`

### 7. L2R Correspondence

**Current**:
```lean
axiom l2r_correspondence_def: ∀ R, ∀ a, ∀ S,
  (a ⭢ᵃ S) ∈ₛₑₜ R→ ↔ (S =ₛₑₜ l2r_fiber R a)
```

Same structure as Compose — characterizes arrow membership in a
correspondence via `∈ₛₑₜ`. The correspondence itself is never equated
to a constructed object.

**New**:
- Prove `l2r_correspondence_pred_cong R`: congruence of the arrow predicate
  `f ↦ ∃ a S, f =→ᵃ (a ⭢ᵃ S) ∧ S =ₛₑₜ l2r_fiber R a` under arrow equality.
- Construct: `noncomputable def l2r_correspondence_corr (R: Rel U₁ U₂): U₁ ⭢ᶜ U₂`
  built from the predicate via set comprehension on arrows.
- New axiom: `axiom l2r_correspondence_def: ∀ R, R→ =→ᶜ l2r_correspondence_corr R`
- Bridge: `theorem l2r_correspondence_unfold: ∀ R, ∀ a, ∀ S, (a ⭢ᵃ S) ∈ₛₑₜ R→ ↔ (S =ₛₑₜ l2r_fiber R a)`

**Downstream**: `l2r_correspondence_cong` (already proved) can be
simplified — with the new axiom, congruence should follow from the
constructed object rather than the ad-hoc proof currently there.

### 8. R2L Correspondence

**Current**:
```lean
axiom r2l_correspondence_def: ∀ R, ∀ b, ∀ S,
  (b ⭢ᵃ S) ∈ₛₑₜ R← ↔ (S =ₛₑₜ r2l_fiber R b)
```

Dual of L2R Correspondence — same structure, reversed direction.

**New**:
- Prove `r2l_correspondence_pred_cong R`: congruence of the arrow predicate
  `f ↦ ∃ b S, f =→ᵃ (b ⭢ᵃ S) ∧ S =ₛₑₜ r2l_fiber R b` under arrow equality.
- Construct: `noncomputable def r2l_correspondence_corr (R: Rel U₁ U₂): Corr U₂ U₁`
  built from the predicate via set comprehension on arrows.
- New axiom: `axiom r2l_correspondence_def: ∀ R, R← =→ᶜ r2l_correspondence_corr R`
- Bridge: `theorem r2l_correspondence_unfold: ∀ R, ∀ b, ∀ S, (b ⭢ᵃ S) ∈ₛₑₜ R← ↔ (S =ₛₑₜ r2l_fiber R b)`

**Downstream**: `r2l_correspondence_cong` (already proved) can be
simplified, same as L2R.

### 9. Compose

**Current**:
```lean
axiom compose_def: ∀ C₂, ∀ C₁, ∀ a, ∀ S,
  (a ⭢ᵃ S) ∈ₛₑₜ (C₂ ∘ᶜ C₁) ↔ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))
```

Same structure as L2R/R2L — characterizes arrow membership via `∈ₛₑₜ`.
The composed correspondence is a set of arrows, and its defining
predicate is on arrows: `(a ⭢ᵃ S) ↦ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))`.

**New**:
- Prove `compose_pred_cong C₂ C₁`: congruence of the arrow predicate
  `f ↦ ∃ a S, f =→ᵃ (a ⭢ᵃ S) ∧ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))` under arrow
  equality.
- Construct: `noncomputable def compose_corr (C₂: U₂ ⭢ᶜ U₃) (C₁: U₁ ⭢ᶜ U₂): U₁ ⭢ᶜ U₃`
  built from the predicate via set comprehension on arrows.
- New axiom: `axiom compose_def: ∀ C₂, ∀ C₁, (C₂ ∘ᶜ C₁) =→ᶜ compose_corr C₂ C₁`
- Bridge: `theorem compose_unfold: ∀ C₂, ∀ C₁, ∀ a, ∀ S, (a ⭢ᵃ S) ∈ₛₑₜ (C₂ ∘ᶜ C₁) ↔ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))`

## Naming Convention

- Predicate: `<op>_predicate` (e.g. `domain_predicate`, `compose_predicate`)
- Equality axiom: `<op>_def` (e.g. `domain_def`)
- Bridge theorem: `<op>_unfold` (e.g. `domain_unfold`)

The `_def` name belongs to the real definition (the equality axiom). The bridge
theorem gets `_unfold` — what else would you be unfolding if not a def? All
downstream references to the old `_def` must be renamed to `_unfold`.

## Execution Order

The execution order is driven by walking the project folders — the
user identifies each operation needing refactoring and requests it
step by step. The dependency notes below are for reference when
resolving compilation errors:

- **SingletonOf** — foundational, used by Domain/Range/CoClassification
- **Powerset** — self-contained within Sets
- **Union** — self-contained within Sets
- **Apply** — Domain/Range/Compose depend on it
- **Domain** — depends on Apply
- **Range** — depends on Apply
- **L2R Correspondence** — depends on L2R Fiber (already done)
- **R2L Correspondence** — depends on R2L Fiber (already done)
- **Compose** — depends on Apply

For each operation:
1. Create **Predicate.lean** — define `<op>_predicate` as a
   `CongruentUnaryPredicate` (or Binary) with its congruence proof
2. Modify **Operation.lean**:
   a. Replace the axiom: equality (`_def`) using set comprehension
      with the predicate's `.cong`
   b. Add the bridge theorem (`_unfold`) recovering the pointwise form
   c. Update existing congruence proofs and bundled operations
3. Compile with `lake env lean <file>`
4. Fix downstream compilation errors (rename `_def` → `_unfold`)

## Downstream Impact

After refactoring each operation, files that import it may need updates.
All downstream references to `_def` must be renamed to `_unfold`.

| Refactored Operation | Downstream Files |
|---------------------|-----------------|
| SingletonOf | Domain, Range (indirectly via Sets barrel) |
| Powerset | Properties/PowersetExistence.lean |
| Union | (none currently) |
| Apply | Domain, Range, Compose, CoClassification/Predicate.lean, Functional/Predicate.lean |
| Domain | Functional/Predicate.lean |
| Range | (none currently) |
| L2R Correspondence | `l2r_correspondence_cong` can be simplified |
| R2L Correspondence | `r2l_correspondence_cong` can be simplified |
| Compose | (none currently) |

## Verification

After each operation:
```
lake env lean <modified_file>
```

After all operations:
```
lake build
```
