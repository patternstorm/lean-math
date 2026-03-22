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

For operations returning **Sets** (which covers all 7 operations
in this refactoring), the preferred approach is **set comprehension
with a named congruence proof**:

```lean
-- 1. Congruence proof defined as a named theorem
theorem <op>_pred_cong ... : ∀ x y, x =₍U₎ y → (P x ↔ P y) := ...

-- 2. Set comprehension references the proof by name
{ x : T | body } with <op>_pred_cong ...
```

The congruence proof is written as a named theorem first, then
the set comprehension references it via the `with` clause. Both
live in the same Operation.lean file. No separate `Predicate.lean`
file or explicit `CongruentUnaryPredicate` structure is needed.

The heavier approach — building a `CongruentUnaryPredicate` or
`CongruentBinaryPredicate` in a separate `Predicate.lean` file,
then using `relation_from` — is reserved for cases where the
predicate has multiple layers of congruence (e.g.
co-classification's ternary predicate) or when the result is a
Relation requiring `uncurry` via `relation_from`. For Sets,
always use set comprehension notation — never `set_from` directly.

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

## Classification of All Operations

### Already correct — no changes needed

| Operation | File | Pattern used |
|-----------|------|-------------|
| L2R Fiber | `Relations/Operations/Unary/L2RFiber/Operation.lean` | `=ₛₑₜ` with set comprehension |
| R2L Fiber | `Relations/Operations/Unary/R2LFiber/Operation.lean` | `=ₛₑₜ` with set comprehension |
| Co-Classification | `Correspondences/Operations/Unary/CoClassification/Operation.lean` | `=ᵣₑₗ` with `relation_from` |
| L2R Correspondence | `Relations/Operations/Unary/L2RCorrespondence/Operation.lean` | `=ₛₑₜ` equating to `l2r_fiber` |
| R2L Correspondence | `Relations/Operations/Unary/R2LCorrespondence/Operation.lean` | `=ₛₑₜ` equating to `r2l_fiber` |

### Already using set comprehension — no changes needed

| Operation | File | How defined |
|-----------|------|-------------|
| Empty Set | `Sets/Operations/Constants/EmptySet/Constant.lean` | `{ x | False } with (false U).cong` |
| Universal Set | `Sets/Operations/Constants/UniversalSet/Constant.lean` | `{ x | True } with (true U).cong` |

### Need refactoring — 7 operations

| # | Operation | File | Current axiom form |
|---|-----------|------|--------------------|
| 1 | SingletonOf | `Sets/Universals/Singleton/Operations/Unary/SingletonOf/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 2 | Powerset | `Sets/Operations/Unary/Powerset/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 3 | Union | `Sets/Operations/Binary/Union/Operation.lean` | `.pred` / `↔` |
| 4 | Apply | `Correspondences/Operations/Unary/Application/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 5 | Domain | `Correspondences/Operations/Unary/Domain/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 6 | Range | `Correspondences/Operations/Unary/Range/Operation.lean` | `∈ₛₑₜ` / `↔` |
| 7 | Compose | `Correspondences/Operations/Binary/Composition/Operation.lean` | `∈ₛₑₜ` / `↔` |

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

### 7. Compose

**Current**:
```lean
axiom compose_def: ∀ C₂, ∀ C₁, ∀ a, ∀ S,
  (a ⭢ᵃ S) ∈ₛₑₜ (C₂ ∘ᶜ C₁) ↔ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))
```

This is the most complex case. The composed correspondence is a set
of arrows, and its defining predicate is on arrows:
`(a ⭢ᵃ S) ↦ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))`.

**New**:
- Prove `compose_pred_cong C₂ C₁`: congruence of the arrow predicate
  `f ↦ ∃ a S, f =→ᵃ (a ⭢ᵃ S) ∧ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))` under arrow
  equality. Or alternatively, express it as a `CongruentUnaryPredicate`
  on the arrow universal.
- Construct: `noncomputable def compose_corr (C₂: U₂ ⭢ᶜ U₃) (C₁: U₁ ⭢ᶜ U₂): U₁ ⭢ᶜ U₃`
  built from the predicate via set comprehension on arrows.
- New axiom: `axiom compose_def: ∀ C₂, ∀ C₁, (C₂ ∘ᶜ C₁) =→ᶜ compose_corr C₂ C₁`
- Bridge: `theorem compose_unfold: ∀ C₂, ∀ C₁, ∀ a, ∀ S, (a ⭢ᵃ S) ∈ₛₑₜ (C₂ ∘ᶜ C₁) ↔ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))`

## Naming Convention

**Open question**: How to name the new equality axiom vs the bridge theorem.

**Option A — Keep `_def` as the bridge**:
- New equality axiom: `<op>_eq` (e.g. `domain_eq`)
- Bridge theorem (old form): `<op>_def` (e.g. `domain_def`)
- Pro: All existing downstream code referencing `_def` keeps working unchanged.
- Con: The "real" definition is not named `_def`.

**Option B — `_def` for the equality, `_unfold` for the bridge**:
- New equality axiom: `<op>_def` (e.g. `domain_def`)
- Bridge theorem: `<op>_unfold` (e.g. `domain_unfold`)
- Pro: Semantically clean — `_def` is the canonical definition.
- Con: All downstream references to `_def` must be renamed to `_unfold`.

## Execution Order

Dependencies flow downward — refactor in this order:

1. **SingletonOf** — foundational, used by Domain/Range/CoClassification
2. **Powerset** — self-contained within Sets
3. **Union** — self-contained within Sets
4. **Apply** — Domain/Range/Compose depend on it
5. **Domain** — depends on Apply
6. **Range** — depends on Apply
7. **Compose** — depends on Apply

For each operation:
1. Prove the predicate congruence as a named theorem (in the Operation.lean file)
2. Define the constructed object via set comprehension, referencing the congruence proof by name (`noncomputable def`)
3. Replace the axiom (membership → equality)
4. Add the bridge theorem
5. Update existing congruence proofs and bundled operations
6. Compile with `lake env lean <file>`
7. Fix downstream compilation errors

## Downstream Impact

After refactoring each operation, files that import it may need updates:

| Refactored Operation | Downstream Files |
|---------------------|-----------------|
| Apply | Domain, Range, Compose, CoClassification/Predicate.lean, Functional/Predicate.lean |
| Domain | Functional/Predicate.lean |
| SingletonOf | Domain, Range (indirectly via Sets barrel) |
| Powerset | Properties/PowersetExistence.lean |
| Compose | (none currently) |
| Range | (none currently) |
| Union | (none currently) |

## Verification

After each operation:
```
lake env lean <modified_file>
```

After all operations:
```
lake build
```
