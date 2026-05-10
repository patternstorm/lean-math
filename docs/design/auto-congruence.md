# Auto-Congruence: Automatic Derivation of Predicate Congruence

## Problem

Every `CongruentUnaryPredicate` requires proving `∀ x y, x =₍U₎ y → (P x ↔ P y)` — typically 30-80 lines of natural deduction per predicate. This is the biggest source of boilerplate in the framework. Many predicates are structurally composed from congruent building blocks (equality, constants, conjunction, existential quantification), yet each one requires a manual proof that repeats the same patterns.

## Solution

A Lean 4 type class `Congruent U P` that decomposes predicates structurally and derives congruence automatically. Combined with a `CoeDep` coercion, plain lambdas coerce to `CongruentUnaryPredicate U` (and therefore `Set U`) wherever the type is expected.

## Prototype

Working prototype: `Test/AutoCongruence.lean`. All tests compile, including the full subsumption predicate pattern (3 nested existentials, 2 conjunctions, constants, atomic equality).

### The type class

```lean
class Congruent (U: Universal) (P: U.Particular → Prop) where
  toPred: CongruentUnaryPredicate U
```

### Instances

| Instance | Pattern | Delegates to |
|----------|---------|-------------|
| `congruent_equal_to` | `x =₍U₎ a` | `equal_to a` |
| `congruent_constant` (priority 100) | `fun _ => A` | `constant_predicate A` |
| `congruent_conjunction` | `P x ∧ Q x` | `conjunction_preserves_congruence` |
| `congruent_existential` | `∃ z, P z x` | `existential_preserves_congruence` |
| `congruent_negation` | `¬P x` | `negation_preserves_congruence1` |

### Coercion

```lean
instance congruent_coercion {U: Universal} {P: U.Particular → Prop}
    [c: Congruent U P]: CoeDep (U.Particular → Prop) P (CongruentUnaryPredicate U) where
  coe := c.toPred
```

### Result

Set comprehension without `with`:
```lean
{ d : U₁ ⋈ U₂ |
    ∃ d' a' b', d' ∈ₛₑₜ R₁ ∧ d' =₍..₎ (a' ⋈ b') ∧ d =₍..₎ (e₁ a' ⋈ e₂ b') }
```

## Constraint

Predicates must use universal equality notation `=₍U₎` (which goes through `universal_eq`) rather than type-specific shorthands like `=ₗₓₗ` (which uses `Dyads.eq` directly). The `congruent_equal_to` instance matches against `universal_eq`, and type-specific notations bypass this path, preventing unification during instance resolution.

## Scope

### What auto-congruence handles

Any predicate built from: `=₍U₎`, constants (propositions not mentioning the free variable), `∧`, `∃`, `¬`.

### What it cannot handle (leave as-is)

Predicates using `∀` (forall quantifier), `∃!` (unique existential), or complex axiom-based definitions:

- Relation properties: `reflexive_predicate`, `symmetric_predicate`, `transitive_predicate`, `quasi_reflexive_predicate`
- Correspondence properties: `total_predicate`, `functional_predicate`, `surjective_predicate`
- Set inclusion: `supersets_of`, `subsets_of` (forall in inclusion definition)
- Singleton: `singleton_predicate` (uses ∃!)
- Co-classification: `co_classified_with` (uses ∃!)

These continue to use manual congruence proofs.

### Future extensions

- **Disjunction instance** (`P x ∨ Q x`): Requires a new `disjunction_preserves_congruence` theorem (~45 lines ND proof). Would fix the `union` `sorry`.
- **Universal quantifier instance** (`∀ z, P z x`): Would handle relation/correspondence properties. Significant new theorem.
- **Exists-unique instance** (`∃! z, P z x`): Would handle singleton/co-classification predicates.

## Refactoring plan

Execute step by step, compiling after each with `lake env lean <file>`.

### Step 1: Create the type class file

**New file**: `Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/AutoCongruence.lean`

Move content from `Test/AutoCongruence.lean` (type class, 5 instances, CoeDep coercion) into the framework. Imports: `Unary/Schema`, `Unary/Instances/Constant`, `Unary/Properties` (barrel), `Binary/Instances/Equals/Instance`.

### Step 2: Update barrel file

**File**: `Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances.lean`

Add import for the new file.

### Step 3: Add without-`with` set comprehension macro

**File**: `Universals/Sets/Definitions/SetComprehension/Definition.lean`

Add alongside existing `with` macro:
```lean
macro "{" x:ident ":" t:term "|" body:term "}" : term =>
  `(set_from (fun $x : $t => $body))
```

Both macros coexist — Lean prefers the longer match (with `with`) when present. The `with` version remains for predicates that can't use auto-congruence.

### Step 4: Simplify set constants

- **`Universals/Sets/Operations/Constants/EmptySet/Constant.lean`**: `{ x | False }` — remove `with (false U).cong`
- **`Universals/Sets/Operations/Constants/UniversalSet/Constant.lean`**: `{ x | True }` — remove `with (true U).cong`

### Step 5: Fix set operations

**File**: `Universals/Sets/Sets.lean`

- **`compl`**: Remove `with negation_preserves_congruence1 A`
- **`inter`**: Currently broken (uses `fun` syntax). Replace with `{ x : X.Particular | A.pred x ∧ B.pred x }`
- **`union`**: Keep `with sorry` — needs disjunction preservation (future step)

### Step 6: Simplify Relations subsumption_of

**File**: `Universals/Relations/Predicates/Binary/SubsumptionGraph/Predicate.lean`

Currently 8 lines of manual composition. Replace with plain lambda + CoeDep coercion. Switch `=ₗₓₗ` to `=₍(U₁ ⧓ U₂)₎`.

### Step 7: Simplify Dyads subsumption_of

**File**: `Universals/Dyads/Predicates/Binary/SubsumptionGraph/Predicate.lean`

The 50-line manual cong proof becomes auto-derived. Replace with lambda + CoeDep.

**Risk**: The outer `subsumption_graph` definition (cong/ltot/rdet proofs) unfolds `(pred d').pred d`. If the auto-derived `.pred` doesn't definitionally equal the lambda body, these proofs break.

**Mitigation**: Do this step last. If outer proofs break, adjust them or keep `subsumption_of` simplified and fix the outer proofs separately.

### Step 8: Clean up

Delete `Test/AutoCongruence.lean` — its functionality is now in the framework.

## Files summary

| File | Change |
|------|--------|
| `Logic/.../Unary/Instances/AutoCongruence.lean` | **NEW** — type class + instances + CoeDep |
| `Logic/.../Unary/Instances.lean` | Add 1 import line |
| `Universals/Sets/Definitions/SetComprehension/Definition.lean` | Add without-`with` macro |
| `Universals/Sets/Operations/Constants/EmptySet/Constant.lean` | Remove `with` |
| `Universals/Sets/Operations/Constants/UniversalSet/Constant.lean` | Remove `with` |
| `Universals/Sets/Sets.lean` | Fix `inter`, simplify `compl` |
| `Universals/Relations/.../SubsumptionGraph/Predicate.lean` | Lambda + CoeDep |
| `Universals/Dyads/.../SubsumptionGraph/Predicate.lean` | Lambda + CoeDep (biggest win: 50 lines → 3) |
| `Test/AutoCongruence.lean` | Delete after migration |
