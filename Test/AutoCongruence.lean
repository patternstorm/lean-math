import Universe
import Logic
import Universals.Relations.Universal

/-!
# Auto-Congruence Tests

Tests for the type class mechanism that automatically derives congruence
for predicates built from congruent building blocks. The classes and instances
live in the framework:

- `CongruentUnary` / `CongruentBinary` — in Schema files
- Connective instances (∧, ∨, ∃, ∀, ¬, ∃!, =₍U₎, constant) — in Properties/Instances files
- `curry_reducicle_def_left/right` + `congruent_curry` / `congruent_curry_partial_left/right` — in Curry/Definition

## Constraint

Predicates must use universal equality notation `=₍U₎` rather than type-specific
shorthands like `=ₗₓₗ`. The type class instance `congruent_equal_to` matches against
`universal_eq`, and type-specific notations (which bypass it) prevent unification.
-/

namespace Test.AutoCongruence

open Logic
open Logic.PC₁
open Logic.ND
open Universe.Sets
open Universe.Dyads
open Universe.Relations

-- ============================================================
-- # 1. Tests with abstract universals
-- ============================================================

variable {U: Universal}

-- Test 1: simple equality — x =₍U₎ a
example (a: U.Particular): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ x =₍U₎ a)

-- Test 2: constant — doesn't mention x
example (A: Prop): CongruentUnaryPredicate U :=
  (_: U.Particular ↦ A)

-- Test 3: conjunction of constant and equality
example (a: U.Particular) (A: Prop): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ A ∧ x =₍U₎ a)

-- Test 4: existential over equality
variable {V: Universal}
example (f: V.Particular → U.Particular): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ ∃ (z: V.Particular), x =₍U₎ f z)

-- Test 5: existential + conjunction (constant + equality)
example (a: U.Particular) (A: Prop): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ ∃ (_z: V.Particular), A ∧ x =₍U₎ a)

-- Test 6: nested existentials
variable {W: Universal}
example (f: V.Particular → W.Particular → U.Particular): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ ∃ (z: V.Particular), ∃ (w: W.Particular), x =₍U₎ f z w)

-- Test 6.5: disjunction of two equalities
example (a b: U.Particular): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ x =₍U₎ a ∨ x =₍U₎ b)

-- Test 6.7: universal quantifier over equality
example (f: V.Particular → U.Particular): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ ∀ (z: V.Particular), x =₍U₎ f z)

-- Test 6.9: exists-unique over equality
example (f: V.Particular → U.Particular): CongruentUnaryPredicate U :=
  (x: U.Particular ↦ ∃!₍V₎ (z: V.Particular), x =₍U₎ f z)

-- ============================================================
-- # 2. Full subsumption pattern
-- ============================================================

variable {U₁' U₁ U₂' U₂: Universal}
variable (e₁: U₁' <: U₁) (e₂: U₂' <: U₂) (R₁: Rel U₁' U₂')

-- Test 7: the full subsumption predicate pattern (must use =₍U₎ notation)
example: CongruentUnaryPredicate (U₁ ⧓ U₂) :=
  (d: U₁ ⋈ U₂ ↦
    ∃ (d': (U₁' ⧓ U₂').Particular), ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular),
      d' ∈ₛₑₜ R₁ ∧ d' =₍(U₁' ⧓ U₂')₎ (a' ⋈ b') ∧ d =₍(U₁ ⧓ U₂)₎ (e₁.embedding a' ⋈ e₂.embedding b'))

-- ============================================================
-- # 3. Set comprehension without `with`
-- ============================================================

-- Test: set comprehension with the subsumption pattern
-- (uses the framework's without-`with` macro from SetComprehension/Definition.lean)
example: Set (U₁ ⧓ U₂) :=
  { d : U₁ ⋈ U₂ |
      ∃ (d': (U₁' ⧓ U₂').Particular), ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular),
        d' ∈ₛₑₜ R₁ ∧ d' =₍(U₁' ⧓ U₂')₎ (a' ⋈ b') ∧ d =₍(U₁ ⧓ U₂)₎ (e₁.embedding a' ⋈ e₂.embedding b') }

-- ============================================================
-- # 4. Fiber pattern: partial application of curried predicate on dyads
-- ============================================================

-- Test 8: l2r fiber pattern — R.pred (a ⋈ y)
example (R: Rel U₁ U₂) (a: U₁.Particular): CongruentUnaryPredicate U₂ :=
  (y: U₂.Particular ↦ R.pred (a ⋈ y))

end Test.AutoCongruence
