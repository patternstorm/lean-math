import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema

namespace Logic

namespace PC₁

/-!
# Sub-Universals

A sub-universal is a refined type of a Universal, defined by a congruent predicate.
Given Universal U and CongruentUnaryPredicate P on U, `sub_universal U P` is a new
Universal whose particulars are elements of U satisfying P.

## This is syntactic sugar over FOL - we are NOT leaving FOL behind

Quantifying over a sub-universal is equivalent to using implication:
  `∀ x : (sub_universal U P).Particular, Q(x)`  ≡  `∀ x : U.Particular, P(x) → Q(x)`

## Working with sub-universal elements

Given `SU := sub_universal U P` and `x : SU.Particular`:

- `x` is the subtype element (value + proof bundled together)
- `↑x` (or `x.val`) extracts the underlying `U.Particular` element
- `x.property` gives the proof that `↑x` satisfies P

## When to use `↑` (underlying element) vs `x` directly

- **Use `x` directly**: with predicates/equality defined on the sub-universal
    Example: `x =₍SU₎ y` — sub-universal's equality on subtype elements

- **Use `↑x`**: with predicates defined on the parent universal U
    Example: `Q.pred ↑x` — predicate Q defined on U needs underlying element

## Examples

```
-- No ↑ needed: sub-universal's equality
∀ (x : SU.Particular), x =₍SU₎ x

-- ↑ needed: predicate Q defined on U
∀ (x : SU.Particular), Q.pred ↑x → Q.pred ↑x

-- Mixed: sub-universal equality + predicate on U
∀ (x y : SU.Particular), x =₍SU₎ y → Q.pred ↑x → Q.pred ↑y
```
-/

def sub_universal (U : Universal) (P : CongruentUnaryPredicate U) : Universal :=
  let T := { x : U.Particular // P.pred x }
  {
    Particular := T
    eq := {
      pred := fun (a : T) (b : T) => a.val =₍U₎ b.val
      refl := fun (a : T) => U.eq.refl a.val
      sym := fun (a : T) (b : T) (h : a.val =₍U₎ b.val) => U.eq.sym a.val b.val h
      trans := fun (a : T) (b : T) (c : T) (h : a.val =₍U₎ b.val ∧ b.val =₍U₎ c.val) =>
        U.eq.trans a.val b.val c.val h
    }
  }

-- Notation: ↑x extracts the underlying U.Particular from a sub-universal element
-- This is clearer than .val and indicates extracting the underlying element
scoped prefix:max "↑" => Subtype.val

end PC₁

end Logic
