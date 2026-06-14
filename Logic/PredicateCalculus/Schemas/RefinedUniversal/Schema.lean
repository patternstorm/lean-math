import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals

namespace Logic

namespace PC₁

/-!
# Refined Universals

A refined universal is a new Universal obtained by restricting an existing Universal
to elements satisfying a congruent predicate. Given Universal U and
CongruentUnaryPredicate P on U, `U ↾ P` is a new Universal whose particulars
are elements of U satisfying P.

## This is syntactic sugar over FOL - we are NOT leaving FOL behind

Quantifying over a refined universal is equivalent to using implication:
  `∀ x : (U ↾ P).Particular, Q(x)`  ≡  `∀ x : U.Particular, P(x) → Q(x)`

## Working with refined universal elements

Given `RU := U ↾ P` and `x : RU.Particular`:

- `x` is the subtype element (value + proof bundled together)
- `↑x` (or `x.val`) extracts the underlying `U.Particular` element
- `x.property` gives the proof that `↑x` satisfies P

## When to use `↑` (underlying element) vs `x` directly

- **Use `x` directly**: with predicates/equality defined on the refined universal
    Example: `x =₍RU₎ y` — refined universal's equality on subtype elements

- **Use `↑x`**: with predicates defined on the parent universal U
    Example: `Q.pred ↑x` — predicate Q defined on U needs underlying element

## Examples

```
-- No ↑ needed: refined universal's equality
∀ (x : RU.Particular), x =₍RU₎ x

-- ↑ needed: predicate Q defined on U
∀ (x : RU.Particular), Q.pred ↑x → Q.pred ↑x

-- Mixed: refined universal equality + predicate on U
∀ (x y : RU.Particular), x =₍RU₎ y → Q.pred ↑x → Q.pred ↑y
```
-/

-- ## Why this uses Lean directly (not the ND framework)
--
-- This definition uses Lean's fun/∀ instead of our natural deduction tactics.
-- This is justified because refined_universal is **logic infrastructure**, not
-- mathematics. In a native many-sorted FOL engine, "restrict sort U to elements
-- satisfying predicate P" would be a built-in operation of the engine itself —
-- the engine would automatically create the new sort, inherit equality from the
-- parent, and verify the equivalence relation properties carry over.
--
-- Lean does provide subtyping infrastructure (Subtype, coercions), but it knows
-- nothing about our axiomatized equalities (=₍U₎). So we implement this engine-level
-- operation manually for our Universals. The fun lambdas delegating to `=₍U₎` are the
-- implementation of what the engine would provide for free.
--
-- Mathematics starts when you use the resulting Universal in ND proofs — proving
-- things about elements of the refined universal. That is where the framework's
-- natural deduction rules apply.
def refined_universal (U : Universal) (P : CongruentUnaryPredicate U) : Universal :=
  let T := { x : U.Particular // P.pred x }
  let pred: T → T → Prop :=
    fun (a: T) (b: T) => a.val =₍U₎ b.val
  let refl: ∀ (a: T), pred a a :=
    fun (a: T) => U.eq.refl a.val
  let sym: ∀ (a: T), ∀ (b: T), pred a b → pred b a :=
    fun (a: T) (b: T) (h: a.val =₍U₎ b.val) => U.eq.sym a.val b.val h
  let trans: ∀ (a: T), ∀ (b: T), ∀ (c: T), pred a b ∧ pred b c → pred a c :=
    fun (a: T) (b: T) (c: T) (h: a.val =₍U₎ b.val ∧ b.val =₍U₎ c.val) =>
      U.eq.trans a.val b.val c.val h
  { Particular := T, eq := { pred := pred, refl := refl, sym := sym, trans := trans } }

notation:max U " ↾ " P => refined_universal U P

end PC₁

end Logic
