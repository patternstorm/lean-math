import Universe
import Logic

/-!
# Dyad

## Motivation: the uniform predicate view

Unary predicates select particulars: P(x) picks out elements of a Universal.
But what about predicates of higher arity? A binary predicate R(x,y) takes
terms from two Universals — it doesn't select elements, it selects *relations*.

The key insight is that we can restore uniformity by introducing dyads —
particulars that represent the relatedness of two terms. If a : U₁ and b : U₂,
then a ⋈ b : U₁ ⋈ U₂ is the dyad binding a and b into a single relatum.
A binary predicate, recast as a unary predicate on dyads, selects
relation-particulars from a Dyad Universal — exactly as a unary predicate
selects elements from an ordinary Universal.

This is the uniform view: all predicates select particulars.
The arity of a predicate determines only what kind of particular it selects —
elements for unary, dyads for binary, nested dyads for higher arities.

## Dyads are not pairs

A dyad is not a pair or product. Pairs package data; dyads represent relations.
The distinction is semantic, not structural: a ⋈ b is the relatum of a and b,
the particular that witnesses their relatedness under some predicate.

## Higher arities via nesting

Dyads nest to handle any arity. A ternary predicate R(x,y,z) becomes a unary
predicate on U₁ ⋈ (U₂ ⋈ U₃). The curry/uncurry axiom schemes (see Definitions/),
applied iteratively, transport between n-ary predicates and unary predicates
on nested dyads. No new machinery is needed beyond arity 2.

## ADT specification

The Dyad is postulated as an abstract data type, following the same pattern
as natural numbers: type, equality, generative constructor, impurifier
equations, and exhaustiveness. Unlike natural numbers, the Dyad has a single
non-recursive constructor, so no induction principle is needed —
exhaustiveness alone suffices to prove the equality is an equivalence relation.
-/

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁

-- # Type
axiom Dyad(U₁: Universal)(U₂: Universal) : Type

-- # Equality
axiom eq: Dyad U₁ U₂ → Dyad U₁ U₂ → Prop
notation:50 a:51 " =ₗₓₗ " b:51 => eq a b

-- # Generative Constructors
axiom bind{U₁: Universal}{U₂: Universal}: U₁.Particular → U₂.Particular → Dyad U₁ U₂
notation:35 x:36 " ⋈ " y:36 => bind x y

-- # Impurifier Equations
axiom eq_def: ∀ (a₁: U₁.Particular), ∀ (b₁: U₂.Particular),
  ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular), (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂

-- # Exhaustiveness
axiom exhaustiveness: ∀ d: Dyad U₁ U₂, ∃ a: U₁.Particular, ∃ b: U₂.Particular, d 🟰 (a ⋈ b)

end Dyads
end Universe
