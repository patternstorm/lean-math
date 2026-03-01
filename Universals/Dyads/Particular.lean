import Universe
import Logic

/-!
# Dyad

## Co-Existence

Existence is the only primitive assertion in this framework. A particular `a`
asserts that `a` exists. A dyad `a ⋈ b` asserts exactly one thing: that `a`
and `b` co-exist in the universe. Nothing more — no direction, no relation,
no properties. Before predication, a dyad has no relational content; it only
asserts that its two particulars can be relata.

Particulars and dyads are equally primitive, equally bare. The only difference
is structural — the number of terms whose co-existence is asserted. Predicates
are what make this co-existence meaningful: a unary predicate on a dyad
actualizes which relations hold.

## Predicate Uniformity

Unary predicates on particulars actualize properties. Unary predicates on
dyads actualize relations. Since dyads are themselves particulars of their
own Universal, all predicates remain unary — they just act on different
structural levels. This is the uniform view: all predicates select particulars.

## Recursive Co-Existential Closure

The universe is closed under co-existential binding at all levels. Dyads nest:
`a ⋈ (b ⋈ c)` exists if `a` and `b ⋈ c` exist. Because dyads are
predicate-associative — different nestings of the same base particulars are
predicate-equivalent — the dimension of a co-existence is simply the number
of base particulars it involves. The curry/uncurry axiom schemes
(see Definitions/) transport between n-ary predicates and unary predicates
on nested dyads.

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
