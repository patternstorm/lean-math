import Universe
import Logic

/-!
# Arrow

## Production

An arrow `a ⟶ b` asserts that from the particular on the left, I can produce
the particular on the right. This is a primitive directed concept, distinct
from co-existence (dyads). Before predication, an arrow has no content beyond
this bare productive capacity.

## Relationship to Dyads

Arrows and dyads are parallel ADTs with the same structure — type, equality,
constructor, componentwise equality, exhaustiveness. The difference is
semantical:

- Dyad `a ⋈ b`: co-existence (undirected) — a and b stand together
- Arrow `a ⟶ b`: production (directed) — from a, produce b

Both are general: they exist between any two universals.

## Role in the Framework

The natural way to select arrows is through relations, via the correspondences
they induce. A correspondence is a set of arrows of type `Arrow U₁ (𝐒𝐞𝐭 U₂)`
— from an individual, produce a set. When a correspondence is functional (all
images are singletons), it is isomorphic to a set of direct `Arrow U₁ U₂`
arrows — from an individual, produce an individual.

## ADT Specification

The Arrow is postulated as an abstract data type, following the same pattern
as the Dyad: type, equality, generative constructor, impurifier equations,
and exhaustiveness. Single non-recursive constructor, so exhaustiveness alone
suffices to prove the equality is an equivalence relation.
-/

namespace Universe
namespace Arrows

open Logic
open Logic.PC₁

-- # Type
axiom Arrow(U₁: Universal)(U₂: Universal) : Type

-- # Equality
axiom eq: Arrow U₁ U₂ → Arrow U₁ U₂ → Prop
notation:50 a:51 " =→ᵃ  " b:51 => eq a b

-- # Generative Constructors
axiom arrow{U₁: Universal}{U₂: Universal}: U₁.Particular → U₂.Particular → Arrow U₁ U₂
notation:35 x:36 " ⭢ᵃ " y:36 => arrow x y

-- # Existence
-- The generative constructor declaration above specifies the signature of the
-- function symbol — its syntactic structure. This existence axiom incarnates
-- it: for any two particulars, their arrow exists. See README.md Note 6.
axiom existence {U₁ U₂: Universal}:
    ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), ∃ (f: Arrow U₁ U₂), f 🟰 (a ⭢ᵃ b)

-- # Impurifier Equations
axiom eq_def: ∀ (a₁: U₁.Particular), ∀ (b₁: U₂.Particular),
  ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular), (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂

-- # Exhaustiveness
axiom exhaustiveness: ∀ f: Arrow U₁ U₂, ∃ a: U₁.Particular, ∃ b: U₂.Particular, f 🟰 (a ⭢ᵃ b)

end Arrows
end Universe
