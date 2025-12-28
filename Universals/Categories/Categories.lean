import Core.Universe
import Core.Sets

/-!
# Categories as Ternary Predicates over Two Types

Just as a `Unary Predicate` partitions a `Universe` into `Sets`, and a `Binary Predicate` introduces `Relations` and `Functions`,
a pair of `Ternary Predicates` over two types introduces a richer structure: the `Category`.

A `Category` requires two types: one whose terms play the role of `Objects`, and another whose terms play the role of `Morphisms`.
Crucially, the terms of these types carry no intrinsic structure — they are not functions, not maps, not arrows. They are simply terms.
The categorical structure is entirely imposed by `Predicates`.

## The Morphism Predicate

The first `Ternary Predicate`, `morphism : X → X → Y → Prop`, transforms unstructured terms into typed arrows.

Given `morphism a b f`, we interpret: "the term `f` is an arrow from object `a` to object `b`."

Before this `Predicate`: `Y` is merely a collection of terms.
After this `Predicate`: `Y` is structured as arrows between objects in `X`.

The `Predicate` does not *discover* that `f` is an arrow — it *declares* how it becomes an arrow. This is the `Predicate` doing what `Predicates` do:
imposing structure on an unstructured universe.

Three axioms govern this `Predicate`:
- **Totality**: every term in `Y` is a `Morphism` between some pair of `Objects`.
- **Total on composable pairs**: when `Morphisms` have matching types, a composite must exist.
- **Uniqueness**: each `Morphism` has exactly one source and one target — arrows do not have multiple types.

## The Composition Predicate

The second `Ternary Predicate`, `op : Y → Y → Y → Prop`, declares which `Morphisms` compose to produce which results.

Given `op g f h`, we interpret: "the `Morphism` `h` is the composite of `f` followed by `g`."

This `Predicate` is constrained to be:
- **Partial**: Only `Morphisms` with matching types (codomain of `f` equals domain of `g`) have a composite.
- **Functional**: When composition is defined, the result is unique.

Partiality is expressed according to our definition of `Binary Relations` and the `Correspondences` they create, i.e.
through `Sets`: `op g f` yields a `Singleton` when `f` and `g` are composable, and the `Empty Set` otherwise.
Functionality is expressed via `IsSingleton` — a predicate on `Sets`, using the framework's stratification.

## The Category Axioms

A `Category` is a refined type: a record containing two ternary `Predicates`, constrained by axioms.

- **comp_well_typed**: If `h` is a composite of `f` and `g`, then the types match — `f : a → b`, `g : b → c`, `h : a → c`.
- **comp_morph_exists**: If types match, a unique composite exists.
- **id_exists**: Each `Object` has an identity morphism that acts as left and right unit for composition.
- **comp_assoc**: Composition is associative — `h ∘ (g ∘ f) = (h ∘ g) ∘ f`.

## Philosophical Significance

This approach reveals that `Categories` need not be built on `Sets` or `Functions` as primitives. The standard definition
of category uses "collections" of objects and morphisms, and "functions" for composition and identity. Our definition shows:

1. **`Objects` and `Morphisms` are just types** — arbitrary types, with no required structure.
2. **The arrow structure is declared, not intrinsic** — the `morphism` predicate interprets terms as arrows.
3. **Composition is a relation constrained to be functional** — not a primitive function.

**Category Theory** is often presented as an alternative foundation to **Set Theory**. Our framework shows that both are
theories within the same foundation: first-order logic with the right notion of predicate. **Category Theory** is not
a foundation — it is a structure that emerges from `Predicates`, just as `Sets` and `Functions` do.

The definition also serves as a **template for construction**: bring any two types, define how terms of one type
are arrows between terms of the other, define how arrows compose, verify the axioms — and you have a `Category`.
The types can be anything: numbers, propositions, monoids, other categories. The predicate imposes the structure.

This vindicates the logicist program at a new level: not only **Arithmetic** and **Set Theory**, but **Category Theory** itself
derives from logic.
-/


namespace Categories

open Universe
open Sets

structure Category(X: Type)(Y: Type) where
  Ob: Set X := Uₛₑₜ
  Hom: Set Y := Uₛₑₜ
  morphism : X → X → Y → Prop -- f is a morphism from a to b
  op : Y → Y → Y → Prop -- the relation on Y that defines the operation of composition, it needs to be a function, that's why it returns a Singleton
  morph_totality: ∀ (f: Y), ∃ (a: X), ∃ (b: X), morphism a b f -- all terms in Y must be morphisms
  morph_uniqueness: ∀ (f: Y), ∀ (a: X), ∀ (b: X), ∀ (c: X), ∀ (d: X), (morphism a b f) ∧ (morphism c d f) → (a =ₚ c) ∧ (b =ₚ d) -- a morphism should be unique
  comp_well_typed: ∀ (f: Y), ∀ (g: Y), ∀ (h: Y), (h ∈ₛₑₜ op g f) → ∃ (a: X), ∃ (b: X), ∃ (c: X), (morphism a b f) ∧ (morphism b c g) ∧ (morphism a c h)
  comp_morph_exists: ∀ (f: Y), ∀ (g: Y), ∀ (a: X), ∀ (b: X), ∀ (c: X), (morphism a b f) ∧ (morphism b c g) → IsSingleton (op g f) -- if two morphisms are composable then the composite morphism exists
  id_morph_exists: ∀ (a: X), ∃ (id: Y), (morphism a a id) ∧ (∀ (b: X), ∀ (f: Y), morphism a b f → (f ∈ₛₑₜ op f id)) ∧ (∀ (b: X), ∀ (f: Y), morphism b a f → (f ∈ₛₑₜ op id f)) -- identity morphism exists
  comp_assoc: ∀ (f: Y), ∀ (g: Y), ∀ (h: Y), ∀ (gf: Y), ∀ (hg: Y), (gf ∈ₛₑₜ op g f) ∧ (hg ∈ₛₑₜ op h g) → (op h gf) =ₛₑₜ (op hg f)

end Categories
