import Logic.PredicateCalculus.Schemas.Operations.Unary.Schema

namespace Logic

namespace PC₁

/-!
# SubUniversal — the `<:` relation between Universals

## What `<:` is: a registration mechanism

`SubUniversal U' U` (notation: `U' <: U`) is a **registration mechanism**.
It records that there is a mapping from U'.Particular to U.Particular
satisfying a condition that we motivate below. Once registered, the
framework allows you to:
- Define **lift axioms** that propagate the subtype relationship through
  composite universals (dyads, relations, correspondences, etc.)
- Create **CoeDep instances** so that Lean can automatically coerce
  particulars of U' into particulars of U wherever needed.

In short: `<:` tells the framework "U' sits inside U", and this allows
you to build coercions that propagate sub-universality to composite universals.

## Why the condition is a `↔`

What condition should a mapping `e : U'.Particular → U.Particular` satisfy
for U' to count as sitting inside U? The answer comes from abstract algebra:
U' must be faithfully **embedded** in U — meaning the mapping preserves all
structure and does not collapse distinct elements. Such a mapping is called
an embedding (an injective homomorphism).

What an embedding concretely requires depends on the kind of structure:

- For **operations**, the homomorphism condition is an equation:
  `h(f(x,y)) = f(h(x), h(y))`. Equations are inherently bidirectional,
  so injectivity does not add a separate condition.

- For **relations**, the homomorphism condition is only an implication:
  `R(x,y) → R(h(x), h(y))`. Implications are directional, so injectivity
  adds the reverse: `R(h(x), h(y)) → R(x,y)`. Together these give the
  bidirectional equivalence: `R(x,y) ↔ R(h(x), h(y))`.

A Universal has only one piece of structure: equality — a relation. So the
embedding condition reduces to:

  x =₍U'₎ y  ↔  e(x) =₍U₎ e(y)

The bidirectional form arises here because equality is the only relation
being preserved, and injectivity is itself an equality condition. The
homomorphism direction (`→`) and the injectivity direction (`←`) both
involve the same relation, so they combine into a single `↔`.

**Example**: ℤ embeds into ℚ via n ↦ n/1. Equal integers map to equal
rationals (forward), and n₁/1 = n₂/1 implies n₁ = n₂ (backward).

**Counterexample**: f(n) = n mod 2 from ℕ to ℕ. The forward direction holds
(equal inputs give equal outputs), but backward fails: f(2) = f(4) yet 2 ≠ 4.
This is a homomorphism but not an embedding — it collapses distinct elements.

## Why this is not circular

The mathematical concepts of "function", "injectivity", and "embedding" do not
yet exist in the framework at this point. We used embedding theory above to
*motivate* the condition, but the definition itself does not depend on it.

The definition of `<:` is entirely self-contained: an `embedding` (UnaryOperation)
and a proof `preserves_eq`. These refer only to operations on particulars and to
the equalities of U' and U — first-order logic primitives that exist before any
mathematics has been built. No framework definition of function, injectivity,
or embedding is imported or referenced.

Later, when the framework defines these concepts as mathematical objects, one
could prove *within the framework* that every `<:` instance corresponds to an
embedding. That theorem would be a satisfying consistency check, but it is not
needed for the definition to be valid.

## Why this infrastructure exists

The framework uses many-sorted first-order logic. Lean does have subtyping
infrastructure (Subtype, coercions, type classes), but we cannot leverage it
for this purpose because our framework uses its own equalities (`=₍U₎`) —
axiomatized predicates that Lean's type system knows nothing about. Lean's
`Subtype.val` handles the element-level injection, but Lean cannot see that
sub-universal equality and parent equality agree, nor propagate this through
our axiomatized composite types.

`SubUniversal` fills this gap. It is framework infrastructure that compensates
for Lean not being a native many-sorted FOL engine. The `embedding` field, the
`preserves_eq` proof, the subsume axioms, and the CoeDep instances are all machinery
that a proper many-sorted engine would provide for free.

## How `<:` propagates through composite universals

`<:` is a typeclass. This allows automated subsuming of Sub-Universals using a a single generic CoeDep instance.

Each composite universal (Dyads, Relations, ...) must provide, subsume operations
that lift component sub-universality into composite sub-universality and use them
to register the composite sub-universality instance.

-/

-- Sub-Universality Registration mechanism: records that U' sits faithfully inside U via
-- an embedding (UnaryOperation) that preserves equality in both directions.
class SubUniversal (U₁: Universal) (U₂: Universal): Type where
  embedding: U₁ ⟴ U₂
  preserves_eq: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), x =₍U₁₎ y ↔ (embedding x =₍U₂₎ embedding y)

notation:25 U':26 " <: " U:26 => SubUniversal U' U

-- Generic CoeDep for automated sub-universal subsumption (used for explicit ↑ coercion)
noncomputable instance {U₁ U₂: Universal} [e: U₁ <: U₂]
    (x: U₁.Particular): CoeDep U₁.Particular x U₂.Particular where
  coe := e.embedding x


end PC₁

end Logic
