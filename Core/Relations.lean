import Core.NaturalDeduction
import Core.Universe
import Core.Sets

/-!
# Binary Relations and Functions as Binary Predicates

Just as a `Unary Predicate` partitions the `Universe` into two parts (those `Particulars` satisfying the `Predicate` and those that don't),
a `Binary Predicate` introduces a different kind of structure into the `Universe`.

A `Binary Predicate` states a property that may or may not hold between any two `Particulars` in the `Universe`. To determine whether the
property holds for a specific pair of `Particulars`, the statement must express something that can be evaluated about one `Particular`
with respect to the other. This necessity introduces an asymmetry: the statement must fix one `Particular` and then express a property about
that `Particular` with respect to the other. This effectively introduces two roles that `Particulars` can play when determining whether they
satisfy the `Binary Predicate`.

Therefore, a `Binary Predicate` introduces the following structure into the `Universe`:

  1. **Two roles** that `Particulars` can play.
  2. **Two entangled `Correspondences`**:
     - For each particular playing the first role, which particulars playing the second role satisfy the `Binary Predicate`.
     - For each particular playing the second role, which particulars playing the first role satisfy the `Binary Predicate`.

*Note*: The two correspondences are **entangled** because they describe the same underlying property, just viewed from each role's perspective.
Knowing how all `Particulars` playing the first role relate to those playing the second role automatically determines how all `Particulars` playing
the second role relate to those playing the first role.

We call this structure a `Binary Relation`, because we interpret that if two `Particulars` satisfy the predicate with each playing a different role,
then they are related to each other as specified by the `Binary Predicate`.

## Roles and Correspondences

- The `Binary Predicate` `Pxy` introduces two roles: the role played by the variable `x` and the role played by the variable `y`.
  - We call the role played by `x` the **left role** and the role played by `y` the **right role**.

- The `Correspondences` are functions mapping each `Particular` playing one role to a `Set` of `Particulars` playing the other role.
  - Therefore, `Correspondences` have a `Domain` and a `Codomain`.
  - We call the `Correspondence` mapping each `Particular` playing the left role to a `Set` of `Particulars` playing the right role the **left-to-right `Correspondence`**.
  - We call the `Correspondence` mapping each `Particular` playing the right role to a `Set` of `Particulars` playing the left role the **right-to-left `Correspondence`**.

## Functions as Binary Relations

A correspondence is a **function** if every `Particular` in its `Domain` is mapped to a `Singleton Set` in its `Codomain`.

A `Binary Relation` is a **`Functional Relation`** (or simply a **`Function`**) if its left-to-right `Correspondence` maps every `Particular` in its `Domain`
to a `Singleton Set` in its `Codomain` — that is, each particular playing the left role is related to exactly one particular playing the right role.
**Note**: we choose the left-to-right `Correspondence` to be the `Correspondence` that characterizes the `Function` to match the traditional definition of `Function`.

## Philosophical Significance

This approach shows that the concept of `Function` need not be primitive — it can be derived from the notion of `Binary Predicate`. Furthermore,
both `Binary Relations` and `Functions` can be defined without using `Cartesian Products`, which we don't use at all in the definition of `Binary
Relations` and `Functions` that follows.

-/

namespace Universe

namespace Relations

open Sets

-- # A `Binary Relation` is a `Binary Predicate`
def BinRel := Universe.BinaryPredicate

-- # A `Correspondance` is a map from X to Set X
def Correspondance (X : Type) := Particular X → Set X

-- # `Binary Relation` equality
axiom eq: BinRel X → BinRel X → Prop
notation:50 A:51 " =ᵣₑₗ " B:51 => eq A B

axiom eq_refl: ∀ (R: BinRel X), R =ᵣₑₗ R
axiom eq_poly_eq : ∀ (R₁: BinRel X), ∀ (R₂: BinRel X), R₁ =ᵣₑₗ R₂ ↔ R₁ =ₚ R₂
-- NOTE, we should be able to derive these
axiom eq_sym: ∀ (R₁: BinRel X), ∀ (R₂: BinRel X), R₁ =ᵣₑₗ R₂ → R₂ =ᵣₑₗ R₁
axiom eq_trans: ∀ (R₁: BinRel X), ∀ (R₂: BinRel X), ∀ (R₃: BinRel X), R₁ =ᵣₑₗ R₂ ∧ R₂ =ᵣₑₗ R₃ → R₁ =ᵣₑₗ R₃

-- ## Two `Binary Relations` are equal if their predicates are logically equivalent.
axiom eq_def: ∀ R₁: BinRel X, ∀ R₂: BinRel X, (R₁ =ᵣₑₗ R₂) ↔ (∀ (x: Particular X), ∀ (y: Particular X), R₁ x y ↔ R₂ x y)

-- # Predicate to characterize `Functional Correspondences`
def is_correspondence_functional (f : Correspondance X) : Prop := ∀ (x : Particular X), Singleton (f x)
prefix:max "Functional " => is_correspondence_functional


-- # `Left-to-right `Correspondence`
-- ## Domain
def l2r_dom (R: BinRel X): Set X := { x: Particular X | (∃ (y: Particular X), R x y) }
prefix:max "dom→" => l2r_dom
-- ## Codomain
def l2r_codom (R: BinRel X): Set X := { y: Particular X | (∃ (x: Particular X), R x y) }
prefix:max "codom→" => l2r_codom
-- ## Application
axiom l2r_apply : (R: BinRel X) → (x: Particular X) → Set X
notation:max R "⟨" x "⟩" => l2r_apply R x
axiom l2r_apply_def: ∀ (R: BinRel X), ∀ (x: Particular X), R⟨x⟩ =ₛₑₜ { y: Particular X | R x y }
-- ## Functional Characterization
axiom functional_l2r: BinRel X → Prop
prefix:max "Functional→ " => functional_l2r
axiom functional_l2r_def: ∀ (R: BinRel X), (Functional→ R) ↔ (Functional (x: Particular X ↦ R⟨x⟩))

-- # `Right-to-left `Correspondence`
-- ## Domain
def r2l_dom (R: BinRel X): Set X := l2r_codom R
prefix:max "dom←" => r2l_dom
-- ## Codomain
def r2l_codom (R: BinRel X): Set X := l2r_dom R
prefix:max "codom←" => r2l_codom
-- ## Application
axiom r2l_apply : (R: BinRel X) → (y: Particular X) → Set X
notation:max R "⟨·," y "⟩" => r2l_apply R y
axiom r2l_apply_def: ∀ (R: BinRel X), ∀ (y: Particular X), R⟨·,y⟩ =ₛₑₜ { x: Particular X | R x y }
-- ## Functional Characterization
axiom functional_r2l: BinRel X → Prop
prefix:max "Functional← " => functional_r2l
axiom functional_r2l_def: ∀ (R: BinRel X), (Functional← R) ↔ (Functional (y: Particular X ↦ R⟨·,y⟩))

-- # Functional Characterization of a Binary Relation
def is_binary_relation_functional (R: BinRel X): Prop := Functional→ R
prefix:max "Functional " => is_binary_relation_functional

-- # Theorems
-- TODO: prove
-- R<x> in Set codom-> R
theorem l2r_dom_iff_non_empty_l2r_apply:
  ∀ (R: BinRel X), (dom→ R) =ₛₑₜ { x: Particular X | ¬(R⟨x⟩ =ₛₑₜ ∅ₛₑₜ) } := sorry

-- TODO: prove
theorem l2r_codom_iff_non_empty_r2l_apply:
  ∀ (R: BinRel X), (codom→ R) =ₛₑₜ { y: Particular X | ¬(R⟨·,y⟩ =ₛₑₜ ∅ₛₑₜ) } := sorry

theorem function_composition_l2r (R₁ : BinRel X) (R₂ : BinRel X) :
dom→ R₁ = dom→ R₂ := sorry

end Relations

end Universe
