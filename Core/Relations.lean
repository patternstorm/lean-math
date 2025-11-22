import Core.NaturalDeduction
import Core.Universe
import Core.Sets

/-!
# Relations
-/

namespace Universe

namespace Relations

open Sets

-- # A `Binary Relation` is a `Binary Predicate`
def BinRel := Universe.BinaryPredicate

-- # Set equality
axiom eq: BinRel X → BinRel X → Prop
notation:50 A:51 " =ᵣₑₗ " B:51 => eq A B

axiom eq_refl: ∀ (R: BinRel X), R =ᵣₑₗ R
axiom eq_poly_eq : ∀ (R₁: BinRel X), ∀ (R₂: BinRel X), R₁ =ᵣₑₗ R₂ ↔ R₁ =ₚ R₂
-- NOTE, we should be able to derive these
axiom eq_sym: ∀ (R₁: BinRel X), ∀ (R₂: BinRel X), R₁ =ᵣₑₗ R₂ → R₂ =ᵣₑₗ R₁
axiom eq_trans: ∀ (R₁: BinRel X), ∀ (R₂: BinRel X), ∀ (R₃: BinRel X), R₁ =ᵣₑₗ R₂ ∧ R₂ =ᵣₑₗ R₃ → R₁ =ᵣₑₗ R₃

def l2r_dom (R: BinRel X): Set X := { x: Particular X | (∃ (y: Particular X), R x y) }
prefix:max "dom→" => l2r_dom
def l2r_codom (R: BinRel X): Set X := { y: Particular X | (∃ (x: Particular X), R x y) }
prefix:max "codom→" => l2r_codom

def r2l_dom (R: BinRel X): Set X := l2r_codom R
prefix:max "dom←" => r2l_dom
def r2l_codom (R: BinRel X): Set X := l2r_dom R
prefix:max "codom←" => r2l_codom

axiom l2r_apply : (R: BinRel X) → (x: Particular X) → Set X
notation:max R "⟨" x "⟩" => l2r_apply R x

axiom r2l_apply : (R: BinRel X) → (y: Particular X) → Set X
notation:max R "⟨·," y "⟩" => r2l_apply R y

axiom l2r_apply_def: ∀ (R: BinRel X), ∀ (x: Particular X), R⟨x⟩ =ₛₑₜ { y: Particular X | R x y }
axiom r2l_apply_def: ∀ (R: BinRel X), ∀ (y: Particular X), R⟨·,y⟩ =ₛₑₜ { x: Particular X | R x y }

axiom function_l2r: BinRel X → Prop
axiom function_r2l: BinRel X → Prop

axiom function_l2r_def: ∀ (R: BinRel X), function_l2r R ↔ ∀ (x: Particular X), (x ∈ₛₑₜ dom→ R) → (Singleton R⟨x⟩)
axiom function_r2l_def: ∀ (R: BinRel X), function_r2l R ↔ ∀ (y: Particular X), (y ∈ₛₑₜ dom← R) → (Singleton R⟨·,y⟩)

-- TODO: prove
theorem l2r_dom_iff_non_empty_l2r_apply:
  ∀ (R: BinRel X), (dom→ R) =ₛₑₜ { x: Particular X | ¬(R⟨x⟩ =ₛₑₜ ∅ₛₑₜ) } := sorry

-- TODO: prove
theorem l2r_codom_iff_non_empty_r2l_apply:
  ∀ (R: BinRel X), (codom→ R) =ₛₑₜ { y: Particular X | ¬(R⟨·,y⟩ =ₛₑₜ ∅ₛₑₜ) } := sorry

end Relations

end Universe
