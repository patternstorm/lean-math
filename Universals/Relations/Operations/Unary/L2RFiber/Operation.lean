import Universals.Relations.Universal
import Universals.Correspondences.Universal
import Universals.Sets
import Universals.Dyads

/-!
# Left-to-Right Fiber

-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets

-- Proof by GPT-5.4, 2026-03-08
theorem l2r_fiber_cong {U₁: Universal} (R: Rel U₁ U₂) (a: U₁.Particular) :
  ∀ (x: U₂.Particular), ∀ (y: U₂.Particular), x =₍U₂₎ y → (R.pred (a ⋈ x) ↔ R.pred (a ⋈ y)) := by forall_intro
  variable(y₁: U₂.Particular)
  variable(y₂: U₂.Particular)
  assume(h₁: y₁ =₍U₂₎ y₂)
  have h₂: a =₍U₁₎ a := U₁.eq.refl a
  have h₃: a =₍U₁₎ a ∧ y₁ =₍U₂₎ y₂ := by and_intro h₂, h₁
  have h₄: ∀ (b₁: U₂.Particular), ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (a ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim Dyads.eq_def, a
  have h₅: ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (a ⋈ y₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a =₍U₁₎ a₂ ∧ y₁ =₍U₂₎ b₂ := by forall_elim h₄, y₁
  have h₆: ∀ (b₂: U₂.Particular),
    (a ⋈ y₁) =ₗₓₗ (a ⋈ b₂) ↔ a =₍U₁₎ a ∧ y₁ =₍U₂₎ b₂ := by forall_elim h₅, a
  have h₇: (a ⋈ y₁) =ₗₓₗ (a ⋈ y₂) ↔ a =₍U₁₎ a ∧ y₁ =₍U₂₎ y₂ := by forall_elim h₆, y₂
  have h₈: (a ⋈ y₁) =ₗₓₗ (a ⋈ y₂) := PC₀.deductive_eq_r2l h₇ h₃
  have h₉: ∀ (d₁: (U₁ ⋈ U₂).Particular), ∀ (d₂: (U₁ ⋈ U₂).Particular), d₁ =ₗₓₗ d₂ → (R.pred d₁ ↔ R.pred d₂) := R.cong
  have h₁₀: ∀ (d₂: (U₁ ⋈ U₂).Particular), (a ⋈ y₁) =ₗₓₗ d₂ → (R.pred (a ⋈ y₁) ↔ R.pred d₂) := by forall_elim h₉, (a ⋈ y₁)
  have h₁₁: (a ⋈ y₁) =ₗₓₗ (a ⋈ y₂) → (R.pred (a ⋈ y₁) ↔ R.pred (a ⋈ y₂)) := by forall_elim h₁₀, (a ⋈ y₂)
  have h₁₂: R.pred (a ⋈ y₁) ↔ R.pred (a ⋈ y₂) := by modus_ponens h₁₁, h₈
  iterate h₁₂

-- # l2r_correspondence: Relation → Correspondence
axiom l2r_fiber: Rel U₁ U₂ → U₁.Particular → Set U₂

-- # Axiom definition
axiom l2r_fiber_def: ∀ (R: Rel U₁ U₂), ∀ (a: U₁.Particular),
  l2r_fiber R a =ₛₑₜ { y: U₂.Particular | R.pred (a ⋈ y) } with l2r_fiber_cong R a

-- TODO: Prove Congruent Operation

end Relations

end Universe
