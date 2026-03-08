import Universals.Relations.Universal
import Universals.Correspondences.Universal
import Universals.Sets
import Universals.Dyads

/-!
# Right-to-Left Fiber

-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets

-- Proof by GPT-5.4, 2026-03-08
theorem r2l_fiber_cong {U₁: Universal} (R: Rel U₁ U₂) (b: U₂.Particular):
  ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), x =₍U₁₎ y → (R.pred (x ⋈ b) ↔ R.pred (y ⋈ b)) := by forall_intro
  variable(x₁: U₁.Particular)
  variable(x₂: U₁.Particular)
  assume(h₁: x₁ =₍U₁₎ x₂)
  have h₂: b =₍U₂₎ b := U₂.eq.refl b
  have h₃: x₁ =₍U₁₎ x₂ ∧ b =₍U₂₎ b := by and_intro h₁, h₂
  have h₄: ∀ (b₁: U₂.Particular), ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (x₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ x₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim Dyads.eq_def, x₁
  have h₅: ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (x₁ ⋈ b) =ₗₓₗ (a₂ ⋈ b₂) ↔ x₁ =₍U₁₎ a₂ ∧ b =₍U₂₎ b₂ := by forall_elim h₄, b
  have h₆: ∀ (b₂: U₂.Particular),
    (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b₂) ↔ x₁ =₍U₁₎ x₂ ∧ b =₍U₂₎ b₂ := by forall_elim h₅, x₂
  have h₇: (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b) ↔ x₁ =₍U₁₎ x₂ ∧ b =₍U₂₎ b := by forall_elim h₆, b
  have h₈: (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b) := PC₀.deductive_eq_r2l h₇ h₃
  have h₉: ∀ (d₁: (U₁ ⋈ U₂).Particular), ∀ (d₂: (U₁ ⋈ U₂).Particular), d₁ =ₗₓₗ d₂ → (R.pred d₁ ↔ R.pred d₂) := R.cong
  have h₁₀: ∀ (d₂: (U₁ ⋈ U₂).Particular), (x₁ ⋈ b) =ₗₓₗ d₂ → (R.pred (x₁ ⋈ b) ↔ R.pred d₂) := by forall_elim h₉, (x₁ ⋈ b)
  have h₁₁: (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b) → (R.pred (x₁ ⋈ b) ↔ R.pred (x₂ ⋈ b)) := by forall_elim h₁₀, (x₂ ⋈ b)
  have h₁₂: R.pred (x₁ ⋈ b) ↔ R.pred (x₂ ⋈ b) := by modus_ponens h₁₁, h₈
  iterate h₁₂

-- # r2l_correspondence: Relation → Correspondence
axiom r2l_fiber: Rel U₁ U₂ → U₂.Particular → Set U₁

-- # Axiom definition
axiom r2l_fiber_def: ∀ (R: Rel U₁ U₂), ∀ (b: U₂.Particular),
  r2l_fiber R b =ₛₑₜ { x: U₁.Particular | R.pred (x ⋈ b) } with r2l_fiber_cong R b

-- TODO: Prove Congruent Operation

end Relations

end Universe
