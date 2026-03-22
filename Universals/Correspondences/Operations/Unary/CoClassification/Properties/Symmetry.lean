import Universals.Correspondences.Operations.Unary.CoClassification.Operation

/-!
# Co-Classification is Symmetric

The co-classification relation induced by a correspondence is symmetric:
if b₁ and b₂ are co-classified (some source particular co-classifies both),
then b₂ and b₁ are co-classified by the same particular.

```
∀ C, ∀ b₁ b₂, (co_classification C).pred (b₁ ⋈ b₂) → (co_classification C).pred (b₂ ⋈ b₁)
```
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
theorem co_classification_symmetry: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
  (co_classification C).pred (b₁ ⋈ b₂) → (co_classification C).pred (b₂ ⋈ b₁) := by forall_intro
  variable(C: U₁ ⭢ᶜ U₂)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  assume(h₁: (co_classification C).pred (b₁ ⋈ b₂))

  -- Unfold co_classification at (b₁, b₂)
  have h₂: ∀ (x: U₂.Particular), ∀ (y: U₂.Particular),
    (co_classification C).pred (x ⋈ y) ↔ ∃ (a: U₁.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ y ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim co_classification_unfold, C
  have h₃: ∀ (y: U₂.Particular),
    (co_classification C).pred (b₁ ⋈ y) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ y ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₂, b₁
  have h₄: (co_classification C).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₃, b₂

  -- Extract the witness
  have h₅: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₄ h₁
  have ⟨(a: U₁.Particular), (h₆: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))⟩ := exists_elim h₅
  have h₇: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₆
  have h₈: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₆

  -- Unfold co_classification at (b₂, b₁) and reconstruct with swapped conjuncts
  have h₉: ∀ (y: U₂.Particular),
    (co_classification C).pred (b₂ ⋈ y) ↔ ∃ (a: U₁.Particular), b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ y ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₂, b₂
  have h₁₀: (co_classification C).pred (b₂ ⋈ b₁) ↔ ∃ (a: U₁.Particular), b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₉, b₁

  have h₁₁: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_intro h₈, h₇
  have h₁₂: ∃ (a: U₁.Particular), b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by exists_intro h₁₁, a
  have h₁₃: (co_classification C).pred (b₂ ⋈ b₁) := PC₀.deductive_eq_r2l h₁₀ h₁₂
  iterate h₁₃

end Correspondences

end Universe
