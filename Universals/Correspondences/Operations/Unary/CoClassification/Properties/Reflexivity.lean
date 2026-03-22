import Universals.Correspondences.Operations.Unary.CoClassification.Operation
import Universals.Correspondences.Operations.Unary.Range.Operation

/-!
# Co-Classification is Reflexive on the Range

The co-classification relation induced by a correspondence is reflexive on the
range of the correspondence: every target particular that is co-classified by
at least one source particular is co-classified with itself.

```
∀ C, ∀ b, b ∈ₛₑₜ range C → (co_classification C).pred (b ⋈ b)
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
theorem co_classification_reflexivity: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (b: U₂.Particular),
  b ∈ₛₑₜ range C → (co_classification C).pred (b ⋈ b) := by forall_intro
  variable(C: U₁ ⭢ᶜ U₂)
  variable(b: U₂.Particular)
  assume(h₁: b ∈ₛₑₜ range C)

  -- Unfold range membership: b ∈ₛₑₜ range C ↔ ∃ a, b ∈ₛₑₜ C(↑{a}ₛₑₜ)
  have h₂: ∀ (b': U₂.Particular), b' ∈ₛₑₜ range C ↔ ∃ (a: U₁.Particular), b' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim range_def, C
  have h₃: b ∈ₛₑₜ range C ↔ ∃ (a: U₁.Particular), b ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₂, b
  have h₄: ∃ (a: U₁.Particular), b ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₃ h₁

  -- Extract the witness: some source particular a co-classifies b
  have ⟨(a: U₁.Particular), (h₅: b ∈ₛₑₜ C (↑{a}ₛₑₜ))⟩ := exists_elim h₄

  -- Unfold co_classification at (b, b)
  have h₆: ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    (co_classification C).pred (b₁ ⋈ b₂) ↔ ∃ (a': U₁.Particular), b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by forall_elim co_classification_unfold, C
  have h₇: ∀ (b₂: U₂.Particular),
    (co_classification C).pred (b ⋈ b₂) ↔ ∃ (a': U₁.Particular), b ∈ₛₑₜ C (↑{a'}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by forall_elim h₆, b
  have h₈: (co_classification C).pred (b ⋈ b) ↔ ∃ (a': U₁.Particular), b ∈ₛₑₜ C (↑{a'}ₛₑₜ) ∧ b ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by forall_elim h₇, b

  -- Construct the witness: a co-classifies b with itself
  have h₉: b ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_intro h₅, h₅
  have h₁₀: ∃ (a': U₁.Particular), b ∈ₛₑₜ C (↑{a'}ₛₑₜ) ∧ b ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by exists_intro h₉, a
  have h₁₁: (co_classification C).pred (b ⋈ b) := PC₀.deductive_eq_r2l h₈ h₁₀
  iterate h₁₁

end Correspondences

end Universe
