import Universals.Correspondences.Operations.Unary.CoClassification.Operation

/-!
# Co-Classification is Symmetric

The co-classification relation induced by a correspondence is symmetric:
if b₁ and b₂ are co-classified (a unique source particular co-classifies both),
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

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
theorem co_classification_symmetry: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
  (co_classification C).pred (b₁ ⋈ b₂) → (co_classification C).pred (b₂ ⋈ b₁) := by forall_intro
  variable(C: U₁ ⭢ᶜ U₂)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  assume(h₁: (co_classification C).pred (b₁ ⋈ b₂))

  -- Unfold co_classification at (b₁, b₂)
  have h₂: ∀ (x: U₂.Particular), ∀ (y: U₂.Particular),
    (co_classification C).pred (x ⋈ y) ↔ ∃!₍U₁₎ a, x ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ y ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim co_classification_unfold, C
  have h₃: ∀ (y: U₂.Particular),
    (co_classification C).pred (b₁ ⋈ y) ↔ ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ y ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₂, b₁
  have h₄: (co_classification C).pred (b₁ ⋈ b₂) ↔ ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₃, b₂

  -- Get ∃! and unfold to ∃ with uniqueness
  have h₅: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₄ h₁
  let P: U₁.Particular → Prop := (a: U₁.Particular ↦ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
  let P': U₁.Particular → Prop := (a: U₁.Particular ↦ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ))
  have eu_U₁: ∀ (Q: U₁.Particular → Prop), ExistsUnique U₁ Q ↔ (∃ (x: U₁.Particular), Q x ∧ (∀ (y: U₁.Particular), Q y → y =₍U₁₎ x)) := by forall_elim exists_unique_def, U₁
  have eu_P: ExistsUnique U₁ P ↔ (∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P
  have eu_P': ExistsUnique U₁ P' ↔ (∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P'

  have h₅': ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P h₅
  have ⟨(a: U₁.Particular), (h₆: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a))⟩ := exists_elim h₅'
  have h₇: P a := by and_elim h₆
  have h₇_unique: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by and_elim h₆
  have h₈: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₇
  have h₉: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₇

  -- Swap conjuncts: P' a = b₂ ∈ C({a}) ∧ b₁ ∈ C({a})
  have h₁₀: P' a := by and_intro h₉, h₈

  -- Transfer uniqueness: ∀ y, P' y → y =₍U₁₎ a
  have h₁₁: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by forall_intro
    variable(a': U₁.Particular)
    assume(h₁₁₁: P' a')
    -- P' a' = b₂ ∈ C({a'}) ∧ b₁ ∈ C({a'})
    have h₁₁₂: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₁₁₁
    have h₁₁₃: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₁₁₁
    -- Swap back to get P a'
    have h₁₁₄: P a' := by and_intro h₁₁₃, h₁₁₂
    have h₁₁₅: P a' → a' =₍U₁₎ a := by forall_elim h₇_unique, a'
    have h₁₁₆: a' =₍U₁₎ a := by modus_ponens h₁₁₅, h₁₁₄
    iterate h₁₁₆

  -- Reconstruct ∃! for (b₂, b₁)
  have h₁₂: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a) := by and_intro h₁₀, h₁₁
  have h₁₃: ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := by exists_intro h₁₂, a
  have h₁₄: ∃!₍U₁₎ a, b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P' h₁₃

  -- Unfold co_classification at (b₂, b₁) and close
  have h₁₅: ∀ (y: U₂.Particular),
    (co_classification C).pred (b₂ ⋈ y) ↔ ∃!₍U₁₎ a, b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ y ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₂, b₂
  have h₁₆: (co_classification C).pred (b₂ ⋈ b₁) ↔ ∃!₍U₁₎ a, b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_elim h₁₅, b₁
  have h₁₇: (co_classification C).pred (b₂ ⋈ b₁) := PC₀.deductive_eq_r2l h₁₆ h₁₄
  iterate h₁₇

end Correspondences

end Universe
