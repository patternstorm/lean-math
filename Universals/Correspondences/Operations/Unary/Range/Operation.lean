import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Application.Operation

/-!
# Correspondence Range

The range of a correspondence is the set of target particulars that are
co-classified by at least one particular in the source universal — the part of the target
universal that gets co-classified by the source universal.

```
range C = { b : U₂ | ∃ a : U₁.Particular, b ∈ₛₑₜ C (↑{a}ₛₑₜ) }
```
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Arrows

axiom range: U₁ ⭢ᶜ U₂ → Set U₂

axiom range_def: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (b: U₂.Particular), b ∈ₛₑₜ range C ↔ ∃ (a: U₁.Particular), b ∈ₛₑₜ C (↑{a}ₛₑₜ)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
theorem range_cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂),
  C₁ =→ᶜ C₂ → range C₁ =ₛₑₜ range C₂ := by forall_intro
  variable(C₁: U₁ ⭢ᶜ U₂)
  variable(C₂: U₁ ⭢ᶜ U₂)
  assume(h₁: C₁ =→ᶜ C₂)

  -- From C₁ =→ᶜ C₂, for any set S: C₁ S =ₛₑₜ C₂ S
  have h₂: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂' S := by forall_elim apply_cong_first, C₁
  have h₃: C₁ =→ᶜ C₂ → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by forall_elim h₂, C₂
  have h₄: ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by modus_ponens h₃, h₁

  -- Set extensionality for the result
  have h₅: ∀ (R₂: Set U₂), range C₁ =ₛₑₜ R₂ ↔ (∀ (x: U₂.Particular), x ∈ₛₑₜ range C₁ ↔ x ∈ₛₑₜ R₂) := by forall_elim set_extensionality, range C₁
  have h₆: range C₁ =ₛₑₜ range C₂ ↔ (∀ (x: U₂.Particular), x ∈ₛₑₜ range C₁ ↔ x ∈ₛₑₜ range C₂) := by forall_elim h₅, range C₂

  -- range_def for both correspondences
  have h₇: ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₁ ↔ ∃ (a: U₁.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim range_def, C₁
  have h₈: ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₂ ↔ ∃ (a: U₁.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim range_def, C₂

  have h₉: ∀ (x: U₂.Particular), x ∈ₛₑₜ range C₁ ↔ x ∈ₛₑₜ range C₂ := by forall_intro
    variable(b: U₂.Particular)
    have h₉₁: b ∈ₛₑₜ range C₁ ↔ ∃ (a: U₁.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim h₇, b
    have h₉₂: b ∈ₛₑₜ range C₂ ↔ ∃ (a: U₁.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₈, b

    -- Forward: b ∈ range C₁ → b ∈ range C₂
    have h₉₃: b ∈ₛₑₜ range C₁ → b ∈ₛₑₜ range C₂ := by
      assume(h₉₃₁: b ∈ₛₑₜ range C₁)
      have h₉₃₂: ∃ (a: U₁.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₁ h₉₃₁
      have ⟨(a: U₁.Particular), (h₉₃₃: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ))⟩ := exists_elim h₉₃₂
      -- Transfer membership via apply congruence
      have h₉₃₄: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
      have h₉₃₅: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
      have h₉₃₆: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₉₃₅, C₂ (↑{a}ₛₑₜ)
      have h₉₃₇: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₃₆ h₉₃₄
      have h₉₃₈: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₉₃₇, b
      have h₉₃₉: b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₃₈ h₉₃₃
      have h₉₃₁₀: ∃ (a: U₁.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by exists_intro h₉₃₉, a
      have h₉₃₁₁: b ∈ₛₑₜ range C₂ := PC₀.deductive_eq_r2l h₉₂ h₉₃₁₀
      iterate h₉₃₁₁

    -- Backward: b ∈ range C₂ → b ∈ range C₁
    have h₉₄: b ∈ₛₑₜ range C₂ → b ∈ₛₑₜ range C₁ := by
      assume(h₉₄₁: b ∈ₛₑₜ range C₂)
      have h₉₄₂: ∃ (a: U₁.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₂ h₉₄₁
      have ⟨(a: U₁.Particular), (h₉₄₃: b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ))⟩ := exists_elim h₉₄₂
      -- Transfer membership via apply congruence
      have h₉₄₄: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
      have h₉₄₅: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
      have h₉₄₆: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₉₄₅, C₂ (↑{a}ₛₑₜ)
      have h₉₄₇: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₄₆ h₉₄₄
      have h₉₄₈: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₉₄₇, b
      have h₉₄₉: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₉₄₈ h₉₄₃
      have h₉₄₁₀: ∃ (a: U₁.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by exists_intro h₉₄₉, a
      have h₉₄₁₁: b ∈ₛₑₜ range C₁ := PC₀.deductive_eq_r2l h₉₁ h₉₄₁₀
      iterate h₉₄₁₁

    have h₉₅: b ∈ₛₑₜ range C₁ ↔ b ∈ₛₑₜ range C₂ := by iff_intro h₉₃, h₉₄
    iterate h₉₅

  have h₁₀: range C₁ =ₛₑₜ range C₂ := PC₀.deductive_eq_r2l h₆ h₉
  iterate h₁₀

-- Range as a congruent unary operation from correspondences to sets.
noncomputable def range_operation (U₁: Universal) (U₂: Universal): CongruentUnaryOperation (U₁ ➞ᶜ U₂) (𝐒𝐞𝐭 U₂) :=
  let op: U₁ ⭢ᶜ U₂ → Set U₂ := range
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (range C₁ =ₛₑₜ range C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    have h₁: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → range C₁ =ₛₑₜ range C₂' := by forall_elim range_cong, C₁
    have h₂: C₁ =→ᶜ C₂ → range C₁ =ₛₑₜ range C₂ := by forall_elim h₁, C₂
    assume(h₃: C₁ =→ᶜ C₂)
    have h₄: range C₁ =ₛₑₜ range C₂ := by modus_ponens h₂, h₃
    iterate h₄
  { op := op, cong := cong }

end Correspondences

end Universe
