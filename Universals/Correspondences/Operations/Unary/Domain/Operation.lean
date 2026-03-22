import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Application.Operation

/-!
# Correspondence Domain

The domain of a correspondence is the set of source particulars that at least
co-classify one target particular, or, equivalently, all particulars in the
source Universal that do not map to False in the target Universal.

```
domain C = { a : U₁ | ∃ b : U₂.Particular, b ∈ₛₑₜ C (↑{a}ₛₑₜ) }
```
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Arrows

axiom domain: U₁ ⭢ᶜ U₂ → Set U₁

axiom domain_def: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (a: U₁.Particular),
  a ∈ₛₑₜ domain C ↔ ∃ (b: U₂.Particular), b ∈ₛₑₜ C (↑{a}ₛₑₜ)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
theorem domain_cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂),
  C₁ =→ᶜ C₂ → domain C₁ =ₛₑₜ domain C₂ := by forall_intro
  variable(C₁: U₁ ⭢ᶜ U₂)
  variable(C₂: U₁ ⭢ᶜ U₂)
  assume(h₁: C₁ =→ᶜ C₂)

  -- From C₁ =→ᶜ C₂, for any set S: C₁ S =ₛₑₜ C₂ S
  have h₂: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂' S := by forall_elim apply_cong_first, C₁
  have h₃: C₁ =→ᶜ C₂ → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by forall_elim h₂, C₂
  have h₄: ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by modus_ponens h₃, h₁

  -- Set extensionality for the result
  have h₅: ∀ (R₂: Set U₁), domain C₁ =ₛₑₜ R₂ ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ R₂) := by forall_elim set_extensionality, domain C₁
  have h₆: domain C₁ =ₛₑₜ domain C₂ ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ domain C₂) := by forall_elim h₅, domain C₂

  -- domain_def for both correspondences
  have h₇: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ ↔ ∃ (b: U₂.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim domain_def, C₁
  have h₈: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ ↔ ∃ (b: U₂.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim domain_def, C₂

  have h₉: ∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ domain C₂ := by forall_intro
    variable(a: U₁.Particular)
    have h₉₁: a ∈ₛₑₜ domain C₁ ↔ ∃ (b: U₂.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim h₇, a
    have h₉₂: a ∈ₛₑₜ domain C₂ ↔ ∃ (b: U₂.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₈, a

    -- C₁ {a} =ₛₑₜ C₂ {a}, so membership is equivalent
    have h₉₃: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
    have h₉₄: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
    have h₉₅: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₉₄, C₂ (↑{a}ₛₑₜ)
    have h₉₆: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₅ h₉₃

    -- Forward: a ∈ domain C₁ → a ∈ domain C₂
    have h₉₇: a ∈ₛₑₜ domain C₁ → a ∈ₛₑₜ domain C₂ := by
      assume(h₉₇₁: a ∈ₛₑₜ domain C₁)
      have h₉₇₂: ∃ (b: U₂.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₁ h₉₇₁
      have ⟨(b: U₂.Particular), (h₉₇₃: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ))⟩ := exists_elim h₉₇₂
      have h₉₇₄: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₉₆, b
      have h₉₇₅: b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₇₄ h₉₇₃
      have h₉₇₆: ∃ (b: U₂.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by exists_intro h₉₇₅, b
      have h₉₇₇: a ∈ₛₑₜ domain C₂ := PC₀.deductive_eq_r2l h₉₂ h₉₇₆
      iterate h₉₇₇

    -- Backward: a ∈ domain C₂ → a ∈ domain C₁
    have h₉₈: a ∈ₛₑₜ domain C₂ → a ∈ₛₑₜ domain C₁ := by
      assume(h₉₈₁: a ∈ₛₑₜ domain C₂)
      have h₉₈₂: ∃ (b: U₂.Particular), b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₉₂ h₉₈₁
      have ⟨(b: U₂.Particular), (h₉₈₃: b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ))⟩ := exists_elim h₉₈₂
      have h₉₈₄: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₉₆, b
      have h₉₈₅: b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₉₈₄ h₉₈₃
      have h₉₈₆: ∃ (b: U₂.Particular), b ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by exists_intro h₉₈₅, b
      have h₉₈₇: a ∈ₛₑₜ domain C₁ := PC₀.deductive_eq_r2l h₉₁ h₉₈₆
      iterate h₉₈₇

    have h₉₉: a ∈ₛₑₜ domain C₁ ↔ a ∈ₛₑₜ domain C₂ := by iff_intro h₉₇, h₉₈
    iterate h₉₉

  have h₁₀: domain C₁ =ₛₑₜ domain C₂ := PC₀.deductive_eq_r2l h₆ h₉
  iterate h₁₀

-- Domain as a congruent unary operation from correspondences to sets.
noncomputable def domain_operation (U₁: Universal) (U₂: Universal): CongruentUnaryOperation (U₁ ➞ᶜ U₂) (𝐒𝐞𝐭 U₁) :=
  let op: U₁ ⭢ᶜ U₂ → Set U₁ := domain
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (domain C₁ =ₛₑₜ domain C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    have h₁: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → domain C₁ =ₛₑₜ domain C₂' := by forall_elim domain_cong, C₁
    have h₂: C₁ =→ᶜ C₂ → domain C₁ =ₛₑₜ domain C₂ := by forall_elim h₁, C₂
    assume(h₃: C₁ =→ᶜ C₂)
    have h₄: domain C₁ =ₛₑₜ domain C₂ := by modus_ponens h₂, h₃
    iterate h₄
  { op := op, cong := cong }

end Correspondences

end Universe
