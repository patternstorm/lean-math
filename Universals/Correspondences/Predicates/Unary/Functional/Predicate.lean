import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Apply.Operation
import Universals.Correspondences.Operations.Unary.Domain.Operation

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets

axiom is_functional: U₁ ⭢ᶜ U₂ → Prop
axiom is_functional_def: ∀ (C: U₁ ⭢ᶜ U₂), is_functional C ↔
  ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C → is_singleton (C (↑{a}ₛₑₜ))

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
def functional_predicate (U₁: Universal) (U₂: Universal): CongruentUnaryPredicate (U₁ ➞ᶜ U₂) :=
  let pred: U₁ ⭢ᶜ U₂ → Prop := (C: U₁ ⭢ᶜ U₂ ↦ is_functional C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (is_functional C₁ ↔ is_functional C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    assume(h₁: C₁ =→ᶜ C₂)

    -- Unfold is_functional for both correspondences
    have h₂: is_functional C₁ ↔ ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ → is_singleton (C₁ (↑{a}ₛₑₜ)) := by forall_elim is_functional_def, C₁
    have h₃: is_functional C₂ ↔ ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ → is_singleton (C₂ (↑{a}ₛₑₜ)) := by forall_elim is_functional_def, C₂

    -- From C₁ =→ᶜ C₂: apply congruence and domain congruence
    have h₄: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (S: Set U₁), C₁ S =ₛₑₜ apply C₂' S := by forall_elim apply_cong_first, C₁
    have h₅: C₁ =→ᶜ C₂ → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by forall_elim h₄, C₂
    have h₆: ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by modus_ponens h₅, h₁

    have h₇: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → domain C₁ =ₛₑₜ domain C₂' := by forall_elim domain_cong, C₁
    have h₈: C₁ =→ᶜ C₂ → domain C₁ =ₛₑₜ domain C₂ := by forall_elim h₇, C₂
    have h₉: domain C₁ =ₛₑₜ domain C₂ := by modus_ponens h₈, h₁

    -- domain membership equivalence
    have h₁₀: ∀ (S: Set U₁), domain C₁ =ₛₑₜ S ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ S) := by forall_elim set_extensionality, domain C₁
    have h₁₁: domain C₁ =ₛₑₜ domain C₂ ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ domain C₂) := by forall_elim h₁₀, domain C₂
    have h₁₂: ∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ domain C₂ := PC₀.deductive_eq_l2r h₁₁ h₉

    -- Forward: is_functional C₁ → is_functional C₂
    have h₁₃: is_functional C₁ → is_functional C₂ := by
      assume(h₁₃₁: is_functional C₁)
      have h₁₃₂: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ → is_singleton (C₁ (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₂ h₁₃₁
      have h₁₃₃: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ → is_singleton (C₂ (↑{a}ₛₑₜ)) := by forall_intro
        variable(a: U₁.Particular)
        assume(h₁₃₃₁: a ∈ₛₑₜ domain C₂)
        -- Transfer domain membership
        have h₁₃₃₂: a ∈ₛₑₜ domain C₁ ↔ a ∈ₛₑₜ domain C₂ := by forall_elim h₁₂, a
        have h₁₃₃₃: a ∈ₛₑₜ domain C₁ := PC₀.deductive_eq_r2l h₁₃₃₂ h₁₃₃₁
        -- Apply hypothesis
        have h₁₃₃₄: a ∈ₛₑₜ domain C₁ → is_singleton (C₁ (↑{a}ₛₑₜ)) := by forall_elim h₁₃₂, a
        have h₁₃₃₅: is_singleton (C₁ (↑{a}ₛₑₜ)) := by modus_ponens h₁₃₃₄, h₁₃₃₃
        -- Transfer via apply congruence + singleton congruence
        have h₁₃₃₆: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆, (↑{a}ₛₑₜ)
        have h₁₃₃₇: ∀ (S₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ S₂ → (is_singleton (C₁ (↑{a}ₛₑₜ)) ↔ is_singleton S₂) := by forall_elim singleton_predicate.cong, (C₁ (↑{a}ₛₑₜ))
        have h₁₃₃₈: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) → (is_singleton (C₁ (↑{a}ₛₑₜ)) ↔ is_singleton (C₂ (↑{a}ₛₑₜ))) := by forall_elim h₁₃₃₇, (C₂ (↑{a}ₛₑₜ))
        have h₁₃₃₉: is_singleton (C₁ (↑{a}ₛₑₜ)) ↔ is_singleton (C₂ (↑{a}ₛₑₜ)) := by modus_ponens h₁₃₃₈, h₁₃₃₆
        have h₁₃₃₁₀: is_singleton (C₂ (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₁₃₃₉ h₁₃₃₅
        iterate h₁₃₃₁₀
      have h₁₃₄: is_functional C₂ := PC₀.deductive_eq_r2l h₃ h₁₃₃
      iterate h₁₃₄

    -- Backward: is_functional C₂ → is_functional C₁
    have h₁₄: is_functional C₂ → is_functional C₁ := by
      assume(h₁₄₁: is_functional C₂)
      have h₁₄₂: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ → is_singleton (C₂ (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₃ h₁₄₁
      have h₁₄₃: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ → is_singleton (C₁ (↑{a}ₛₑₜ)) := by forall_intro
        variable(a: U₁.Particular)
        assume(h₁₄₃₁: a ∈ₛₑₜ domain C₁)
        -- Transfer domain membership
        have h₁₄₃₂: a ∈ₛₑₜ domain C₁ ↔ a ∈ₛₑₜ domain C₂ := by forall_elim h₁₂, a
        have h₁₄₃₃: a ∈ₛₑₜ domain C₂ := PC₀.deductive_eq_l2r h₁₄₃₂ h₁₄₃₁
        -- Apply hypothesis
        have h₁₄₃₄: a ∈ₛₑₜ domain C₂ → is_singleton (C₂ (↑{a}ₛₑₜ)) := by forall_elim h₁₄₂, a
        have h₁₄₃₅: is_singleton (C₂ (↑{a}ₛₑₜ)) := by modus_ponens h₁₄₃₄, h₁₄₃₃
        -- Transfer via apply congruence + singleton congruence
        have h₁₄₃₆: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆, (↑{a}ₛₑₜ)
        have h₁₄₃₇: ∀ (S₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ S₂ → (is_singleton (C₁ (↑{a}ₛₑₜ)) ↔ is_singleton S₂) := by forall_elim singleton_predicate.cong, (C₁ (↑{a}ₛₑₜ))
        have h₁₄₃₈: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) → (is_singleton (C₁ (↑{a}ₛₑₜ)) ↔ is_singleton (C₂ (↑{a}ₛₑₜ))) := by forall_elim h₁₄₃₇, (C₂ (↑{a}ₛₑₜ))
        have h₁₄₃₉: is_singleton (C₁ (↑{a}ₛₑₜ)) ↔ is_singleton (C₂ (↑{a}ₛₑₜ)) := by modus_ponens h₁₄₃₈, h₁₄₃₆
        have h₁₄₃₁₀: is_singleton (C₁ (↑{a}ₛₑₜ)) := PC₀.deductive_eq_r2l h₁₄₃₉ h₁₄₃₅
        iterate h₁₄₃₁₀
      have h₁₄₄: is_functional C₁ := PC₀.deductive_eq_r2l h₂ h₁₄₃
      iterate h₁₄₄

    have h₁₅: is_functional C₁ ↔ is_functional C₂ := by iff_intro h₁₃, h₁₄
    iterate h₁₅
  { pred := pred, cong := cong }

end Correspondences

end Universe
