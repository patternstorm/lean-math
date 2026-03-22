import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Domain.Operation

/-!
# Correspondence Totality

A correspondence is total if every source particular is in its domain —
every source particular co-classifies at least one target particular.

```
total C ↔ ∀ a : U₁.Particular, a ∈ₛₑₜ domain C
```
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets

axiom is_total: U₁ ⭢ᶜ U₂ → Prop
axiom is_total_def: ∀ (C: U₁ ⭢ᶜ U₂), is_total C ↔ ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
def total_predicate (U₁: Universal) (U₂: Universal): CongruentUnaryPredicate (U₁ ➞ᶜ U₂) :=
  let pred: U₁ ⭢ᶜ U₂ → Prop := (C: U₁ ⭢ᶜ U₂ ↦ is_total C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (is_total C₁ ↔ is_total C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    assume(h₁: C₁ =→ᶜ C₂)

    -- Unfold is_total for both correspondences
    have h₂: is_total C₁ ↔ ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ := by forall_elim is_total_def, C₁
    have h₃: is_total C₂ ↔ ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ := by forall_elim is_total_def, C₂

    -- domain C₁ =ₛₑₜ domain C₂, hence membership equivalence
    have h₄: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → domain C₁ =ₛₑₜ domain C₂' := by forall_elim domain_cong, C₁
    have h₅: C₁ =→ᶜ C₂ → domain C₁ =ₛₑₜ domain C₂ := by forall_elim h₄, C₂
    have h₆: domain C₁ =ₛₑₜ domain C₂ := by modus_ponens h₅, h₁
    have h₇: ∀ (S: Set U₁), domain C₁ =ₛₑₜ S ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ S) := by forall_elim set_extensionality, domain C₁
    have h₈: domain C₁ =ₛₑₜ domain C₂ ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ domain C₂) := by forall_elim h₇, domain C₂
    have h₉: ∀ (x: U₁.Particular), x ∈ₛₑₜ domain C₁ ↔ x ∈ₛₑₜ domain C₂ := PC₀.deductive_eq_l2r h₈ h₆

    -- Forward: is_total C₁ → is_total C₂
    have h₁₀: is_total C₁ → is_total C₂ := by
      assume(h₁₀₁: is_total C₁)
      have h₁₀₂: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ := PC₀.deductive_eq_l2r h₂ h₁₀₁
      have h₁₀₃: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ := by forall_intro
        variable(a: U₁.Particular)
        have h₁₀₃₁: a ∈ₛₑₜ domain C₁ := by forall_elim h₁₀₂, a
        have h₁₀₃₂: a ∈ₛₑₜ domain C₁ ↔ a ∈ₛₑₜ domain C₂ := by forall_elim h₉, a
        have h₁₀₃₃: a ∈ₛₑₜ domain C₂ := PC₀.deductive_eq_l2r h₁₀₃₂ h₁₀₃₁
        iterate h₁₀₃₃
      have h₁₀₄: is_total C₂ := PC₀.deductive_eq_r2l h₃ h₁₀₃
      iterate h₁₀₄

    -- Backward: is_total C₂ → is_total C₁
    have h₁₁: is_total C₂ → is_total C₁ := by
      assume(h₁₁₁: is_total C₂)
      have h₁₁₂: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₂ := PC₀.deductive_eq_l2r h₃ h₁₁₁
      have h₁₁₃: ∀ (a: U₁.Particular), a ∈ₛₑₜ domain C₁ := by forall_intro
        variable(a: U₁.Particular)
        have h₁₁₃₁: a ∈ₛₑₜ domain C₂ := by forall_elim h₁₁₂, a
        have h₁₁₃₂: a ∈ₛₑₜ domain C₁ ↔ a ∈ₛₑₜ domain C₂ := by forall_elim h₉, a
        have h₁₁₃₃: a ∈ₛₑₜ domain C₁ := PC₀.deductive_eq_r2l h₁₁₃₂ h₁₁₃₁
        iterate h₁₁₃₃
      have h₁₁₄: is_total C₁ := PC₀.deductive_eq_r2l h₂ h₁₁₃
      iterate h₁₁₄

    have h₁₂: is_total C₁ ↔ is_total C₂ := by iff_intro h₁₀, h₁₁
    iterate h₁₂
  { pred := pred, cong := cong }

end Correspondences

end Universe
