import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.CoClassification.Operation
import Universals.Relations.Predicates.Unary.PartialEquivalenceRelation.Predicate

/-!
# Injective Correspondences

A correspondence is injective if its co-classification relation is a partial
equivalence relation (symmetric and transitive). Since co-classification is
always symmetric, injectivity reduces to transitivity of co-classification.

```
is_injective C ↔ is_partial_equivalence_relation (co_classification C)
```
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets
open Relations

axiom is_injective: U₁ ⭢ᶜ U₂ → Prop
axiom is_injective_def: ∀ (C: U₁ ⭢ᶜ U₂), is_injective C ↔
  is_partial_equivalence_relation (co_classification C)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
def injective_predicate (U₁: Universal) (U₂: Universal): CongruentUnaryPredicate (U₁ ➞ᶜ U₂) :=
  let pred: U₁ ⭢ᶜ U₂ → Prop := (C: U₁ ⭢ᶜ U₂ ↦ is_injective C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (is_injective C₁ ↔ is_injective C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    assume(h₁: C₁ =→ᶜ C₂)

    -- Unfold is_injective for both correspondences
    have h₂: is_injective C₁ ↔ is_partial_equivalence_relation (co_classification C₁) := by forall_elim is_injective_def, C₁
    have h₃: is_injective C₂ ↔ is_partial_equivalence_relation (co_classification C₂) := by forall_elim is_injective_def, C₂

    -- co_classification_cong: C₁ =→ᶜ C₂ → co_classification C₁ =ᵣₑₗ co_classification C₂
    have h₄: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → co_classification C₁ =ᵣₑₗ co_classification C₂' := by forall_elim co_classification_cong, C₁
    have h₅: C₁ =→ᶜ C₂ → co_classification C₁ =ᵣₑₗ co_classification C₂ := by forall_elim h₄, C₂
    have h₆: co_classification C₁ =ᵣₑₗ co_classification C₂ := by modus_ponens h₅, h₁

    -- PER predicate congruence: R₁ =ᵣₑₗ R₂ → (is_per R₁ ↔ is_per R₂)
    have h₇: ∀ (R₂: Rel U₂ U₂), co_classification C₁ =ᵣₑₗ R₂ → (is_partial_equivalence_relation (co_classification C₁) ↔ is_partial_equivalence_relation R₂) := by forall_elim (partial_equivalence_relation_predicate U₂).cong, co_classification C₁
    have h₈: co_classification C₁ =ᵣₑₗ co_classification C₂ → (is_partial_equivalence_relation (co_classification C₁) ↔ is_partial_equivalence_relation (co_classification C₂)) := by forall_elim h₇, co_classification C₂
    have h₉: is_partial_equivalence_relation (co_classification C₁) ↔ is_partial_equivalence_relation (co_classification C₂) := by modus_ponens h₈, h₆

    -- Chain: is_injective C₁ ↔ is_per (co_class C₁) ↔ is_per (co_class C₂) ↔ is_injective C₂
    have h₁₀: is_injective C₁ → is_injective C₂ := by
      assume(h₁₀₁: is_injective C₁)
      have h₁₀₂: is_partial_equivalence_relation (co_classification C₁) := PC₀.deductive_eq_l2r h₂ h₁₀₁
      have h₁₀₃: is_partial_equivalence_relation (co_classification C₂) := PC₀.deductive_eq_l2r h₉ h₁₀₂
      have h₁₀₄: is_injective C₂ := PC₀.deductive_eq_r2l h₃ h₁₀₃
      iterate h₁₀₄

    have h₁₁: is_injective C₂ → is_injective C₁ := by
      assume(h₁₁₁: is_injective C₂)
      have h₁₁₂: is_partial_equivalence_relation (co_classification C₂) := PC₀.deductive_eq_l2r h₃ h₁₁₁
      have h₁₁₃: is_partial_equivalence_relation (co_classification C₁) := PC₀.deductive_eq_r2l h₉ h₁₁₂
      have h₁₁₄: is_injective C₁ := PC₀.deductive_eq_r2l h₂ h₁₁₃
      iterate h₁₁₄

    have h₁₂: is_injective C₁ ↔ is_injective C₂ := by iff_intro h₁₀, h₁₁
    iterate h₁₂
  { pred := pred, cong := cong }

end Correspondences

end Universe
