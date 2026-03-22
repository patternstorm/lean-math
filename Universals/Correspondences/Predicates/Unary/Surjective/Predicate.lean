import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Range.Operation

/-!
# Correspondence Surjectivity

A correspondence is surjective if every target particular is in its range —
every target particular is co-classified by at least one source particular.

```
surjective C ↔ ∀ b : U₂.Particular, b ∈ₛₑₜ range C
```
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets

axiom is_surjective: U₁ ⭢ᶜ U₂ → Prop
axiom is_surjective_def: ∀ (C: U₁ ⭢ᶜ U₂), is_surjective C ↔ ∀ (b: U₂.Particular), b ∈ₛₑₜ range C

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
def surjective_predicate (U₁: Universal) (U₂: Universal): CongruentUnaryPredicate (U₁ ➞ᶜ U₂) :=
  let pred: U₁ ⭢ᶜ U₂ → Prop := (C: U₁ ⭢ᶜ U₂ ↦ is_surjective C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (is_surjective C₁ ↔ is_surjective C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    assume(h₁: C₁ =→ᶜ C₂)

    -- Unfold is_surjective for both correspondences
    have h₂: is_surjective C₁ ↔ ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₁ := by forall_elim is_surjective_def, C₁
    have h₃: is_surjective C₂ ↔ ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₂ := by forall_elim is_surjective_def, C₂

    -- range C₁ =ₛₑₜ range C₂, hence membership equivalence
    have h₄: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → range C₁ =ₛₑₜ range C₂' := by forall_elim range_cong, C₁
    have h₅: C₁ =→ᶜ C₂ → range C₁ =ₛₑₜ range C₂ := by forall_elim h₄, C₂
    have h₆: range C₁ =ₛₑₜ range C₂ := by modus_ponens h₅, h₁
    have h₇: ∀ (S: Set U₂), range C₁ =ₛₑₜ S ↔ (∀ (x: U₂.Particular), x ∈ₛₑₜ range C₁ ↔ x ∈ₛₑₜ S) := by forall_elim set_extensionality, range C₁
    have h₈: range C₁ =ₛₑₜ range C₂ ↔ (∀ (x: U₂.Particular), x ∈ₛₑₜ range C₁ ↔ x ∈ₛₑₜ range C₂) := by forall_elim h₇, range C₂
    have h₉: ∀ (x: U₂.Particular), x ∈ₛₑₜ range C₁ ↔ x ∈ₛₑₜ range C₂ := PC₀.deductive_eq_l2r h₈ h₆

    -- Forward: is_surjective C₁ → is_surjective C₂
    have h₁₀: is_surjective C₁ → is_surjective C₂ := by
      assume(h₁₀₁: is_surjective C₁)
      have h₁₀₂: ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₁ := PC₀.deductive_eq_l2r h₂ h₁₀₁
      have h₁₀₃: ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₂ := by forall_intro
        variable(b: U₂.Particular)
        have h₁₀₃₁: b ∈ₛₑₜ range C₁ := by forall_elim h₁₀₂, b
        have h₁₀₃₂: b ∈ₛₑₜ range C₁ ↔ b ∈ₛₑₜ range C₂ := by forall_elim h₉, b
        have h₁₀₃₃: b ∈ₛₑₜ range C₂ := PC₀.deductive_eq_l2r h₁₀₃₂ h₁₀₃₁
        iterate h₁₀₃₃
      have h₁₀₄: is_surjective C₂ := PC₀.deductive_eq_r2l h₃ h₁₀₃
      iterate h₁₀₄

    -- Backward: is_surjective C₂ → is_surjective C₁
    have h₁₁: is_surjective C₂ → is_surjective C₁ := by
      assume(h₁₁₁: is_surjective C₂)
      have h₁₁₂: ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₂ := PC₀.deductive_eq_l2r h₃ h₁₁₁
      have h₁₁₃: ∀ (b: U₂.Particular), b ∈ₛₑₜ range C₁ := by forall_intro
        variable(b: U₂.Particular)
        have h₁₁₃₁: b ∈ₛₑₜ range C₂ := by forall_elim h₁₁₂, b
        have h₁₁₃₂: b ∈ₛₑₜ range C₁ ↔ b ∈ₛₑₜ range C₂ := by forall_elim h₉, b
        have h₁₁₃₃: b ∈ₛₑₜ range C₁ := PC₀.deductive_eq_r2l h₁₁₃₂ h₁₁₃₁
        iterate h₁₁₃₃
      have h₁₁₄: is_surjective C₁ := PC₀.deductive_eq_r2l h₂ h₁₁₃
      iterate h₁₁₄

    have h₁₂: is_surjective C₁ ↔ is_surjective C₂ := by iff_intro h₁₀, h₁₁
    iterate h₁₂
  { pred := pred, cong := cong }

end Correspondences

end Universe
