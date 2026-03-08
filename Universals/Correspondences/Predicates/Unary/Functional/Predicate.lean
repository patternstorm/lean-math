import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Apply.Operation
import Universals.Sets.Predicates.Unary.Singleton.Predicate

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets

axiom is_functional: Corr U₁ U₂ → Prop
axiom is_functional_def: ∀ (C: Corr U₁ U₂), is_functional C ↔ ∀ (a: U₁.Particular), is_singleton (apply C a)

-- Proof by GPT-5.4, 2026-03-08
def functional_predicate (U₁: Universal) (U₂: Universal): CongruentUnaryPredicate (CorrespondenceUniversal U₁ U₂) :=
  let pred: Corr U₁ U₂ → Prop := (C: Corr U₁ U₂ ↦ is_functional C)
  let cong: ∀ (C₁: Corr U₁ U₂), ∀ (C₂: Corr U₁ U₂), C₁ =₍CorrespondenceUniversal U₁ U₂₎ C₂ → (pred C₁ ↔ pred C₂) := by forall_intro
    variable(C₁: Corr U₁ U₂)
    variable(C₂: Corr U₁ U₂)
    assume(h₁: C₁ =→ᶜ C₂)
    have h₂: is_functional C₁ ↔ ∀ (a: U₁.Particular), is_singleton (apply C₁ a) := by forall_elim is_functional_def, C₁
    have h₃: is_functional C₂ ↔ ∀ (a: U₁.Particular), is_singleton (apply C₂ a) := by forall_elim is_functional_def, C₂
    have h₄: ∀ (a: U₁.Particular), is_singleton (apply C₁ a) → is_singleton (apply C₂ a) := by forall_intro
      variable(a: U₁.Particular)
      assume(h₄₁: is_singleton (apply C₁ a))
      have h₄₂₀: ∀ (a': U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ (apply C₁ a') ↔ (a' ⭢ᵃ S) ∈ₛₑₜ C₁ := by forall_elim apply_def, C₁
      have h₄₂: ∀ (S: Set U₂), S =ₛₑₜ (apply C₁ a) ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₁ := by forall_elim h₄₂₀, a
      have h₄₃₀: ∀ (a': U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ (apply C₂ a') ↔ (a' ⭢ᵃ S) ∈ₛₑₜ C₂ := by forall_elim apply_def, C₂
      have h₄₃: ∀ (S: Set U₂), S =ₛₑₜ (apply C₂ a) ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₂ := by forall_elim h₄₃₀, a
      have h₄₄: C₁ =ₛₑₜ C₂ := h₁
      have h₄₅₀: ∀ (S₂: Set (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂))), C₁ =ₛₑₜ S₂ ↔ ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), C₁.pred x ↔ S₂.pred x := by forall_elim Sets.eq_def, C₁
      have h₄₅: C₁ =ₛₑₜ C₂ ↔ ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), C₁.pred x ↔ C₂.pred x := by forall_elim h₄₅₀, C₂
      have h₄₆: ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), C₁.pred x ↔ C₂.pred x := PC₀.deductive_eq_l2r h₄₅ h₄₄
      have h₄₇: C₁.pred (a ⭢ᵃ (apply C₁ a)) ↔ C₂.pred (a ⭢ᵃ (apply C₁ a)) := by forall_elim h₄₆, (a ⭢ᵃ (apply C₁ a))
      have h₄₈: (apply C₁ a) =ₛₑₜ (apply C₁ a) := Sets.equality.refl (apply C₁ a)
      have h₄₉: (apply C₁ a) =ₛₑₜ (apply C₁ a) ↔ (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₁ := by forall_elim h₄₂, (apply C₁ a)
      have h₅₀: (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₁ := PC₀.deductive_eq_l2r h₄₉ h₄₈
      have h₅₀₁: (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₁ ↔ C₁.pred (a ⭢ᵃ (apply C₁ a)) := by
        have h₅₀₁₁: ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), x ∈ₛₑₜ C₁ ↔ C₁.pred x := by forall_elim mem_def, C₁
        have h₅₀₁₂: (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₁ ↔ C₁.pred (a ⭢ᵃ (apply C₁ a)) := by forall_elim h₅₀₁₁, (a ⭢ᵃ (apply C₁ a))
        iterate h₅₀₁₂
      have h₅₀₂: (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₂ ↔ C₂.pred (a ⭢ᵃ (apply C₁ a)) := by
        have h₅₀₂₁: ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), x ∈ₛₑₜ C₂ ↔ C₂.pred x := by forall_elim mem_def, C₂
        have h₅₀₂₂: (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₂ ↔ C₂.pred (a ⭢ᵃ (apply C₁ a)) := by forall_elim h₅₀₂₁, (a ⭢ᵃ (apply C₁ a))
        iterate h₅₀₂₂
      have h₅₀₃: C₁.pred (a ⭢ᵃ (apply C₁ a)) := PC₀.deductive_eq_l2r h₅₀₁ h₅₀
      have h₅₀₄: C₂.pred (a ⭢ᵃ (apply C₁ a)) := PC₀.deductive_eq_l2r h₄₇ h₅₀₃
      have h₅₁: (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₂ := PC₀.deductive_eq_r2l h₅₀₂ h₅₀₄
      have h₅₂: (apply C₁ a) =ₛₑₜ (apply C₂ a) ↔ (a ⭢ᵃ (apply C₁ a)) ∈ₛₑₜ C₂ := by forall_elim h₄₃, (apply C₁ a)
      have h₅₃: (apply C₁ a) =ₛₑₜ (apply C₂ a) := PC₀.deductive_eq_r2l h₅₂ h₅₁
      have h₅₄: is_singleton (apply C₁ a) ↔ is_singleton (apply C₂ a) := singleton_predicate.cong (apply C₁ a) (apply C₂ a) h₅₃
      have h₅₅: is_singleton (apply C₂ a) := PC₀.deductive_eq_l2r h₅₄ h₄₁
      iterate h₅₅

    have h₅: ∀ (a: U₁.Particular), is_singleton (apply C₂ a) → is_singleton (apply C₁ a) := by forall_intro
      variable(a: U₁.Particular)
      assume(h₅₁: is_singleton (apply C₂ a))
      have h₅₂₀: ∀ (a': U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ (apply C₁ a') ↔ (a' ⭢ᵃ S) ∈ₛₑₜ C₁ := by forall_elim apply_def, C₁
      have h₅₂: ∀ (S: Set U₂), S =ₛₑₜ (apply C₁ a) ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₁ := by forall_elim h₅₂₀, a
      have h₅₃₀: ∀ (a': U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ (apply C₂ a') ↔ (a' ⭢ᵃ S) ∈ₛₑₜ C₂ := by forall_elim apply_def, C₂
      have h₅₃: ∀ (S: Set U₂), S =ₛₑₜ (apply C₂ a) ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₂ := by forall_elim h₅₃₀, a
      have h₅₄: C₁ =ₛₑₜ C₂ := h₁
      have h₅₅₀: ∀ (S₂: Set (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂))), C₁ =ₛₑₜ S₂ ↔ ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), C₁.pred x ↔ S₂.pred x := by forall_elim Sets.eq_def, C₁
      have h₅₅: C₁ =ₛₑₜ C₂ ↔ ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), C₁.pred x ↔ C₂.pred x := by forall_elim h₅₅₀, C₂
      have h₅₆: ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), C₁.pred x ↔ C₂.pred x := PC₀.deductive_eq_l2r h₅₅ h₅₄
      have h₅₇: C₁.pred (a ⭢ᵃ (apply C₂ a)) ↔ C₂.pred (a ⭢ᵃ (apply C₂ a)) := by forall_elim h₅₆, (a ⭢ᵃ (apply C₂ a))
      have h₅₈: (apply C₂ a) =ₛₑₜ (apply C₂ a) := Sets.equality.refl (apply C₂ a)
      have h₅₉: (apply C₂ a) =ₛₑₜ (apply C₂ a) ↔ (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₂ := by forall_elim h₅₃, (apply C₂ a)
      have h₆₀: (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₂ := PC₀.deductive_eq_l2r h₅₉ h₅₈
      have h₆₀₁: (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₁ ↔ C₁.pred (a ⭢ᵃ (apply C₂ a)) := by
        have h₆₀₁₁: ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), x ∈ₛₑₜ C₁ ↔ C₁.pred x := by forall_elim mem_def, C₁
        have h₆₀₁₂: (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₁ ↔ C₁.pred (a ⭢ᵃ (apply C₂ a)) := by forall_elim h₆₀₁₁, (a ⭢ᵃ (apply C₂ a))
        iterate h₆₀₁₂
      have h₆₀₂: (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₂ ↔ C₂.pred (a ⭢ᵃ (apply C₂ a)) := by
        have h₆₀₂₁: ∀ (x: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)).Particular), x ∈ₛₑₜ C₂ ↔ C₂.pred x := by forall_elim mem_def, C₂
        have h₆₀₂₂: (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₂ ↔ C₂.pred (a ⭢ᵃ (apply C₂ a)) := by forall_elim h₆₀₂₁, (a ⭢ᵃ (apply C₂ a))
        iterate h₆₀₂₂
      have h₆₀₃: C₂.pred (a ⭢ᵃ (apply C₂ a)) := PC₀.deductive_eq_l2r h₆₀₂ h₆₀
      have h₆₀₄: C₁.pred (a ⭢ᵃ (apply C₂ a)) := PC₀.deductive_eq_r2l h₅₇ h₆₀₃
      have h₆₁: (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₁ := PC₀.deductive_eq_r2l h₆₀₁ h₆₀₄
      have h₆₂: (apply C₂ a) =ₛₑₜ (apply C₁ a) ↔ (a ⭢ᵃ (apply C₂ a)) ∈ₛₑₜ C₁ := by forall_elim h₅₂, (apply C₂ a)
      have h₆₃: (apply C₂ a) =ₛₑₜ (apply C₁ a) := PC₀.deductive_eq_r2l h₆₂ h₆₁
      have h₆₄: is_singleton (apply C₂ a) ↔ is_singleton (apply C₁ a) := singleton_predicate.cong (apply C₂ a) (apply C₁ a) h₆₃
      have h₆₅: is_singleton (apply C₁ a) := PC₀.deductive_eq_l2r h₆₄ h₅₁
      iterate h₆₅
    have h₆: (∀ (a: U₁.Particular), is_singleton (apply C₁ a)) → (∀ (a: U₁.Particular), is_singleton (apply C₂ a)) := by
      assume(h₆₁: ∀ (a: U₁.Particular), is_singleton (apply C₁ a))
      have h₆₂: ∀ (a: U₁.Particular), is_singleton (apply C₂ a) := by forall_intro
        variable(a: U₁.Particular)
        have h₆₃: is_singleton (apply C₁ a) := by forall_elim h₆₁, a
        have h₆₄: is_singleton (apply C₁ a) → is_singleton (apply C₂ a) := by forall_elim h₄, a
        have h₆₅: is_singleton (apply C₂ a) := by modus_ponens h₆₄, h₆₃
        iterate h₆₅
      iterate h₆₂
    have h₇: (∀ (a: U₁.Particular), is_singleton (apply C₂ a)) → (∀ (a: U₁.Particular), is_singleton (apply C₁ a)) := by
      assume(h₇₁: ∀ (a: U₁.Particular), is_singleton (apply C₂ a))
      have h₇₂: ∀ (a: U₁.Particular), is_singleton (apply C₁ a) := by forall_intro
        variable(a: U₁.Particular)
        have h₇₃: is_singleton (apply C₂ a) := by forall_elim h₇₁, a
        have h₇₄: is_singleton (apply C₂ a) → is_singleton (apply C₁ a) := by forall_elim h₅, a
        have h₇₅: is_singleton (apply C₁ a) := by modus_ponens h₇₄, h₇₃
        iterate h₇₅
      iterate h₇₂
    have h₈: (∀ (a: U₁.Particular), is_singleton (apply C₁ a)) ↔ (∀ (a: U₁.Particular), is_singleton (apply C₂ a)) := by iff_intro h₆, h₇
    have h₉: is_functional C₁ ↔ is_functional C₂ := by
      have h₉₁: is_functional C₁ → is_functional C₂ := by
        assume(h₉₁₁: is_functional C₁)
        have h₉₁₂: ∀ (a: U₁.Particular), is_singleton (apply C₁ a) := PC₀.deductive_eq_l2r h₂ h₉₁₁
        have h₉₁₃: ∀ (a: U₁.Particular), is_singleton (apply C₂ a) := PC₀.deductive_eq_l2r h₈ h₉₁₂
        have h₉₁₄: is_functional C₂ := PC₀.deductive_eq_r2l h₃ h₉₁₃
        iterate h₉₁₄
      have h₉₂: is_functional C₂ → is_functional C₁ := by
        assume(h₉₂₁: is_functional C₂)
        have h₉₂₂: ∀ (a: U₁.Particular), is_singleton (apply C₂ a) := PC₀.deductive_eq_l2r h₃ h₉₂₁
        have h₉₂₃: ∀ (a: U₁.Particular), is_singleton (apply C₁ a) := PC₀.deductive_eq_r2l h₈ h₉₂₂
        have h₉₂₄: is_functional C₁ := PC₀.deductive_eq_r2l h₂ h₉₂₃
        iterate h₉₂₄
      have h₉₃: is_functional C₁ ↔ is_functional C₂ := by iff_intro h₉₁, h₉₂
      iterate h₉₃
    iterate h₉
  { pred := pred, cong := cong }

end Correspondences

end Universe
