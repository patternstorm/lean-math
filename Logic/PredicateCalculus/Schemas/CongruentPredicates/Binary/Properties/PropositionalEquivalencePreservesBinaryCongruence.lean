import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- # Propositional equivalence preserves binary congruence.
--
-- If two binary predicates `P` and `Q` over Universals `U₁`, `U₂` are
-- propositionally equivalent at every point (`∀ x y, P x y ↔ Q x y`), then
-- combined congruence of `Q` implies combined congruence of `P`.
-- Equivalently: combined congruence is a property invariant under
-- propositional equivalence between binary predicates.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem propositional_equivalence_preserves_binary_congruence
    {U₁ U₂: Universal} (P Q: U₁.Particular → U₂.Particular → Prop)
    (equiv: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), P x y ↔ Q x y)
    (Q_cong: ∀ (x₁ x₂: U₁.Particular), ∀ (y₁ y₂: U₂.Particular),
              x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → (Q x₁ y₁ ↔ Q x₂ y₂)):
    ∀ (x₁ x₂: U₁.Particular), ∀ (y₁ y₂: U₂.Particular),
      x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → (P x₁ y₁ ↔ P x₂ y₂) := by forall_intro
  variable(a₁: U₁.Particular)
  variable(a₂: U₁.Particular)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  assume(h₁: a₁ =₍U₁₎ a₂)
  assume(h₂: b₁ =₍U₂₎ b₂)
  have h₃: P a₁ b₁ ↔ Q a₁ b₁ := by forall_elim equiv, a₁, b₁
  have h₄: P a₂ b₂ ↔ Q a₂ b₂ := by forall_elim equiv, a₂, b₂
  have h₅: a₁ =₍U₁₎ a₂ → b₁ =₍U₂₎ b₂ → (Q a₁ b₁ ↔ Q a₂ b₂) := by forall_elim Q_cong, a₁, a₂, b₁, b₂
  have h₆: b₁ =₍U₂₎ b₂ → (Q a₁ b₁ ↔ Q a₂ b₂) := by modus_ponens h₅, h₁
  have h₇: Q a₁ b₁ ↔ Q a₂ b₂ := by modus_ponens h₆, h₂
  have h₈: P a₁ b₁ → P a₂ b₂ := by
    assume(h₈₁: P a₁ b₁)
    have h₈₂: Q a₁ b₁ := PC₀.deductive_eq_l2r h₃ h₈₁
    have h₈₃: Q a₂ b₂ := PC₀.deductive_eq_l2r h₇ h₈₂
    have h₈₄: P a₂ b₂ := PC₀.deductive_eq_r2l h₄ h₈₃
    iterate h₈₄
  have h₉: P a₂ b₂ → P a₁ b₁ := by
    assume(h₉₁: P a₂ b₂)
    have h₉₂: Q a₂ b₂ := PC₀.deductive_eq_l2r h₄ h₉₁
    have h₉₃: Q a₁ b₁ := PC₀.deductive_eq_r2l h₇ h₉₂
    have h₉₄: P a₁ b₁ := PC₀.deductive_eq_r2l h₃ h₉₃
    iterate h₉₄
  have h₁₀: P a₁ b₁ ↔ P a₂ b₂ := by iff_intro h₈, h₉
  iterate h₁₀

end PC₁

end Logic
