import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- # Propositional equivalence preserves congruence (unary).
--
-- If two unary predicates `P` and `Q` over a Universal `U` are propositionally
-- equivalent at every point (`∀ x, P x ↔ Q x`), then congruence of `Q`
-- implies congruence of `P`. Equivalently: congruence is a property invariant
-- under propositional equivalence between predicates.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem propositional_equivalence_preserves_congruence
    {U: Universal} (P Q: U.Particular → Prop)
    (equiv: ∀ (x: U.Particular), P x ↔ Q x)
    (Q_cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (Q x ↔ Q y)):
    ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (P x ↔ P y) := by forall_intro
  variable(a: U.Particular)
  variable(b: U.Particular)
  assume(h₁: a =₍U₎ b)
  have h₂: P a ↔ Q a := by forall_elim equiv, a
  have h₃: a =₍U₎ b → (Q a ↔ Q b) := by forall_elim Q_cong, a, b
  have h₄: Q a ↔ Q b := by modus_ponens h₃, h₁
  have h₅: P b ↔ Q b := by forall_elim equiv, b
  have h₆: P a → P b := by
    assume(h₆₁: P a)
    have h₆₂: Q a := PC₀.deductive_eq_l2r h₂ h₆₁
    have h₆₃: Q b := PC₀.deductive_eq_l2r h₄ h₆₂
    have h₆₄: P b := PC₀.deductive_eq_r2l h₅ h₆₃
    iterate h₆₄
  have h₇: P b → P a := by
    assume(h₇₁: P b)
    have h₇₂: Q b := PC₀.deductive_eq_l2r h₅ h₇₁
    have h₇₃: Q a := PC₀.deductive_eq_r2l h₄ h₇₂
    have h₇₄: P a := PC₀.deductive_eq_r2l h₂ h₇₃
    iterate h₇₄
  have h₈: P a ↔ P b := by iff_intro h₆, h₇
  iterate h₈

end PC₁

end Logic
