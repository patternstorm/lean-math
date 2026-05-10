import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

-- The conjunction of two congruent unary predicates is itself congruent.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
def conjunction_preserves_congruence (P Q: CongruentUnaryPredicate U): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ P.pred x ∧ Q.pred x)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (pred x ↔ pred y) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h₁: a =₍U₎ b)
    -- Unfold P.cong for a, b
    have h₂: ∀ (y: U.Particular), a =₍U₎ y → (P.pred a ↔ P.pred y) := by forall_elim P.cong, a
    have h₃: a =₍U₎ b → (P.pred a ↔ P.pred b) := by forall_elim h₂, b
    have h₄: P.pred a ↔ P.pred b := by modus_ponens h₃, h₁
    -- Unfold Q.cong for a, b
    have h₅: ∀ (y: U.Particular), a =₍U₎ y → (Q.pred a ↔ Q.pred y) := by forall_elim Q.cong, a
    have h₆: a =₍U₎ b → (Q.pred a ↔ Q.pred b) := by forall_elim h₅, b
    have h₇: Q.pred a ↔ Q.pred b := by modus_ponens h₆, h₁
    -- Forward: P a ∧ Q a → P b ∧ Q b
    have h₈: P.pred a ∧ Q.pred a → P.pred b ∧ Q.pred b := by
      assume(h₈₁: P.pred a ∧ Q.pred a)
      have h₈₂: P.pred a := by and_elim h₈₁
      have h₈₃: Q.pred a := by and_elim h₈₁
      have h₈₄: P.pred b := PC₀.deductive_eq_l2r h₄ h₈₂
      have h₈₅: Q.pred b := PC₀.deductive_eq_l2r h₇ h₈₃
      have h₈₆: P.pred b ∧ Q.pred b := by and_intro h₈₄, h₈₅
      iterate h₈₆
    -- Backward: P b ∧ Q b → P a ∧ Q a
    have h₉: P.pred b ∧ Q.pred b → P.pred a ∧ Q.pred a := by
      assume(h₉₁: P.pred b ∧ Q.pred b)
      have h₉₂: P.pred b := by and_elim h₉₁
      have h₉₃: Q.pred b := by and_elim h₉₁
      have h₉₄: P.pred a := PC₀.deductive_eq_r2l h₄ h₉₂
      have h₉₅: Q.pred a := PC₀.deductive_eq_r2l h₇ h₉₃
      have h₉₆: P.pred a ∧ Q.pred a := by and_intro h₉₄, h₉₅
      iterate h₉₆
    have h₁₀: pred a ↔ pred b := by iff_intro h₈, h₉
    iterate h₁₀
  { pred := pred, cong := cong }

instance congruent_conjunction {U: Universal} {P Q: U.Particular → Prop} [p: CongruentUnary U P] [q: CongruentUnary U Q]:
    CongruentUnary U (x: U.Particular ↦ P x ∧ Q x) where
  cong := (conjunction_preserves_congruence { pred := P, cong := p.cong } { pred := Q, cong := q.cong }).cong

end PC₁

end Logic
