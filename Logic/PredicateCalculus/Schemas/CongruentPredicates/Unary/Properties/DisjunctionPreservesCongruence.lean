import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

-- The disjunction of two congruent unary predicates is itself congruent.
-- Proof by Kimi 2.6, 2026-05-10
def disjunction_preserves_congruence (P Q: CongruentUnaryPredicate U): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ P.pred x ∨ Q.pred x)
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
    -- Forward: P a ∨ Q a → P b ∨ Q b
    have h₈: P.pred a ∨ Q.pred a → P.pred b ∨ Q.pred b := by
      assume(h₈₁: P.pred a ∨ Q.pred a)
      have h₈₂: P.pred a → P.pred b ∨ Q.pred b := by
        assume(h₈₂₁: P.pred a)
        have h₈₂₂: P.pred b := PC₀.deductive_eq_l2r h₄ h₈₂₁
        have h₈₂₃: P.pred b ∨ Q.pred b := by or_intro h₈₂₂
        iterate h₈₂₃
      have h₈₃: Q.pred a → P.pred b ∨ Q.pred b := by
        assume(h₈₃₁: Q.pred a)
        have h₈₃₂: Q.pred b := PC₀.deductive_eq_l2r h₇ h₈₃₁
        have h₈₃₃: P.pred b ∨ Q.pred b := by or_intro h₈₃₂
        iterate h₈₃₃
      or_elimination h₈₁, h₈₂, h₈₃
    -- Backward: P b ∨ Q b → P a ∨ Q a
    have h₉: P.pred b ∨ Q.pred b → P.pred a ∨ Q.pred a := by
      assume(h₉₁: P.pred b ∨ Q.pred b)
      have h₉₂: P.pred b → P.pred a ∨ Q.pred a := by
        assume(h₉₂₁: P.pred b)
        have h₉₂₂: P.pred a := PC₀.deductive_eq_r2l h₄ h₉₂₁
        have h₉₂₃: P.pred a ∨ Q.pred a := by or_intro h₉₂₂
        iterate h₉₂₃
      have h₉₃: Q.pred b → P.pred a ∨ Q.pred a := by
        assume(h₉₃₁: Q.pred b)
        have h₉₃₂: Q.pred a := PC₀.deductive_eq_r2l h₇ h₉₃₁
        have h₉₃₃: P.pred a ∨ Q.pred a := by or_intro h₉₃₂
        iterate h₉₃₃
      or_elimination h₉₁, h₉₂, h₉₃
    have h₁₀: pred a ↔ pred b := by iff_intro h₈, h₉
    iterate h₁₀
  { pred := pred, cong := cong }

instance congruent_disjunction {U: Universal} {P Q: U.Particular → Prop} [p: CongruentUnary U P] [q: CongruentUnary U Q]:
    CongruentUnary U (x: U.Particular ↦ P x ∨ Q x) where
  cong := (disjunction_preserves_congruence { pred := P, cong := p.cong } { pred := Q, cong := q.cong }).cong

end PC₁

end Logic
