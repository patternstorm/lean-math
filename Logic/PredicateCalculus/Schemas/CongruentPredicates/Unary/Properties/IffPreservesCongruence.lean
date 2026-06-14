import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

-- The biconditional of two congruent unary predicates is itself congruent.
--
-- This is the "iff preserves congruence" theorem: given two `CongruentUnaryPredicate`s
-- `P` and `Q`, the predicate `(x ↦ P.pred x ↔ Q.pred x)` is congruent.
-- Distinct from `propositional_equivalence_preserves_congruence`, which transports
-- congruence from one predicate to another along a pointwise iff between them.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
def iff_preserves_congruence (P Q: CongruentUnaryPredicate U): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ P.pred x ↔ Q.pred x)
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
    -- Forward: (P.pred a ↔ Q.pred a) → (P.pred b ↔ Q.pred b)
    have h₈: (P.pred a ↔ Q.pred a) → (P.pred b ↔ Q.pred b) := by
      assume(h₈₁: P.pred a ↔ Q.pred a)
      -- Sub-forward: P.pred b → Q.pred b
      have h₈₂: P.pred b → Q.pred b := by
        assume(h₈₂₁: P.pred b)
        have h₈₂₂: P.pred a := PC₀.deductive_eq_r2l h₄ h₈₂₁
        have h₈₂₃: Q.pred a := PC₀.deductive_eq_l2r h₈₁ h₈₂₂
        have h₈₂₄: Q.pred b := PC₀.deductive_eq_l2r h₇ h₈₂₃
        iterate h₈₂₄
      -- Sub-backward: Q.pred b → P.pred b
      have h₈₃: Q.pred b → P.pred b := by
        assume(h₈₃₁: Q.pred b)
        have h₈₃₂: Q.pred a := PC₀.deductive_eq_r2l h₇ h₈₃₁
        have h₈₃₃: P.pred a := PC₀.deductive_eq_r2l h₈₁ h₈₃₂
        have h₈₃₄: P.pred b := PC₀.deductive_eq_l2r h₄ h₈₃₃
        iterate h₈₃₄
      have h₈₄: P.pred b ↔ Q.pred b := by iff_intro h₈₂, h₈₃
      iterate h₈₄
    -- Backward: (P.pred b ↔ Q.pred b) → (P.pred a ↔ Q.pred a)
    have h₉: (P.pred b ↔ Q.pred b) → (P.pred a ↔ Q.pred a) := by
      assume(h₉₁: P.pred b ↔ Q.pred b)
      -- Sub-forward: P.pred a → Q.pred a
      have h₉₂: P.pred a → Q.pred a := by
        assume(h₉₂₁: P.pred a)
        have h₉₂₂: P.pred b := PC₀.deductive_eq_l2r h₄ h₉₂₁
        have h₉₂₃: Q.pred b := PC₀.deductive_eq_l2r h₉₁ h₉₂₂
        have h₉₂₄: Q.pred a := PC₀.deductive_eq_r2l h₇ h₉₂₃
        iterate h₉₂₄
      -- Sub-backward: Q.pred a → P.pred a
      have h₉₃: Q.pred a → P.pred a := by
        assume(h₉₃₁: Q.pred a)
        have h₉₃₂: Q.pred b := PC₀.deductive_eq_l2r h₇ h₉₃₁
        have h₉₃₃: P.pred b := PC₀.deductive_eq_r2l h₉₁ h₉₃₂
        have h₉₃₄: P.pred a := PC₀.deductive_eq_r2l h₄ h₉₃₃
        iterate h₉₃₄
      have h₉₄: P.pred a ↔ Q.pred a := by iff_intro h₉₂, h₉₃
      iterate h₉₄
    have h₁₀: pred a ↔ pred b := by iff_intro h₈, h₉
    iterate h₁₀
  { pred := pred, cong := cong }

instance congruent_iff {U: Universal} {P Q: U.Particular → Prop} [p: CongruentUnary U P] [q: CongruentUnary U Q]:
    CongruentUnary U (x: U.Particular ↦ P x ↔ Q x) where
  cong := (iff_preserves_congruence { pred := P, cong := p.cong } { pred := Q, cong := q.cong }).cong

end PC₁

end Logic
