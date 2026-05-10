import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁


theorem negation_preserves_congruence (P: CongruentUnaryPredicate U):
  ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (¬P.pred x ↔ ¬P.pred y) := by forall_intro
    variable(u: U.Particular)
    variable(v: U.Particular)
    assume(h₁: u =₍U₎ v)
    have h₂: ∀ (y: U.Particular), u =₍U₎ y → (P.pred u ↔ P.pred y) := by forall_elim P.cong, u
    have h₃: u =₍U₎ v → (P.pred u ↔ P.pred v) := by forall_elim h₂, v
    have h₄: P.pred u ↔ P.pred v := by modus_ponens h₃, h₁
    have h₅: ¬P.pred u ↔ ¬P.pred v := PC₀.deductive_eq_l2r PC₀.iff_contrapositiveness h₄
    iterate h₅

instance congruent_negation {U: Universal} {P: U.Particular → Prop} [p: CongruentUnary U P]: CongruentUnary U (x: U.Particular ↦ ¬P x) where
  cong := negation_preserves_congruence { pred := P, cong := p.cong }

end PC₁

end Logic
