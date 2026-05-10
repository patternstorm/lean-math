import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema

namespace Logic

namespace PC₁

open ND

-- # Constant Predicate
-- Any proposition A, viewed as a predicate that ignores its argument,
-- is trivially congruent because A ↔ A always holds.

def constant_predicate {U: Universal} (A: Prop): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ A)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (A ↔ A) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h₁: a =₍U₎ b)
    have h₂: A → A := by
      assume(h₁₁: A)
      iterate h₁₁
    have h₃: A ↔ A := by iff_intro h₂, h₂
    iterate h₃
  { pred := pred, cong := cong }

instance (priority := 100) congruent_constant {U: Universal} {A: Prop}:
    CongruentUnary U (_: U.Particular ↦ A) where
  cong := (constant_predicate A).cong

end PC₁

end Logic
