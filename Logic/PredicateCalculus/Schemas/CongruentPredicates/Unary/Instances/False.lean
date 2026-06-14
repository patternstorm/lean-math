import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

def false (U: Universal): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ False)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (False ↔ False) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h: a =₍U₎ b)
    have h₁: False → False := by
      assume(h₁₁: False)
      iterate h₁₁
    have h₂: False ↔ False := by iff_intro h₁, h₁
    iterate h₂
  { pred := pred, cong := cong }

end PC₁

end Logic
