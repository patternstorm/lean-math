import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Schemas.Universal.Schema

namespace Logic

namespace PC₁

def true (U: Universal): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ True)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (True ↔ True) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h: a =₍U₎ b)
    have h₁: True → True := by
      assume(h₁₁: True)
      iterate h₁₁
    have h₂: True ↔ True := by iff_intro h₁, h₁
    iterate h₂
  { pred := pred, cong := cong }

end PC₁

end Logic
