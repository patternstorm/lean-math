import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema

namespace Logic

namespace PC₁

structure CongruentBinaryPredicate (U₁: Universal) (U₂: Universal): Type where
  pred: U₁.Particular → CongruentUnaryPredicate U₂
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x =₍U₁₎ y → ((pred x).pred z ↔ (pred y).pred z)

end PC₁

end Logic
