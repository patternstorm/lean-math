import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentOperations.Unary.Schema

namespace Logic

namespace PC₁

structure CongruentBinaryOperation (U₁ U₂ U₃: Universal): Type where
  op: U₁.Particular → CongruentUnaryOperation U₂ U₃
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x =₍U₁₎ y → ((op x).op z =₍U₃₎ (op y).op z)

end PC₁

end Logic
