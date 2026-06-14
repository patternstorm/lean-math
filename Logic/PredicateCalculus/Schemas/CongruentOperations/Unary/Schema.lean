import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals

namespace Logic

namespace PC₁

structure CongruentUnaryOperation (U₁ U₂: Universal): Type where
  op: U₁.Particular → U₂.Particular
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), x =₍U₁₎ y → (op x =₍U₂₎ op y)

end PC₁

end Logic
