import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema

namespace Logic

namespace PC₁

structure CongruentTernaryPredicate (U₁: Universal) (U₂: Universal) (U₃: Universal): Type where
  pred: U₁.Particular → CongruentBinaryPredicate U₂ U₃
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (u: U₂.Particular), ∀ (v: U₃.Particular),
        x =₍U₁₎ y → (((pred x).pred u).pred v ↔ ((pred y).pred u).pred v)

end PC₁

end Logic
