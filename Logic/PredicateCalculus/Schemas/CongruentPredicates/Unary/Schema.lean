import Logic.PredicateCalculus.Schemas.Universal.Schema

namespace Logic

namespace PC₁

structure CongruentUnaryPredicate (U: Universal): Type where
  pred: U.Particular → Prop
  cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (pred x ↔ pred y)

end PC₁

end Logic
