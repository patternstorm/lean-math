import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema

namespace Logic

namespace PC₁

structure CongruentTernaryPredicate (U₁: Universal) (U₂: Universal) (U₃: Universal): Type where
  pred: U₁.Particular → CongruentBinaryPredicate U₂ U₃
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (u: U₂.Particular), ∀ (v: U₃.Particular),
        x =₍U₁₎ y → (((pred x).pred u).pred v ↔ ((pred y).pred u).pred v)

structure ZPairs where
  pair : Nat × Nat

structure QPairs where
  pair : Nat × Nat

-- Check their types
#check ZPairs  -- Type
#check QPairs  -- Type


example : ZPairs = QPairs := sorry -- by
  -- This WON'T compile - they're different types!
  -- rfl  -- Error: ZPairs and QPairs are different

end PC₁

end Logic
