namespace Logic

namespace PC₁

structure Equality (X: Type) where
  pred: X → X → Prop
  refl: ∀ (x: X), pred x x
  sym: ∀ (x: X), ∀ (y: X), pred x y → pred y x
  trans: ∀ (x: X), ∀ (y: X), ∀  (z: X), pred x y ∧ pred y z → pred x z

end PC₁

end Logic
