-- Polymorphic equality of the universe
axiom eq_poly {X: Type}: X → X → Prop
notation:50 A:51 " =ₚ " B:51 => eq_poly A B

axiom eq_poly_refl: ∀ (x: X), x =ₚ x
axiom eq_poly_sym: ∀ (x:  X), ∀ (y:  X), x =ₚ y → y =ₚ x
axiom eq_poly_trans: ∀ (x:  X), ∀ (y:  X), ∀ (z:  X), x =ₚ y ∧ y =ₚ z → x =ₚ z
