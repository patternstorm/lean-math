import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

open ND

structure CongruentBinaryPredicate (U₁: Universal) (U₂: Universal): Type where
  pred: U₁.Particular → CongruentUnaryPredicate U₂
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x =₍U₁₎ y → ((pred x).pred z ↔ (pred y).pred z)

class CongruentBinary (U₁: Universal) (U₂: Universal) (P: U₁.Particular → U₂.Particular → Prop) where
  inner_cong: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂)
  outer_cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (z: U₂.Particular), x₁ =₍U₁₎ x₂ → (P x₁ z ↔ P x₂ z)

-- Coercion: when Lean expects a CongruentBinaryPredicate and finds a binary predicate P,
-- it coerces automatically if CongruentBinary U₁ U₂ P is synthesizable.
-- Key invariant: each fiber's .pred = P x definitionally.
instance congruent_binary_coercion {U₁: Universal} {U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    [c: CongruentBinary U₁ U₂ P]: CoeDep (U₁.Particular → U₂.Particular → Prop) P (CongruentBinaryPredicate U₁ U₂) where
  coe :=
    let pred: U₁.Particular → CongruentUnaryPredicate U₂ :=
      (x: U₁.Particular ↦
        let fiber_cong: ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂) := by
          have h₁ := by forall_elim c.inner_cong, x
          iterate h₁
        { pred := P x, cong := fiber_cong })
    { pred := pred, cong := c.outer_cong }

-- Bridge: derives CongruentBinary from unary CongruentUnary instances.
-- For each fixed x, P x must be congruent in y (inner).
-- For each fixed z, (fun x => P x z) must be congruent in x (outer).
-- Low priority so specific instances (congruent_curry) take precedence.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
instance (priority := 50) congruent_binary_from_unary {U₁ U₂: Universal}
    {P: U₁.Particular → U₂.Particular → Prop}
    [inner: ∀ x: U₁.Particular, CongruentUnary U₂ (P x)]
    [outer: ∀ z: U₂.Particular, CongruentUnary U₁ (fun x => P x z)]:
    CongruentBinary U₁ U₂ P where
  inner_cong: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂) := by forall_intro
    variable(x: U₁.Particular)
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    have h₂: ∀ (b: U₂.Particular), y₁ =₍U₂₎ b → (P x y₁ ↔ P x b) := by forall_elim (inner x).cong, y₁
    have h₃: y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂) := by forall_elim h₂, y₂
    have h₄: P x y₁ ↔ P x y₂ := by modus_ponens h₃, h₁
    iterate h₄
  outer_cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (z: U₂.Particular), x₁ =₍U₁₎ x₂ → (P x₁ z ↔ P x₂ z) := by forall_intro
    variable(x₁: U₁.Particular)
    variable(x₂: U₁.Particular)
    variable(z: U₂.Particular)
    assume(h₁: x₁ =₍U₁₎ x₂)
    have h₂: ∀ (b: U₁.Particular), x₁ =₍U₁₎ b → ((fun x => P x z) x₁ ↔ (fun x => P x z) b) := by forall_elim (outer z).cong, x₁
    have h₃: x₁ =₍U₁₎ x₂ → ((fun x => P x z) x₁ ↔ (fun x => P x z) x₂) := by forall_elim h₂, x₂
    have h₄: (fun x => P x z) x₁ ↔ (fun x => P x z) x₂ := by modus_ponens h₃, h₁
    iterate h₄

end PC₁

end Logic
