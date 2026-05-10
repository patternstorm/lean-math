import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

open ND

structure CongruentTernaryPredicate (U₁: Universal) (U₂: Universal) (U₃: Universal): Type where
  pred: U₁.Particular → CongruentBinaryPredicate U₂ U₃
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (u: U₂.Particular), ∀ (v: U₃.Particular),
        x =₍U₁₎ y → (((pred x).pred u).pred v ↔ ((pred y).pred u).pred v)

class CongruentTernary (U₁: Universal) (U₂: Universal) (U₃: Universal)
    (P: U₁.Particular → U₂.Particular → U₃.Particular → Prop) where
  cong₁: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
    x₁ =₍U₁₎ x₂ → (P x₁ y z ↔ P x₂ y z)
  cong₂: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
    y₁ =₍U₂₎ y₂ → (P x y₁ z ↔ P x y₂ z)
  cong₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
    z₁ =₍U₃₎ z₂ → (P x y z₁ ↔ P x y z₂)

-- Coercion: when Lean expects a CongruentTernaryPredicate and finds a ternary predicate P,
-- it coerces automatically if CongruentTernary U₁ U₂ U₃ P is synthesizable.
-- Key invariant: the inner .pred fields equal P x y z definitionally.
instance congruent_ternary_coercion {U₁: Universal} {U₂: Universal} {U₃: Universal}
    {P: U₁.Particular → U₂.Particular → U₃.Particular → Prop}
    [c: CongruentTernary U₁ U₂ U₃ P]:
    CoeDep (U₁.Particular → U₂.Particular → U₃.Particular → Prop) P (CongruentTernaryPredicate U₁ U₂ U₃) where
  coe :=
    let pred: U₁.Particular → CongruentBinaryPredicate U₂ U₃ :=
      (x: U₁.Particular ↦
        let inner_pred: U₂.Particular → CongruentUnaryPredicate U₃ :=
          (y: U₂.Particular ↦
            let fiber_cong: ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
                z₁ =₍U₃₎ z₂ → (P x y z₁ ↔ P x y z₂) := by
              have h₁ := by forall_elim c.cong₃, x
              have h₂ := by forall_elim h₁, y
              iterate h₂
            { pred := P x y, cong := fiber_cong })
        let inner_cong: ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
            y₁ =₍U₂₎ y₂ → ((inner_pred y₁).pred z ↔ (inner_pred y₂).pred z) := by
          have h₁ := by forall_elim c.cong₂, x
          iterate h₁
        { pred := inner_pred, cong := inner_cong })
    let cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
        x₁ =₍U₁₎ x₂ → (((pred x₁).pred y).pred z ↔ ((pred x₂).pred y).pred z) :=
      c.cong₁
    { pred := pred, cong := cong }

-- Bridge: a CongruentTernaryPredicate's nested .pred fields are themselves congruent.
-- Low priority so structural instances take precedence.
instance (priority := 50) congruent_ternary_pred {U₁: Universal} {U₂: Universal} {U₃: Universal} {R: CongruentTernaryPredicate U₁ U₂ U₃}:
    CongruentTernary U₁ U₂ U₃ (x: U₁.Particular, y: U₂.Particular, z: U₃.Particular ↦ ((R.pred x).pred y).pred z) where
  cong₁: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
      x₁ =₍U₁₎ x₂ → (((R.pred x₁).pred y).pred z ↔ ((R.pred x₂).pred y).pred z) := R.cong
  cong₂: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
      y₁ =₍U₂₎ y₂ → (((R.pred x).pred y₁).pred z ↔ ((R.pred x).pred y₂).pred z) := by forall_intro
    variable(x: U₁.Particular)
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    variable(z: U₃.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    have h₂: ∀ (y₂': U₂.Particular), ∀ (z': U₃.Particular), y₁ =₍U₂₎ y₂' → (((R.pred x).pred y₁).pred z' ↔ ((R.pred x).pred y₂').pred z') := by forall_elim (R.pred x).cong, y₁
    have h₃: ∀ (z': U₃.Particular), y₁ =₍U₂₎ y₂ → (((R.pred x).pred y₁).pred z' ↔ ((R.pred x).pred y₂).pred z') := by forall_elim h₂, y₂
    have h₄: y₁ =₍U₂₎ y₂ → (((R.pred x).pred y₁).pred z ↔ ((R.pred x).pred y₂).pred z) := by forall_elim h₃, z
    have h₅: ((R.pred x).pred y₁).pred z ↔ ((R.pred x).pred y₂).pred z := by modus_ponens h₄, h₁
    iterate h₅
  cong₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      z₁ =₍U₃₎ z₂ → (((R.pred x).pred y).pred z₁ ↔ ((R.pred x).pred y).pred z₂) := by forall_intro
    variable(x: U₁.Particular)
    variable(y: U₂.Particular)
    variable(z₁: U₃.Particular)
    variable(z₂: U₃.Particular)
    assume(h₁: z₁ =₍U₃₎ z₂)
    have h₂: ∀ (z₂': U₃.Particular), z₁ =₍U₃₎ z₂' → (((R.pred x).pred y).pred z₁ ↔ ((R.pred x).pred y).pred z₂') := by forall_elim ((R.pred x).pred y).cong, z₁
    have h₃: z₁ =₍U₃₎ z₂ → (((R.pred x).pred y).pred z₁ ↔ ((R.pred x).pred y).pred z₂) := by forall_elim h₂, z₂
    have h₄: ((R.pred x).pred y).pred z₁ ↔ ((R.pred x).pred y).pred z₂ := by modus_ponens h₃, h₁
    iterate h₄

-- Bridge: derives CongruentTernary from unary CongruentUnary instances.
-- For each pair of fixed arguments, the predicate must be congruent in the remaining argument.
-- Low priority so specific instances take precedence.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
instance (priority := 50) congruent_ternary_from_unary {U₁ U₂ U₃: Universal}
    {P: U₁.Particular → U₂.Particular → U₃.Particular → Prop}
    [c₁: ∀ (y: U₂.Particular), ∀ (z: U₃.Particular), CongruentUnary U₁ (x: U₁.Particular ↦ P x y z)]
    [c₂: ∀ (x: U₁.Particular), ∀ (z: U₃.Particular), CongruentUnary U₂ (y: U₂.Particular ↦ P x y z)]
    [c₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), CongruentUnary U₃ (P x y)]:
    CongruentTernary U₁ U₂ U₃ P where
  cong₁: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
      x₁ =₍U₁₎ x₂ → (P x₁ y z ↔ P x₂ y z) := by forall_intro
    variable(x₁: U₁.Particular)
    variable(x₂: U₁.Particular)
    variable(y: U₂.Particular)
    variable(z: U₃.Particular)
    assume(h₁: x₁ =₍U₁₎ x₂)
    have h₂: ∀ (x₂': U₁.Particular), x₁ =₍U₁₎ x₂' → ((x: U₁.Particular ↦ P x y z) x₁ ↔ (x: U₁.Particular ↦ P x y z) x₂') := by forall_elim (c₁ y z).cong, x₁
    have h₃: x₁ =₍U₁₎ x₂ → ((x: U₁.Particular ↦ P x y z) x₁ ↔ (x: U₁.Particular ↦ P x y z) x₂) := by forall_elim h₂, x₂
    have h₄: (x: U₁.Particular ↦ P x y z) x₁ ↔ (x: U₁.Particular ↦ P x y z) x₂ := by modus_ponens h₃, h₁
    iterate h₄
  cong₂: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
      y₁ =₍U₂₎ y₂ → (P x y₁ z ↔ P x y₂ z) := by forall_intro
    variable(x: U₁.Particular)
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    variable(z: U₃.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    have h₂: ∀ (y₂': U₂.Particular), y₁ =₍U₂₎ y₂' → ((y: U₂.Particular ↦ P x y z) y₁ ↔ (y: U₂.Particular ↦ P x y z) y₂') := by forall_elim (c₂ x z).cong, y₁
    have h₃: y₁ =₍U₂₎ y₂ → ((y: U₂.Particular ↦ P x y z) y₁ ↔ (y: U₂.Particular ↦ P x y z) y₂) := by forall_elim h₂, y₂
    have h₄: (y: U₂.Particular ↦ P x y z) y₁ ↔ (y: U₂.Particular ↦ P x y z) y₂ := by modus_ponens h₃, h₁
    iterate h₄
  cong₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      z₁ =₍U₃₎ z₂ → (P x y z₁ ↔ P x y z₂) := by forall_intro
    variable(x: U₁.Particular)
    variable(y: U₂.Particular)
    variable(z₁: U₃.Particular)
    variable(z₂: U₃.Particular)
    assume(h₁: z₁ =₍U₃₎ z₂)
    have h₂: ∀ (z₂': U₃.Particular), z₁ =₍U₃₎ z₂' → (P x y z₁ ↔ P x y z₂') := by forall_elim (c₃ x y).cong, z₁
    have h₃: z₁ =₍U₃₎ z₂ → (P x y z₁ ↔ P x y z₂) := by forall_elim h₂, z₂
    have h₄: P x y z₁ ↔ P x y z₂ := by modus_ponens h₃, h₁
    iterate h₄

end PC₁

end Logic
