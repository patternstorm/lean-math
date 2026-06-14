import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND

-- A `CongruentTernaryPredicate U₁ U₂ U₃` is a ternary predicate over three
-- Universals that respects each Universal's equality.
--
-- Flat shape: `pred` is a direct ternary function and `cong` is a single
-- combined congruence statement (all three arguments may vary together).
-- Per-fiber views are derived via preservation theorems and auto-inference
-- instances, parallel to the binary case.
structure CongruentTernaryPredicate (U₁: Universal) (U₂: Universal) (U₃: Universal): Type where
  pred: U₁.Particular → U₂.Particular → U₃.Particular → Prop
  cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular),
        ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular),
        ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
        x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → z₁ =₍U₃₎ z₂ → (pred x₁ y₁ z₁ ↔ pred x₂ y₂ z₂)  -- TOO use and

-- Typeclass form. Three independent per-argument cong fields, kept for the
-- natural shape of structural auto-derivation via connectives.
class CongruentTernary (U₁: Universal) (U₂: Universal) (U₃: Universal)
    (P: U₁.Particular → U₂.Particular → U₃.Particular → Prop) where
  cong₁: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
    x₁ =₍U₁₎ x₂ → (P x₁ y z ↔ P x₂ y z)
  cong₂: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
    y₁ =₍U₂₎ y₂ → (P x y₁ z ↔ P x y₂ z)
  cong₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
    z₁ =₍U₃₎ z₂ → (P x y z₁ ↔ P x y z₂)

-- Combine the three per-argument congs into a single combined cong (the shape
-- the structure's `cong` field expects). Chains through two intermediates:
-- `P x₁ y₁ z₁ ↔ P x₂ y₁ z₁ ↔ P x₂ y₂ z₁ ↔ P x₂ y₂ z₂`.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31

theorem ternary_cong_from_fibers {U₁ U₂ U₃: Universal} {P: U₁.Particular → U₂.Particular → U₃.Particular → Prop}
    (cong₁: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
            x₁ =₍U₁₎ x₂ → (P x₁ y z ↔ P x₂ y z))
    (cong₂: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
            y₁ =₍U₂₎ y₂ → (P x y₁ z ↔ P x y₂ z))
    (cong₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
            z₁ =₍U₃₎ z₂ → (P x y z₁ ↔ P x y z₂)) :
    ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular),
    ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular),
    ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → z₁ =₍U₃₎ z₂ →
      (P x₁ y₁ z₁ ↔ P x₂ y₂ z₂) := by forall_intro
  variable(a₁: U₁.Particular)
  variable(a₂: U₁.Particular)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  variable(c₁: U₃.Particular)
  variable(c₂: U₃.Particular)
  assume(h₁: a₁ =₍U₁₎ a₂)
  assume(h₂: b₁ =₍U₂₎ b₂)
  assume(h₃: c₁ =₍U₃₎ c₂)
  -- Step 1: vary x — P a₁ b₁ c₁ ↔ P a₂ b₁ c₁
  have h₄: a₁ =₍U₁₎ a₂ → (P a₁ b₁ c₁ ↔ P a₂ b₁ c₁) := by forall_elim cong₁, a₁, a₂, b₁, c₁
  have h₅: P a₁ b₁ c₁ ↔ P a₂ b₁ c₁ := by modus_ponens h₄, h₁
  -- Step 2: vary y — P a₂ b₁ c₁ ↔ P a₂ b₂ c₁
  have h₆: b₁ =₍U₂₎ b₂ → (P a₂ b₁ c₁ ↔ P a₂ b₂ c₁) := by forall_elim cong₂, a₂, b₁, b₂, c₁
  have h₇: P a₂ b₁ c₁ ↔ P a₂ b₂ c₁ := by modus_ponens h₆, h₂
  -- Step 3: vary z — P a₂ b₂ c₁ ↔ P a₂ b₂ c₂
  have h₈: c₁ =₍U₃₎ c₂ → (P a₂ b₂ c₁ ↔ P a₂ b₂ c₂) := by forall_elim cong₃, a₂, b₂, c₁, c₂
  have h₉: P a₂ b₂ c₁ ↔ P a₂ b₂ c₂ := by modus_ponens h₈, h₃
  -- Chain
  have h₁₀: P a₁ b₁ c₁ → P a₂ b₂ c₂ := by
    assume(h₁₀₁: P a₁ b₁ c₁)
    have h₁₀₂: P a₂ b₁ c₁ := PC₀.deductive_eq_l2r h₅ h₁₀₁
    have h₁₀₃: P a₂ b₂ c₁ := PC₀.deductive_eq_l2r h₇ h₁₀₂
    have h₁₀₄: P a₂ b₂ c₂ := PC₀.deductive_eq_l2r h₉ h₁₀₃
    iterate h₁₀₄
  have h₁₁: P a₂ b₂ c₂ → P a₁ b₁ c₁ := by
    assume(h₁₁₁: P a₂ b₂ c₂)
    have h₁₁₂: P a₂ b₂ c₁ := PC₀.deductive_eq_r2l h₉ h₁₁₁
    have h₁₁₃: P a₂ b₁ c₁ := PC₀.deductive_eq_r2l h₇ h₁₁₂
    have h₁₁₄: P a₁ b₁ c₁ := PC₀.deductive_eq_r2l h₅ h₁₁₃
    iterate h₁₁₄
  have h₁₂: P a₁ b₁ c₁ ↔ P a₂ b₂ c₂ := by iff_intro h₁₀, h₁₁
  iterate h₁₂

-- Coercion: from `[CongruentTernary]` typeclass to the structure.
-- Combined cong is derived from the three per-argument congs via
-- `combined_from_three_cong`. Key invariant: `coe.pred = P` definitionally.
instance congruent_ternary_coercion {U₁: Universal} {U₂: Universal} {U₃: Universal}
    {P: U₁.Particular → U₂.Particular → U₃.Particular → Prop}
    [c: CongruentTernary U₁ U₂ U₃ P]:
    CoeDep (U₁.Particular → U₂.Particular → U₃.Particular → Prop) P (CongruentTernaryPredicate U₁ U₂ U₃) where
  coe := { pred := P, cong := ternary_cong_from_fibers c.cong₁ c.cong₂ c.cong₃ }

-- Bridge: a `CongruentTernaryPredicate`'s `.pred` is itself congruent in each
-- argument. Each per-arg cong is derived from `R.cong` (combined) by
-- instantiating with reflexivity on the other two arguments.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
instance (priority := 50) congruent_ternary_pred {U₁ U₂ U₃: Universal} {R: CongruentTernaryPredicate U₁ U₂ U₃}:
    CongruentTernary U₁ U₂ U₃ R.pred where
  cong₁: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
      x₁ =₍U₁₎ x₂ → (R.pred x₁ y z ↔ R.pred x₂ y z) := by forall_intro
    variable(x₁: U₁.Particular)
    variable(x₂: U₁.Particular)
    variable(y: U₂.Particular)
    variable(z: U₃.Particular)
    assume(h₁: x₁ =₍U₁₎ x₂)
    have h₂: x₁ =₍U₁₎ x₂ → y =₍U₂₎ y → z =₍U₃₎ z → (R.pred x₁ y z ↔ R.pred x₂ y z) := by forall_elim R.cong, x₁, x₂, y, y, z, z
    have h₃: y =₍U₂₎ y := U₂.eq.refl y
    have h₄: z =₍U₃₎ z := U₃.eq.refl z
    have h₅: y =₍U₂₎ y → z =₍U₃₎ z → (R.pred x₁ y z ↔ R.pred x₂ y z) := by modus_ponens h₂, h₁
    have h₆: z =₍U₃₎ z → (R.pred x₁ y z ↔ R.pred x₂ y z) := by modus_ponens h₅, h₃
    have h₇: R.pred x₁ y z ↔ R.pred x₂ y z := by modus_ponens h₆, h₄
    iterate h₇
  cong₂: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
      y₁ =₍U₂₎ y₂ → (R.pred x y₁ z ↔ R.pred x y₂ z) := by forall_intro
    variable(x: U₁.Particular)
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    variable(z: U₃.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    have h₂: x =₍U₁₎ x → y₁ =₍U₂₎ y₂ → z =₍U₃₎ z → (R.pred x y₁ z ↔ R.pred x y₂ z) := by forall_elim R.cong, x, x, y₁, y₂, z, z
    have h₃: x =₍U₁₎ x := U₁.eq.refl x
    have h₄: z =₍U₃₎ z := U₃.eq.refl z
    have h₅: y₁ =₍U₂₎ y₂ → z =₍U₃₎ z → (R.pred x y₁ z ↔ R.pred x y₂ z) := by modus_ponens h₂, h₃
    have h₆: z =₍U₃₎ z → (R.pred x y₁ z ↔ R.pred x y₂ z) := by modus_ponens h₅, h₁
    have h₇: R.pred x y₁ z ↔ R.pred x y₂ z := by modus_ponens h₆, h₄
    iterate h₇
  cong₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      z₁ =₍U₃₎ z₂ → (R.pred x y z₁ ↔ R.pred x y z₂) := by forall_intro
    variable(x: U₁.Particular)
    variable(y: U₂.Particular)
    variable(z₁: U₃.Particular)
    variable(z₂: U₃.Particular)
    assume(h₁: z₁ =₍U₃₎ z₂)
    have h₂: x =₍U₁₎ x → y =₍U₂₎ y → z₁ =₍U₃₎ z₂ → (R.pred x y z₁ ↔ R.pred x y z₂) := by forall_elim R.cong, x, x, y, y, z₁, z₂
    have h₃: x =₍U₁₎ x := U₁.eq.refl x
    have h₄: y =₍U₂₎ y := U₂.eq.refl y
    have h₅: y =₍U₂₎ y → z₁ =₍U₃₎ z₂ → (R.pred x y z₁ ↔ R.pred x y z₂) := by modus_ponens h₂, h₃
    have h₆: z₁ =₍U₃₎ z₂ → (R.pred x y z₁ ↔ R.pred x y z₂) := by modus_ponens h₅, h₄
    have h₇: R.pred x y z₁ ↔ R.pred x y z₂ := by modus_ponens h₆, h₁
    iterate h₇

-- Bridge: derives `CongruentTernary` from per-argument `CongruentUnary` instances.
-- For each pair of fixed arguments, the predicate must be congruent in the
-- remaining argument. Low priority so specific instances take precedence.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
instance (priority := 50) congruent_ternary_from_fibers {U₁ U₂ U₃: Universal}
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

-- Fiber preservation theorems and the corresponding auto-inference instances
-- live in the `Properties/` folder:
--   - `Properties/FiberFirstPreservesCongruence.lean` — fix first arg → `CongruentBinary`
--   - `Properties/FiberFirstTwoPreservesCongruence.lean` — fix first two args → `CongruentUnary`

-- # `CoeFun`: lets us write `P x y z` instead of `P.pred x y z`.
instance {U₁ U₂ U₃: Universal}: CoeFun (CongruentTernaryPredicate U₁ U₂ U₃) (fun _ => U₁.Particular → U₂.Particular → U₃.Particular → Prop) where
  coe P := P.pred

end PC₁

end Logic
