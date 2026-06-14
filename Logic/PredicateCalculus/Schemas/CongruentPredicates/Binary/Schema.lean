import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND

-- A `CongruentBinaryPredicate U₁ U₂` is a binary predicate over two Universals
-- that respects each Universal's equality.
--
-- The shape is FLAT: `pred` is a direct binary function and `cong` is a single
-- combined congruence statement (both arguments may vary together). This avoids
-- artificially splitting binary predicates through a fiber-valued representation.
-- When the per-fiber view is needed, `fiber_first_preserves_binary_congruence` /
-- `fiber_second_preserves_binary_congruence` derive it as a `CongruentUnaryPredicate`-shaped
-- fact, and the matching `fiber_first_binary_congruent_unary` / `fiber_second_binary_congruent_unary`
-- instances let the auto-cong machinery pick it up automatically.
structure CongruentBinaryPredicate (U₁: Universal) (U₂: Universal): Type where
  pred: U₁.Particular → U₂.Particular → Prop
  cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular),
        U₁.eq x₁ x₂ → U₂.eq y₁ y₂ → (pred x₁ y₁ ↔ pred x₂ y₂) -- TODO refactor to use and

-- Typeclass form. Kept as inner+outer cong (the natural shape for structural
-- auto-derivation via connectives). The two per-argument congs are combined
-- into the structure's single cong field via `binary_congruence_from_congruent_fibers`
-- (in `Binary.Properties.BinaryCongruenceFromCongruentFibers`) at coercion time.
class CongruentBinary (U₁: Universal) (U₂: Universal) (P: U₁.Particular → U₂.Particular → Prop) where
  inner_cong: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), U₂.eq y₁ y₂ → (P x y₁ ↔ P x y₂)
  outer_cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (z: U₂.Particular), U₁.eq x₁ x₂ → (P x₁ z ↔ P x₂ z)

-- Bridge: derives `CongruentBinary` from per-argument `CongruentUnary` instances.
-- For each fixed `x`, `P x` must be congruent in `y` (inner).
-- For each fixed `z`, `fun x => P x z` must be congruent in `x` (outer).
-- Low priority so specific instances (e.g. `congruent_curry`) take precedence.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
instance (priority := 50) congruent_binary_from_fibers {U₁ U₂: Universal}
    {P: U₁.Particular → U₂.Particular → Prop}
    [inner: ∀ x: U₁.Particular, CongruentUnary U₂ (P x)]
    [outer: ∀ z: U₂.Particular, CongruentUnary U₁ (fun x => P x z)]:
    CongruentBinary U₁ U₂ P where
  inner_cong: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), U₂.eq y₁ y₂ → (P x y₁ ↔ P x y₂) := by forall_intro
    variable(x: U₁.Particular)
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    assume(h₁: U₂.eq y₁ y₂)
    have h₂: ∀ (b: U₂.Particular), U₂.eq y₁ b → (P x y₁ ↔ P x b) := by forall_elim (inner x).cong, y₁
    have h₃: U₂.eq y₁ y₂ → (P x y₁ ↔ P x y₂) := by forall_elim h₂, y₂
    have h₄: P x y₁ ↔ P x y₂ := by modus_ponens h₃, h₁
    iterate h₄
  outer_cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (z: U₂.Particular), U₁.eq x₁ x₂ → (P x₁ z ↔ P x₂ z) := by forall_intro
    variable(x₁: U₁.Particular)
    variable(x₂: U₁.Particular)
    variable(z: U₂.Particular)
    assume(h₁: U₁.eq x₁ x₂)
    have h₂: ∀ (b: U₁.Particular), U₁.eq x₁ b → ((fun x => P x z) x₁ ↔ (fun x => P x z) b) := by forall_elim (outer z).cong, x₁
    have h₃: U₁.eq x₁ x₂ → ((fun x => P x z) x₁ ↔ (fun x => P x z) x₂) := by forall_elim h₂, x₂
    have h₄: (fun x => P x z) x₁ ↔ (fun x => P x z) x₂ := by modus_ponens h₃, h₁
    iterate h₄

-- # `CoeFun`: lets us write `P x y` instead of `P.pred x y`.
-- A `CongruentBinaryPredicate U₁ U₂` is callable as a 2-argument function returning
-- the proposition. The `.pred` projection becomes implicit.
instance {U₁ U₂: Universal}: CoeFun (CongruentBinaryPredicate U₁ U₂) (fun _ => U₁.Particular → U₂.Particular → Prop) where
  coe P := P.pred

end PC₁

end Logic
