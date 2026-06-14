import Logic.PredicateCalculus.Schemas.Operations.Binary
import Logic.PredicateCalculus.Definitions.Operations.Binary

namespace Test.BinaryOperation

open Logic
open Logic.PC₁


-- # Test: a trivial binary operation
--
-- This file exercises the binary-operation framework end-to-end. We define a
-- simple binary operation `first_projection : U ⟴ U ⟴ U` that returns its
-- first argument, then verify:
-- 1. The graph compiles with all four obligations (pred, cong, ltot, rdet).
-- 2. The `binary_operation` macro accepts the graph and produces the curried
--    `BinaryOperation` value.
-- 3. Partial application `first_projection x : U ⟴ U` is a `UnaryOperation`
--    (the curried form is wired correctly).
-- 4. The defining axiom can be used to derive an equational characterization.
--
-- Graph: `pred x y z  ≡  z =₍U₎ x`


-- ## Left totality: for each (x, y), z := x is a witness.
theorem first_projection_left_totality {U: Universal}:
    ∀ (x: U.Particular), ∀ (y: U.Particular), ∃ (z: U.Particular), z =₍U₎ x := by forall_intro
  variable(x: U.Particular)
  variable(y: U.Particular)
  have h₁: x =₍U₎ x := by forall_elim U.eq.refl, x
  have h₂: ∃ (z: U.Particular), z =₍U₎ x := by exists_intro h₁, x
  iterate h₂


-- ## Right determinacy: if z₁ =₍U₎ x and z₂ =₍U₎ x, then z₁ =₍U₎ z₂.
theorem first_projection_right_determinacy {U: Universal}:
    ∀ (x: U.Particular), ∀ (y: U.Particular), ∀ (z₁: U.Particular), ∀ (z₂: U.Particular),
      z₁ =₍U₎ x ∧ z₂ =₍U₎ x → z₁ =₍U₎ z₂ := by forall_intro
  variable(x: U.Particular)
  variable(y: U.Particular)
  variable(z₁: U.Particular)
  variable(z₂: U.Particular)
  assume(h₁: z₁ =₍U₎ x ∧ z₂ =₍U₎ x)
  have h₂: z₁ =₍U₎ x := by and_elim h₁
  have h₃: z₂ =₍U₎ x := by and_elim h₁
  -- z₂ =₍U₎ x → x =₍U₎ z₂ via symmetry.
  have h₄: z₂ =₍U₎ x → x =₍U₎ z₂ := by forall_elim U.eq.sym, z₂, x
  have h₅: x =₍U₎ z₂ := by modus_ponens h₄, h₃
  -- z₁ =₍U₎ x ∧ x =₍U₎ z₂ → z₁ =₍U₎ z₂ via transitivity.
  have h₆: z₁ =₍U₎ x ∧ x =₍U₎ z₂ → z₁ =₍U₎ z₂ := by forall_elim U.eq.trans, z₁, x, z₂
  have h₇: z₁ =₍U₎ x ∧ x =₍U₎ z₂ := by and_intro h₂, h₅
  have h₈: z₁ =₍U₎ z₂ := by modus_ponens h₆, h₇
  iterate h₈


-- ## The binary graph itself.
noncomputable def first_projection_graph {U: Universal}: BinaryOperationGraph U U U :=
  let pred: U.Particular → U.Particular → U.Particular → Prop :=
    (x: U.Particular, y: U.Particular, z: U.Particular ↦ z =₍U₎ x)
  let cong: ∀ (x₁: U.Particular), ∀ (x₂: U.Particular),
            ∀ (y₁: U.Particular), ∀ (y₂: U.Particular),
            ∀ (z₁: U.Particular), ∀ (z₂: U.Particular),
        x₁ =₍U₎ x₂ → y₁ =₍U₎ y₂ → z₁ =₍U₎ z₂ →
          ((z₁ =₍U₎ x₁) ↔ (z₂ =₍U₎ x₂)) := by forall_intro
    variable(x₁: U.Particular)
    variable(x₂: U.Particular)
    variable(y₁: U.Particular)
    variable(y₂: U.Particular)
    variable(z₁: U.Particular)
    variable(z₂: U.Particular)
    assume(h₁: x₁ =₍U₎ x₂)
    assume(h₂: y₁ =₍U₎ y₂)
    assume(h₃: z₁ =₍U₎ z₂)
    -- Forward: z₁ =₍U₎ x₁ → z₂ =₍U₎ x₂.
    have h₄: z₁ =₍U₎ x₁ → z₂ =₍U₎ x₂ := by
      assume(h₄₁: z₁ =₍U₎ x₁)
      have h₄₂: z₁ =₍U₎ z₂ → z₂ =₍U₎ z₁ := by forall_elim U.eq.sym, z₁, z₂
      have h₄₃: z₂ =₍U₎ z₁ := by modus_ponens h₄₂, h₃
      have h₄₄: z₂ =₍U₎ z₁ ∧ z₁ =₍U₎ x₁ → z₂ =₍U₎ x₁ := by forall_elim U.eq.trans, z₂, z₁, x₁
      have h₄₅: z₂ =₍U₎ z₁ ∧ z₁ =₍U₎ x₁ := by and_intro h₄₃, h₄₁
      have h₄₆: z₂ =₍U₎ x₁ := by modus_ponens h₄₄, h₄₅
      have h₄₇: z₂ =₍U₎ x₁ ∧ x₁ =₍U₎ x₂ → z₂ =₍U₎ x₂ := by forall_elim U.eq.trans, z₂, x₁, x₂
      have h₄₈: z₂ =₍U₎ x₁ ∧ x₁ =₍U₎ x₂ := by and_intro h₄₆, h₁
      have h₄₉: z₂ =₍U₎ x₂ := by modus_ponens h₄₇, h₄₈
      iterate h₄₉
    -- Backward: z₂ =₍U₎ x₂ → z₁ =₍U₎ x₁.
    have h₅: z₂ =₍U₎ x₂ → z₁ =₍U₎ x₁ := by
      assume(h₅₁: z₂ =₍U₎ x₂)
      have h₅₂: x₁ =₍U₎ x₂ → x₂ =₍U₎ x₁ := by forall_elim U.eq.sym, x₁, x₂
      have h₅₃: x₂ =₍U₎ x₁ := by modus_ponens h₅₂, h₁
      have h₅₄: z₂ =₍U₎ x₂ ∧ x₂ =₍U₎ x₁ → z₂ =₍U₎ x₁ := by forall_elim U.eq.trans, z₂, x₂, x₁
      have h₅₅: z₂ =₍U₎ x₂ ∧ x₂ =₍U₎ x₁ := by and_intro h₅₁, h₅₃
      have h₅₆: z₂ =₍U₎ x₁ := by modus_ponens h₅₄, h₅₅
      have h₅₇: z₁ =₍U₎ z₂ ∧ z₂ =₍U₎ x₁ → z₁ =₍U₎ x₁ := by forall_elim U.eq.trans, z₁, z₂, x₁
      have h₅₈: z₁ =₍U₎ z₂ ∧ z₂ =₍U₎ x₁ := by and_intro h₃, h₅₆
      have h₅₉: z₁ =₍U₎ x₁ := by modus_ponens h₅₇, h₅₈
      iterate h₅₉
    have h₆: (z₁ =₍U₎ x₁) ↔ (z₂ =₍U₎ x₂) := by iff_intro h₄, h₅
    iterate h₆
  { pred := pred
    cong := cong
    ltot := first_projection_left_totality
    rdet := first_projection_right_determinacy }


-- ## The binary operation via the macro.
binary_operation first_projection : U ⟴ U ⟴ U from first_projection_graph


-- ## Sanity check 1: first_projection x y =₍U₎ x.
-- Uses the defining axiom + reflexivity, with the graph's predicate
-- definitionally unfolding through `z =₍U₎ x` at z := x.
theorem first_projection_returns_first {U: Universal}:
    ∀ (x: U.Particular), ∀ (y: U.Particular), first_projection x y =₍U₎ x := by forall_intro
  variable(x: U.Particular)
  variable(y: U.Particular)
  have h₁: ∀ (z: U.Particular), (first_projection x y =₍U₎ z) ↔ first_projection_graph.pred x y z := by forall_elim first_projection_def, x, y
  have h₂: (first_projection x y =₍U₎ x) ↔ first_projection_graph.pred x y x := by forall_elim h₁, x
  -- first_projection_graph.pred x y x unfolds (definitionally) to x =₍U₎ x.
  have h₃: x =₍U₎ x := by forall_elim U.eq.refl, x
  have h₄: first_projection x y =₍U₎ x := PC₀.deductive_eq_r2l h₂ h₃
  iterate h₄


-- ## Sanity check 2: partial application gives a UnaryOperation.
-- `first_projection x` is typed as `U ⟴ U` (a UnaryOperation), confirming the
-- curried-form schema is wired correctly. `noncomputable` is required because
-- `first_projection` depends on axioms.
noncomputable example {U: Universal} (a: U.Particular): U ⟴ U := first_projection a


end Test.BinaryOperation
