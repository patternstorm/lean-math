import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Instances.BinaryOperationGraph
import Logic.PredicateCalculus.Schemas.Operations.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND


-- # BinaryOperation
--
-- In first-order logic, a binary operation op : U₁ → U₂ → U₃ is defined by
-- its graph — a `BinaryOperationGraph` G(x, y, z) (a congruent ternary
-- predicate refined with totality and functionality obligations on the third
-- argument) satisfying:
--   ∀ x y z, op x y =₍U₃₎ z ↔ G(x, y, z).
--
-- The `op` field is **curried**: it takes the first argument and returns a
-- full `UnaryOperation U₂ U₃` (not a raw Lean function). This means partial
-- application `op x : U₂ ⟴ U₃` is a first-class framework operation, with
-- its own graph (the fiber at x via `BinaryOperationGraph.fiber`), its own
-- opaque symbol (`<name>_sym x`), and its own derived congruence.
--
-- The defining axiom relates the doubly-applied `op x y` to the graph's
-- ternary predicate: `(op x y =₍U₃₎ z) ↔ graph.pred x y z`.
--
-- Congruence is derived as a theorem (`BinaryOperation.cong`) from graph
-- congruence + the defining axiom — never assumed independently.
--
-- Requiring a `BinaryOperationGraph` (rather than a plain
-- `CongruentTernaryPredicate`) forces callers to discharge totality and
-- functionality before introducing the axiomatic `op` and `def`, ruling out
-- silently inconsistent declarations.

structure BinaryOperation (U₁ U₂ U₃: Universal): Type where
  graph: BinaryOperationGraph U₁ U₂ U₃
  op: U₁.Particular → UnaryOperation U₂ U₃
  «def»: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),(op x y =₍U₃₎ z) ↔ graph.pred x y z


-- Notation: a binary operation from `U₁` and `U₂` to `U₃` is written `U₁ ⟴ U₂ ⟴ U₃`.
-- Reads as the curried form, matching the implementation (op produces a unary op per x).
notation:25 U₁:26 " ⟴ " U₂:26 " ⟴ " U₃:26 => BinaryOperation U₁ U₂ U₃


-- Syntactic convenience: applying `op` to its first argument yields the unary
-- operation (the fiber at that argument). Subsequent application uses
-- `UnaryOperation`'s own CoeFun.
instance {U₁ U₂ U₃: Universal}: CoeFun (BinaryOperation U₁ U₂ U₃) (fun _ => U₁.Particular → UnaryOperation U₂ U₃) where
  coe f := f.op


-- # Derived congruence of a binary operation
--
-- Congruence is a theorem in the `BinaryOperation` namespace, not a struct
-- field. The hypothesis is **conjunctive**: `x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂ → ...`.
--
-- Proof shape (analogous to `UnaryOperation.cong`):
-- 1. By reflexivity + def forward: graph(x₁, y₁, op x₁ y₁).
-- 2. By graph cong with refl on op x₁ y₁: graph(x₂, y₂, op x₁ y₁).
-- 3. By def backward at (x₂, y₂): op x₂ y₂ =₍U₃₎ op x₁ y₁.
-- 4. By symmetry: op x₁ y₁ =₍U₃₎ op x₂ y₂.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem BinaryOperation.cong {U₁ U₂ U₃: Universal} (op: BinaryOperation U₁ U₂ U₃): ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂ → (op x₁ y₁ =₍U₃₎ op x₂ y₂) := by forall_intro
  variable(x₁: U₁.Particular)
  variable(x₂: U₁.Particular)
  variable(y₁: U₂.Particular)
  variable(y₂: U₂.Particular)
  assume(h₁: x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂)
  have h₂: x₁ =₍U₁₎ x₂ := by and_elim h₁
  have h₃: y₁ =₍U₂₎ y₂ := by and_elim h₁

  -- Step 1: graph(x₁, y₁, op x₁ y₁) via def forward + reflexivity.
  have h₄: ∀ (z: U₃.Particular), (op x₁ y₁ =₍U₃₎ z) ↔ op.graph.pred x₁ y₁ z := by forall_elim op.def, x₁, y₁
  have h₅: (op x₁ y₁ =₍U₃₎ op x₁ y₁) ↔ op.graph.pred x₁ y₁ (op x₁ y₁) := by forall_elim h₄, (op x₁ y₁)
  have h₆: op x₁ y₁ =₍U₃₎ op x₁ y₁ := by forall_elim U₃.eq.refl, (op x₁ y₁)
  have h₇: op.graph.pred x₁ y₁ (op x₁ y₁) := PC₀.deductive_eq_l2r h₅ h₆

  -- Step 2: graph(x₁, y₁, op x₁ y₁) → graph(x₂, y₂, op x₁ y₁) via combined cong.
  have h₈: x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → op x₁ y₁ =₍U₃₎ op x₁ y₁ → (op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁)) := by forall_elim op.graph.cong, x₁, x₂, y₁, y₂, (op x₁ y₁), (op x₁ y₁)
  have h₉: y₁ =₍U₂₎ y₂ → op x₁ y₁ =₍U₃₎ op x₁ y₁ → (op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁)) := by modus_ponens h₈, h₂
  have h₁₀: op x₁ y₁ =₍U₃₎ op x₁ y₁ → (op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁)) := by modus_ponens h₉, h₃
  have h₁₁: op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁) := by modus_ponens h₁₀, h₆
  have h₁₂: op.graph.pred x₂ y₂ (op x₁ y₁) := PC₀.deductive_eq_l2r h₁₁ h₇

  -- Step 3: graph(x₂, y₂, op x₁ y₁) → op x₂ y₂ =₍U₃₎ op x₁ y₁ via def backward.
  have h₁₃: ∀ (z: U₃.Particular), (op x₂ y₂ =₍U₃₎ z) ↔ op.graph.pred x₂ y₂ z := by forall_elim op.def, x₂, y₂
  have h₁₄: (op x₂ y₂ =₍U₃₎ op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁) := by forall_elim h₁₃, (op x₁ y₁)
  have h₁₅: op x₂ y₂ =₍U₃₎ op x₁ y₁ := PC₀.deductive_eq_r2l h₁₄ h₁₂

  -- Step 4: symmetry.
  have h₁₆: op x₂ y₂ =₍U₃₎ op x₁ y₁ → op x₁ y₁ =₍U₃₎ op x₂ y₂ := by forall_elim U₃.eq.sym, (op x₂ y₂), (op x₁ y₁)
  have h₁₇: op x₁ y₁ =₍U₃₎ op x₂ y₂ := by modus_ponens h₁₆, h₁₅
  iterate h₁₇


end PC₁

end Logic
