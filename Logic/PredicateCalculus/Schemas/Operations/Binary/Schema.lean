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
-- predicate refined with left-totality and right-determinacy on the third
-- argument) and a satisfies axiom:
--   ∀ x y, G(x, y, op x y).
--
-- The `op` field is **curried**: it takes the first argument and returns a
-- full `UnaryOperation U₂ U₃` (not a raw Lean function). This means partial
-- application `op x : U₂ ⟴ U₃` is a first-class framework operation, with
-- its own graph (the fiber at x via `BinaryOperationGraph.fiber`), its own
-- opaque symbol (`<name>_sym x`), and its own derived congruence.
--
-- The satisfies axiom relates the doubly-applied `op x y` to the graph's
-- ternary predicate: `graph.pred x y (op x y)`.
--
-- Congruence is derived as a theorem (`BinaryOperation.cong`) from graph
-- machinery + satisfies. The derived `BinaryOperation.def` theorem recovers
-- the bidirectional iff form `∀ x y z, (op x y =₍U₃₎ z) ↔ graph.pred x y z`
-- from satisfies + graph.cong + graph.rdet — same logical content, factored
-- to make the most common consumer use (graph.pred x y (op x y)) a single
-- field projection.
--
-- Requiring a `BinaryOperationGraph` (rather than a plain
-- `CongruentTernaryPredicate`) forces callers to discharge left-totality and
-- right-determinacy before introducing the axiomatic `op` and `satisfies`,
-- ruling out silently inconsistent declarations.

structure BinaryOperation (U₁ U₂ U₃: Universal): Type where
  graph: BinaryOperationGraph U₁ U₂ U₃
  op: U₁.Particular → UnaryOperation U₂ U₃
  satisfies: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), graph.pred x y (op x y)


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
-- Cong follows directly from the graph's machinery + satisfies (parallel to
-- UnaryOperation.cong, just at one higher arity):
-- 1. graph.pred x₁ y₁ (op x₁ y₁) from satisfies (x₁, y₁).
-- 2. graph.cong combined with refl on op x₁ y₁ + x₁ =₍U₁₎ x₂ + y₁ =₍U₂₎ y₂:
--    graph.pred x₁ y₁ (op x₁ y₁) ↔ graph.pred x₂ y₂ (op x₁ y₁).
-- 3. graph.pred x₂ y₂ (op x₁ y₁) by transfer.
-- 4. graph.pred x₂ y₂ (op x₂ y₂) from satisfies (x₂, y₂).
-- 5. graph.rdet at (x₂, y₂): graph.pred x₂ y₂ (op x₁ y₁) ∧ graph.pred x₂ y₂ (op x₂ y₂)
--    → op x₁ y₁ =₍U₃₎ op x₂ y₂.
--
-- Hypothesis is **conjunctive**: `x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂ → ...`.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem BinaryOperation.cong {U₁ U₂ U₃: Universal} (op: BinaryOperation U₁ U₂ U₃): ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂ → (op x₁ y₁ =₍U₃₎ op x₂ y₂) := by forall_intro
  variable(x₁: U₁.Particular)
  variable(x₂: U₁.Particular)
  variable(y₁: U₂.Particular)
  variable(y₂: U₂.Particular)
  assume(h₁: x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂)
  have h₂: x₁ =₍U₁₎ x₂ := by and_elim h₁
  have h₃: y₁ =₍U₂₎ y₂ := by and_elim h₁
  -- Step 1: graph.pred x₁ y₁ (op x₁ y₁) from satisfies.
  have h₄: op.graph.pred x₁ y₁ (op x₁ y₁) := by forall_elim op.satisfies, x₁, y₁
  -- Step 2: combined cong with refl on op x₁ y₁ + h₂ + h₃ to transfer.
  have h₅: x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → op x₁ y₁ =₍U₃₎ op x₁ y₁ → (op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁)) := by forall_elim op.graph.cong, x₁, x₂, y₁, y₂, (op x₁ y₁), (op x₁ y₁)
  have h₆: op x₁ y₁ =₍U₃₎ op x₁ y₁ := by forall_elim U₃.eq.refl, (op x₁ y₁)
  have h₇: y₁ =₍U₂₎ y₂ → op x₁ y₁ =₍U₃₎ op x₁ y₁ → (op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁)) := by modus_ponens h₅, h₂
  have h₈: op x₁ y₁ =₍U₃₎ op x₁ y₁ → (op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁)) := by modus_ponens h₇, h₃
  have h₉: op.graph.pred x₁ y₁ (op x₁ y₁) ↔ op.graph.pred x₂ y₂ (op x₁ y₁) := by modus_ponens h₈, h₆
  have h₁₀: op.graph.pred x₂ y₂ (op x₁ y₁) := PC₀.deductive_eq_l2r h₉ h₄
  -- Step 3: graph.pred x₂ y₂ (op x₂ y₂) from satisfies.
  have h₁₁: op.graph.pred x₂ y₂ (op x₂ y₂) := by forall_elim op.satisfies, x₂, y₂
  -- Step 4: rdet collapses the two witnesses to op x₁ y₁ =₍U₃₎ op x₂ y₂.
  have h₁₂: op.graph.pred x₂ y₂ (op x₁ y₁) ∧ op.graph.pred x₂ y₂ (op x₂ y₂) := by and_intro h₁₀, h₁₁
  have h₁₃: op.graph.pred x₂ y₂ (op x₁ y₁) ∧ op.graph.pred x₂ y₂ (op x₂ y₂) → op x₁ y₁ =₍U₃₎ op x₂ y₂ := by forall_elim op.graph.rdet, x₂, y₂, (op x₁ y₁), (op x₂ y₂)
  have h₁₄: op x₁ y₁ =₍U₃₎ op x₂ y₂ := by modus_ponens h₁₃, h₁₂
  iterate h₁₄


-- # Derived defining iff of a binary operation
--
-- Recovers the bidirectional characterization
-- `∀ x y z, (op x y =₍U₃₎ z) ↔ graph.pred x y z` from the simpler satisfies
-- axiom + graph machinery. Both directions follow from the graph's existing
-- machinery:
--
-- - Forward (op x y =₍U₃₎ z → graph.pred x y z): graph.cong instantiated with
--   refl on x, y + the given z-equality, transferred via satisfies.
-- - Backward (graph.pred x y z → op x y =₍U₃₎ z): graph.rdet at (x, y) +
--   satisfies.
--
-- Same logical content as the historical `_def` axiom, derived instead of
-- axiomatized.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem BinaryOperation.«def» {U₁ U₂ U₃: Universal} (op: BinaryOperation U₁ U₂ U₃): ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
      (op x y =₍U₃₎ z) ↔ op.graph.pred x y z := by forall_intro
  variable(x: U₁.Particular)
  variable(y: U₂.Particular)
  variable(z: U₃.Particular)
  -- Step 0: extract graph.pred x y (op x y) from satisfies — used by both directions.
  have h₀: op.graph.pred x y (op x y) := by forall_elim op.satisfies, x, y
  -- Step 1: forward direction (op x y =₍U₃₎ z → graph.pred x y z) via graph.cong + satisfies.
  have h₁: op x y =₍U₃₎ z → op.graph.pred x y z := by
    assume(h₁₁: op x y =₍U₃₎ z)
    have h₁₂: x =₍U₁₎ x → y =₍U₂₎ y → op x y =₍U₃₎ z → (op.graph.pred x y (op x y) ↔ op.graph.pred x y z) := by forall_elim op.graph.cong, x, x, y, y, (op x y), z
    have h₁₃: x =₍U₁₎ x := by forall_elim U₁.eq.refl, x
    have h₁₄: y =₍U₂₎ y := by forall_elim U₂.eq.refl, y
    have h₁₅: y =₍U₂₎ y → op x y =₍U₃₎ z → (op.graph.pred x y (op x y) ↔ op.graph.pred x y z) := by modus_ponens h₁₂, h₁₃
    have h₁₆: op x y =₍U₃₎ z → (op.graph.pred x y (op x y) ↔ op.graph.pred x y z) := by modus_ponens h₁₅, h₁₄
    have h₁₇: op.graph.pred x y (op x y) ↔ op.graph.pred x y z := by modus_ponens h₁₆, h₁₁
    have h₁₈: op.graph.pred x y z := PC₀.deductive_eq_l2r h₁₇ h₀
    iterate h₁₈
  -- Step 2: backward direction (graph.pred x y z → op x y =₍U₃₎ z) via graph.rdet + satisfies.
  have h₂: op.graph.pred x y z → op x y =₍U₃₎ z := by
    assume(h₂₁: op.graph.pred x y z)
    have h₂₂: op.graph.pred x y (op x y) ∧ op.graph.pred x y z := by and_intro h₀, h₂₁
    have h₂₃: op.graph.pred x y (op x y) ∧ op.graph.pred x y z → op x y =₍U₃₎ z := by forall_elim op.graph.rdet, x, y, (op x y), z
    have h₂₄: op x y =₍U₃₎ z := by modus_ponens h₂₃, h₂₂
    iterate h₂₄
  -- Step 3: combine via iff_intro.
  have h₃: (op x y =₍U₃₎ z) ↔ op.graph.pred x y z := by iff_intro h₁, h₂
  iterate h₃


end PC₁

end Logic
