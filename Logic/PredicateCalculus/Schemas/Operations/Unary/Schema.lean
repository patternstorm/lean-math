import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- In first-order logic, a unary operation op : U₁ → U₂ is defined by its graph —
-- a `UnaryOperationGraph` G(x, y) (a congruent binary predicate refined with
-- totality and functionality obligations) satisfying:
--   ∀ x y, op(x) =₍U₂₎ y ↔ G(x, y).
--
-- The structure bundles the graph (.graph), the operation function symbol (.op), and
-- the defining axiom (.def). Congruence is derived as a theorem (UnaryOperation.cong)
-- from graph congruence + the defining axiom — never assumed independently.
--
-- Requiring a `UnaryOperationGraph` (rather than a plain `CongruentBinaryPredicate`)
-- forces callers to discharge totality and functionality before introducing the
-- axiomatic `op` and `def`, ruling out silently inconsistent declarations — see
-- Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph.Schema
-- for the collapse argument.
--
-- ## How to declare a unary operation
--
-- Given a G : UnaryOperationGraph U₁ U₂, declare:
--
--     axiom my_op_sym : U₁.Particular → U₂.Particular
--     axiom my_op_def : ∀ x y, (my_op_sym x =₍U₂₎ y) ↔ (G.pred x).pred y
--     noncomputable def my_op : U₁ ⟴ U₂ :=
--       { graph := G, op := my_op_sym, def := my_op_def }
--
-- After declaration, the following are available:
--   my_op x        — apply the operation (via CoeFun)
--   my_op.graph    — the operation's graph (exposes .pred, .cong, .tot, .func)
--   my_op.def      — the defining axiom (usable via forall_elim)
--   my_op.cong     — congruence (derived theorem, never assumed)
--
-- For a one-line shortcut, see the `unary_operation` macro in
-- Logic.PredicateCalculus.Definitions.Operations.Unary.Definition.

structure UnaryOperation(U₁ U₂: Universal): Type where
  graph: UnaryOperationGraph U₁ U₂
  op: U₁.Particular → U₂.Particular
  «def»: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (op x =₍U₂₎ y) ↔ (graph.pred x).pred y

notation:25 U₁:26 " ⟴ " U₂:26 => UnaryOperation U₁ U₂

-- Syntactic convenience: allows writing op x instead of op.op x.
instance: CoeFun (U₁ ⟴ U₂) (fun _ => U₁.Particular → U₂.Particular) where
  coe f := f.op

-- Congruence is a theorem in the UnaryOperation namespace, not a field.
-- This is intentional: declaring it as an external theorem means op.cong
-- always resolves to the derived proof (from graph congruence + defining axiom).
-- A structure field with a default value could be overridden when constructing,
-- and would become an independent opaque assumption for axiom declarations.
-- The external theorem ensures congruence is always derived, never assumed.
--
-- Given a UnaryOperationGraph and the defining axiom, congruence follows:
-- 1. By reflexivity + def forward: graph(x₁, op x₁)
-- 2. By graph congruence in 1st arg: graph(x₂, op x₁)
-- 3. By def backward at x₂: op x₂ =₍U₂₎ op x₁
-- 4. By symmetry: op x₁ =₍U₂₎ op x₂
--
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-12
theorem UnaryOperation.cong (op: U₁ ⟴ U₂):
  ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), x₁ =₍U₁₎ x₂ → (op x₁ =₍U₂₎ op x₂) := by forall_intro
  variable(x₁: U₁.Particular)
  variable(x₂: U₁.Particular)
  assume(h₁: x₁ =₍U₁₎ x₂)

  -- ext(x₁, op x₁) via def forward + reflexivity
  have h₂: ∀ (y: U₂.Particular), (op x₁ =₍U₂₎ y) ↔ (op.graph.pred x₁).pred y := by forall_elim op.def, x₁
  have h₃: (op x₁ =₍U₂₎ op x₁) ↔ (op.graph.pred x₁).pred (op x₁) := by forall_elim h₂, (op x₁)
  have h₄: op x₁ =₍U₂₎ op x₁ := by forall_elim U₂.eq.refl, (op x₁)
  have h₅: (op.graph.pred x₁).pred (op x₁) := PC₀.deductive_eq_l2r h₃ h₄

  -- Graph congruence in 1st arg: graph(x₁, op x₁) → graph(x₂, op x₁)
  have h₆: ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x₁ =₍U₁₎ y → ((op.graph.pred x₁).pred z ↔ (op.graph.pred y).pred z) := by forall_elim op.graph.cong, x₁
  have h₇: ∀ (z: U₂.Particular), x₁ =₍U₁₎ x₂ → ((op.graph.pred x₁).pred z ↔ (op.graph.pred x₂).pred z) := by forall_elim h₆, x₂
  have h₈: x₁ =₍U₁₎ x₂ → ((op.graph.pred x₁).pred (op x₁) ↔ (op.graph.pred x₂).pred (op x₁)) := by forall_elim h₇, (op x₁)
  have h₉: (op.graph.pred x₁).pred (op x₁) ↔ (op.graph.pred x₂).pred (op x₁) := by modus_ponens h₈, h₁
  have h₁₀: (op.graph.pred x₂).pred (op x₁) := PC₀.deductive_eq_l2r h₉ h₅

  -- graph(x₂, op x₁) → op x₂ =₍U₂₎ op x₁ via def backward
  have h₁₁: ∀ (y: U₂.Particular), (op x₂ =₍U₂₎ y) ↔ (op.graph.pred x₂).pred y := by forall_elim op.def, x₂
  have h₁₂: (op x₂ =₍U₂₎ op x₁) ↔ (op.graph.pred x₂).pred (op x₁) := by forall_elim h₁₁, (op x₁)
  have h₁₃: op x₂ =₍U₂₎ op x₁ := PC₀.deductive_eq_r2l h₁₂ h₁₀

  -- By symmetry: op x₁ =₍U₂₎ op x₂
  have h₁₄₁: op x₂ =₍U₂₎ op x₁ → op x₁ =₍U₂₎ op x₂ := by forall_elim U₂.eq.sym, (op x₂), (op x₁)
  have h₁₄: op x₁ =₍U₂₎ op x₂ := by modus_ponens h₁₄₁, h₁₃
  iterate h₁₄

end PC₁

end Logic
