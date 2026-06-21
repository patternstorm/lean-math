import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- In first-order logic, a unary operation op : U₁ → U₂ is defined by its graph —
-- a `UnaryOperationGraph` G(x, y) (a congruent binary predicate refined with
-- left-totality and right-determinacy) and a satisfies axiom:
--   ∀ x, G(x, op x).
--
-- The structure bundles the graph (.graph), the operation function symbol (.op),
-- and the satisfies axiom (.satisfies : ∀ x, graph.pred x (op x)). The derived
-- `.cong` theorem (UnaryOperation.cong) gives congruence from graph cong + rdet
-- + satisfies. The derived `.def` theorem (UnaryOperation.def) recovers the
-- bidirectional iff form `∀ x y, (op x =₍U₂₎ y) ↔ graph.pred x y` from the
-- satisfies axiom together with the graph's cong and rdet — same logical
-- content, factored to make the most common consumer use (graph.pred x (op x))
-- a single field projection.
--
-- Requiring a `UnaryOperationGraph` (rather than a plain `CongruentBinaryPredicate`)
-- forces callers to discharge left-totality and right-determinacy before
-- introducing the axiomatic `op` and `satisfies`, ruling out silently
-- inconsistent declarations — see
-- Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph.Schema
-- for the collapse argument.
--
-- ## How to declare a unary operation
--
-- Given a G : UnaryOperationGraph U₁ U₂, declare:
--
--     axiom my_op_sym : U₁.Particular → U₂.Particular
--     axiom my_op_satisfies : ∀ x, G.pred x (my_op_sym x)
--     noncomputable def my_op : U₁ ⟴ U₂ :=
--       { graph := G, op := my_op_sym, satisfies := my_op_satisfies }
--
-- After declaration, the following are available:
--   my_op x          — apply the operation (via CoeFun)
--   my_op.graph      — the operation's graph (exposes .pred, .cong, .ltot, .rdet)
--   my_op.satisfies  — the satisfies axiom (`∀ x, graph.pred x (op x)`)
--   my_op.def        — derived defining iff `∀ x y, (op x =₍U₂₎ y) ↔ graph.pred x y`
--   my_op.cong       — derived congruence (never assumed)
--
-- For a one-line shortcut, see the `unary_operation` macro in
-- Logic.PredicateCalculus.Definitions.Operations.Unary.Definition.

structure UnaryOperation(U₁ U₂: Universal): Type where
  graph: UnaryOperationGraph U₁ U₂
  op: U₁.Particular → U₂.Particular
  satisfies: ∀ (x: U₁.Particular), graph.pred x (op x)

notation:25 U₁:26 " ⟴ " U₂:26 => UnaryOperation U₁ U₂

-- Syntactic convenience: allows writing op x instead of op.op x.
instance: CoeFun (U₁ ⟴ U₂) (fun _ => U₁.Particular → U₂.Particular) where
  coe f := f.op

-- # Derived congruence of a unary operation
--
-- Cong follows directly from the graph's machinery + satisfies:
-- 1. graph.pred x₁ (op x₁) from satisfies x₁.
-- 2. graph.cong combined with refl on op x₁ + x₁ =₍U₁₎ x₂:
--    graph.pred x₁ (op x₁) ↔ graph.pred x₂ (op x₁).
-- 3. graph.pred x₂ (op x₁) by transfer.
-- 4. graph.pred x₂ (op x₂) from satisfies x₂.
-- 5. graph.rdet at x₂: graph.pred x₂ (op x₁) ∧ graph.pred x₂ (op x₂) → op x₁ =₍U₂₎ op x₂.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem UnaryOperation.cong (op: U₁ ⟴ U₂): ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), x₁ =₍U₁₎ x₂ → (op x₁ =₍U₂₎ op x₂) := by forall_intro
  variable(x₁: U₁.Particular)
  variable(x₂: U₁.Particular)
  assume(h₁: x₁ =₍U₁₎ x₂)
  -- Step 1: graph.pred x₁ (op x₁) from satisfies.
  have h₂: op.graph.pred x₁ (op x₁) := by forall_elim op.satisfies, x₁
  -- Step 2: combined cong with refl on op x₁ + h₁ to transfer.
  have h₃: x₁ =₍U₁₎ x₂ → op x₁ =₍U₂₎ op x₁ → (op.graph.pred x₁ (op x₁) ↔ op.graph.pred x₂ (op x₁)) := by forall_elim op.graph.cong, x₁, x₂, (op x₁), (op x₁)
  have h₄: op x₁ =₍U₂₎ op x₁ := by forall_elim U₂.eq.refl, (op x₁)
  have h₅: op x₁ =₍U₂₎ op x₁ → (op.graph.pred x₁ (op x₁) ↔ op.graph.pred x₂ (op x₁)) := by modus_ponens h₃, h₁
  have h₆: op.graph.pred x₁ (op x₁) ↔ op.graph.pred x₂ (op x₁) := by modus_ponens h₅, h₄
  have h₇: op.graph.pred x₂ (op x₁) := PC₀.deductive_eq_l2r h₆ h₂
  -- Step 3: graph.pred x₂ (op x₂) from satisfies.
  have h₈: op.graph.pred x₂ (op x₂) := by forall_elim op.satisfies, x₂
  -- Step 4: graph.rdet at x₂ collapses the two witnesses to op x₁ =₍U₂₎ op x₂.
  have h₉: op.graph.pred x₂ (op x₁) ∧ op.graph.pred x₂ (op x₂) := by and_intro h₇, h₈
  have h₁₀: op.graph.pred x₂ (op x₁) ∧ op.graph.pred x₂ (op x₂) → op x₁ =₍U₂₎ op x₂ := by forall_elim op.graph.rdet, x₂, (op x₁), (op x₂)
  have h₁₁: op x₁ =₍U₂₎ op x₂ := by modus_ponens h₁₀, h₉
  iterate h₁₁

-- # Derived defining iff of a unary operation
--
-- Recovers the bidirectional characterization `∀ x y, (op x =₍U₂₎ y) ↔ graph.pred x y`
-- from the simpler `satisfies` axiom. Both directions follow from the graph's
-- existing machinery:
--
-- - Forward (op x =₍U₂₎ y → graph.pred x y): graph.cong instantiated with
--   refl on x + the given y-equality, transferred via satisfies.
-- - Backward (graph.pred x y → op x =₍U₂₎ y): graph.rdet at x + satisfies.
--
-- Same logical content as the historical `_def` axiom, derived instead of
-- axiomatized.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem UnaryOperation.«def» (op: U₁ ⟴ U₂): ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (op x =₍U₂₎ y) ↔ op.graph.pred x y := by forall_intro
  variable(x: U₁.Particular)
  variable(y: U₂.Particular)
  -- Step 0: extract graph.pred x (op x) from satisfies — used by both directions.
  have h₀: op.graph.pred x (op x) := by forall_elim op.satisfies, x
  -- Step 1: forward direction (op x =₍U₂₎ y → graph.pred x y) via graph.cong + satisfies.
  have h₁: op x =₍U₂₎ y → op.graph.pred x y := by
    assume(h₁₁: op x =₍U₂₎ y)
    have h₁₂: x =₍U₁₎ x → op x =₍U₂₎ y → (op.graph.pred x (op x) ↔ op.graph.pred x y) := by forall_elim op.graph.cong, x, x, (op x), y
    have h₁₃: x =₍U₁₎ x := by forall_elim U₁.eq.refl, x
    have h₁₄: op x =₍U₂₎ y → (op.graph.pred x (op x) ↔ op.graph.pred x y) := by modus_ponens h₁₂, h₁₃
    have h₁₅: op.graph.pred x (op x) ↔ op.graph.pred x y := by modus_ponens h₁₄, h₁₁
    have h₁₆: op.graph.pred x y := PC₀.deductive_eq_l2r h₁₅ h₀
    iterate h₁₆
  -- Step 2: backward direction (graph.pred x y → op x =₍U₂₎ y) via graph.rdet + satisfies.
  have h₂: op.graph.pred x y → op x =₍U₂₎ y := by
    assume(h₂₁: op.graph.pred x y)
    have h₂₂: op.graph.pred x (op x) ∧ op.graph.pred x y := by and_intro h₀, h₂₁
    have h₂₃: op.graph.pred x (op x) ∧ op.graph.pred x y → op x =₍U₂₎ y := by forall_elim op.graph.rdet, x, (op x), y
    have h₂₄: op x =₍U₂₎ y := by modus_ponens h₂₃, h₂₂
    iterate h₂₄
  -- Step 3: combine via iff_intro.
  have h₃: (op x =₍U₂₎ y) ↔ op.graph.pred x y := by iff_intro h₁, h₂
  iterate h₃

end PC₁

end Logic
