import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Instances.ConstantOperationGraph
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- In first-order logic, a constant op : U is defined by its graph — a
-- `ConstantOperationGraph` G(c) (a congruent unary predicate refined with
-- left-totality and right-determinacy) and a satisfies axiom:
--   G(op).
--
-- The structure bundles the graph (.graph), the constant function symbol
-- (.op : U.Particular), and the satisfies axiom (.satisfies : graph.pred op).
-- The derived `.cong` theorem is the 0-arity collapse of the cong shape used
-- at higher arities: with no inputs to vary, it reduces to reflexivity of
-- `=₍U₎` on the constant. The derived `.def` theorem recovers the
-- bidirectional iff form `∀ c, (op =₍U₎ c) ↔ graph.pred c` from the
-- satisfies axiom together with the graph's cong and rdet — same logical
-- content, factored to make the most common consumer use (`pred op`)
-- a single field projection.
--
-- Requiring a `ConstantOperationGraph` (rather than a plain
-- `CongruentUnaryPredicate`) forces callers to discharge left-totality and
-- right-determinacy before introducing the axiomatic `op` and `satisfies`,
-- ruling out silently inconsistent declarations — see
-- Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Instances.ConstantOperationGraph.Schema
-- for the collapse argument.
--
-- ## How to declare a constant
--
-- Given a G : ConstantOperationGraph U, declare:
--
--     axiom my_const_sym : U.Particular
--     axiom my_const_satisfies : G.pred my_const_sym
--     noncomputable def my_const : ConstantOperation U :=
--       { graph := G, op := my_const_sym, satisfies := my_const_satisfies }
--
-- After declaration, the following are available:
--   my_const            — refer to the constant directly (via Coe, behaves as U.Particular)
--   my_const.graph      — the constant's graph (exposes .pred, .cong, .ltot, .rdet)
--   my_const.satisfies  — the satisfies axiom (`graph.pred my_const.op`)
--   my_const.def        — derived defining iff `∀ c, (op =₍U₎ c) ↔ graph.pred c`
--   my_const.cong       — derived reflexivity `my_const.op =₍U₎ my_const.op`
--
-- For a one-line shortcut, see the `constant` macro in
-- Logic.PredicateCalculus.Definitions.Operations.Constant.Definition.

structure ConstantOperation (U: Universal): Type where
  graph: ConstantOperationGraph U
  op: U.Particular
  satisfies: graph.pred op

-- Transparent value access: allows using the operation directly wherever
-- `U.Particular` is expected, parallel to how `CoeFun` lets `op x` work
-- on `UnaryOperation`. A `ConstantOperation` is logically just a particular
-- with a justification — the coercion exposes the particular.
instance {U: Universal}: Coe (ConstantOperation U) U.Particular where
  coe k := k.op

-- # Derived congruence of a constant operation
--
-- At 0-arity the cong statement collapses: there are no inputs to vary, so
-- the obligation reduces to `op =₍U₎ op` — reflexivity of `=₍U₎` on the
-- constant's underlying particular. Kept as a derived theorem for symmetry
-- with `UnaryOperation.cong` and `BinaryOperation.cong`; use sites can write
-- `op.cong` instead of fishing for reflexivity.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-20
theorem ConstantOperation.cong {U: Universal} (op: ConstantOperation U): op =₍U₎ op := U.eq.refl op

-- # Derived defining iff of a constant operation
--
-- Recovers the bidirectional characterization `(op =₍U₎ c) ↔ graph.pred c`
-- from the simpler `satisfies` axiom. Both directions follow from the graph's
-- existing machinery:
--
-- - Forward (op =₍U₎ c → graph.pred c): graph.cong + satisfies.
-- - Backward (graph.pred c → op =₍U₎ c): graph.rdet + satisfies.
--
-- Same logical content as the historical `_def` axiom, derived instead of
-- axiomatized.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem ConstantOperation.«def» {U: Universal} (op: ConstantOperation U): ∀ (x: U.Particular), (op =₍U₎ x) ↔ op.graph.pred x := by forall_intro
  variable(c: U.Particular)
  -- Step 1: forward direction (op =₍U₎ c → op.graph.pred c) via graph.cong + satisfies.
  have h₁: op =₍U₎ c → op.graph.pred c := by
    assume(h₁₁: op =₍U₎ c)
    have h₁₂: op =₍U₎ c → (op.graph.pred op ↔ op.graph.pred c) := by forall_elim op.graph.cong, op, c
    have h₁₃: op.graph.pred op ↔ op.graph.pred c := by modus_ponens h₁₂, h₁₁
    have h₁₄: op.graph.pred c := PC₀.deductive_eq_l2r h₁₃ op.satisfies
    iterate h₁₄
  -- Step 2: backward direction (op.graph.pred c → op =₍U₎ c) via graph.rdet + satisfies.
  have h₂: op.graph.pred c → op =₍U₎ c := by
    assume(h₂₁: op.graph.pred c)
    have h₂₂: op.graph.pred op ∧ op.graph.pred c := by and_intro op.satisfies, h₂₁
    have h₂₃: op.graph.pred op ∧ op.graph.pred c → op =₍U₎ c := by forall_elim op.graph.rdet, op, c
    have h₂₄: op =₍U₎ c := by modus_ponens h₂₃, h₂₂
    iterate h₂₄
  -- Step 3: combine via iff_intro.
  have h₃: (op =₍U₎ c) ↔ op.graph.pred c := by iff_intro h₁, h₂
  iterate h₃

end PC₁

end Logic
