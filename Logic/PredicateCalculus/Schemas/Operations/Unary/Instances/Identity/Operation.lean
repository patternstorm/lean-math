import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph
import Logic.PredicateCalculus.Definitions.Operations.Unary.Definition

-- # Identity — the UnaryOperation U ⟴ U whose graph is the universal equality
--
-- The graph for the identity operation is `equals` lifted to a `UnaryOperationGraph U U` by discharging:
-- - `equals_left_totality` — every `x` has at least one related `y` (witness `x` itself, by reflexivity),
-- - `equals_right_determinacy` — any two related `y`s coincide (by sym + trans).
--
-- The `unary_operation identity ... from identity_graph` macro then generates:
-- - axiom `identity_sym : U.Particular → U.Particular` — the operation function symbol,
-- - axiom `identity_def : ∀ x y, (identity_sym x =₍U₎ y) ↔ (identity_graph.pred x).pred y` — defining axiom,
-- - `noncomputable def identity : U ⟴ U := { graph := identity_graph, op := identity_sym, def := identity_def }`.
--
-- Since `(identity_graph.pred x).pred y` reduces to `x =₍U₎ y` (the inherited
-- `equals` graph, domain-first convention), the defining axiom reads:
--   identity_sym x =₍U₎ y ↔ x =₍U₎ y.

namespace Logic

namespace PC₁

-- The identity operation's graph: `equals` refined with left-totality and right-determinacy.
def identity_graph {U: Universal}: UnaryOperationGraph U U :=
  { equals with
    ltot := equals_left_totality,
    rdet := equals_right_determinacy }

unary_operation identity : U ⟴ U from identity_graph

end PC₁

end Logic
