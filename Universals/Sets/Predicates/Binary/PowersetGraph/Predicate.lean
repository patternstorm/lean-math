import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Inclusion.Predicate
import Universals.Sets.Predicates.Binary.Definitions.PowersetGraphPredicate
import Universals.Sets.Predicates.Binary.PowersetGraph.Properties

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Powerset operation graph
--
-- The graph of the powerset operation: relates `S : Set U` to
-- `P : Set (𝐒𝐞𝐭 U)` exactly when `P` is the set of all subsets of `S`.
--
--   pred S P  ≡  ∀ S' : Set U, S' ∈ₛₑₜ P ↔ S' ⊆ₛₑₜ S
--
-- The binary congruence is **auto-derived** by the typeclass machinery: the
-- body `powerset_graph_pred` (a `@[reducible]` def) unfolds during synthesis,
-- and the chain `congruent_binary_from_fibers → congruent_universal →
-- congruent_iff → (fiber_*_binary_congruent_unary, congruent_constant)`
-- produces a `CongruentBinary` instance from which we combine the per-arg
-- congs into a single combined cong via `binary_congruence_from_congruent_fibers`.
-- Left-totality and right-determinacy are imported from the `Properties/` folder.
noncomputable def powerset_graph {U: Universal}: UnaryOperationGraph (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 (𝐒𝐞𝐭 U)) := UnaryOperationGraph.fromCongPred
    (powerset_graph_pred (U := U) : CongruentBinaryPredicate (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 (𝐒𝐞𝐭 U)))
    (powerset_graph_left_totality (U := U))
    (powerset_graph_right_determinacy (U := U))


end Sets

end Universe
