import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Universals.Singleton.Predicates.Binary.Definitions.SingletonOfGraphPredicate
import Universals.Sets.Universals.Singleton.Predicates.Binary.SingletonOfGraph.Properties

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Singleton-of operation graph
--
-- The graph of the singleton construction operation: relates an element
-- `x : U.Particular` and a singleton set `S : SingletonSet U` exactly when `S`
-- contains precisely the element `x`.
--
--   pred x S  ≡  ∀ (y: U.Particular), y ∈ₛₑₜ S ↔ y =₍U₎ x
--
-- Congruence is intended to be auto-derived by the typeclass machinery. The
-- body is a universal quantification over a biconditional between membership
-- (a congruent binary predicate) and equality. Left-totality and
-- right-determinacy are imported from the `Properties/` folder.
--
-- If auto-cong fails here, that is a framework gap to be fixed in the
-- congruence machinery, not a per-operation workaround.
noncomputable def singleton_of_graph {U: Universal}: UnaryOperationGraph U (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) := UnaryOperationGraph.fromCongPred
    (singleton_of_graph_pred (U := U))
    (singleton_of_graph_left_totality)
    (singleton_of_graph_right_determinacy)


end Sets

end Universe
