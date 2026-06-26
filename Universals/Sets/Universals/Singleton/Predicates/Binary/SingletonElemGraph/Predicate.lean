import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Universals.Singleton.Predicates.Binary.Definitions.SingletonElemGraphPredicate
import Universals.Sets.Universals.Singleton.Predicates.Binary.SingletonElemGraph.Properties
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Singleton element operation graph
--
-- The graph of the singleton-element extraction operation: relates a
-- singleton set `S : SingletonSet U` and a particular `y : U.Particular`
-- exactly when `y` is a member of the underlying set.
--
--   pred S y  ≡  y ∈ₛₑₜ S
--
-- The binary congruence is auto-derived by the typeclass machinery: the body
-- `singleton_elem_graph_pred` is `@[reducible]`, and `y ∈ₛₑₜ S` is a congruent
-- binary predicate in both arguments. Left-totality and right-determinacy
-- are imported from the `Properties/` folder.
noncomputable def singleton_elem_graph {U: Universal}: UnaryOperationGraph (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) U := UnaryOperationGraph.fromCongPred
    (singleton_elem_graph_pred (U := U))
    (singleton_elem_graph_left_totality)
    (singleton_elem_graph_right_determinacy)


end Sets

end Universe
