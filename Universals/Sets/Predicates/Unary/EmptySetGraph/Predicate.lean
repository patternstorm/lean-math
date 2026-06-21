import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Definitions.EmptySetGraphPredicate
import Universals.Sets.Predicates.Unary.EmptySetGraph.Properties

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Empty set operation graph
--
-- The graph of the empty set constant: relates a set `X : Set U` to the
-- constant exactly when `X` contains no elements.
--
--   pred X  ≡  ∀ x : U.Particular, x ∉ₛₑₜ X
--
-- The unary congruence is auto-derived by the typeclass machinery: the body
-- `empty_set_graph_pred` is `@[reducible]`, and `x ∉ₛₑₜ X` is a congruent
-- binary predicate in `X` for each fixed `x`, so universal quantification
-- preserves congruence. Left-totality and right-determinacy are imported
-- from the `Properties/` folder.
noncomputable def empty_set_graph {U: Universal}: ConstantOperationGraph (𝐒𝐞𝐭 U) := ConstantOperationGraph.fromCongPred
    (empty_set_graph_pred (U := U) : CongruentUnaryPredicate (𝐒𝐞𝐭 U))
    (empty_set_graph_left_totality (U := U))
    (empty_set_graph_right_determinacy (U := U))


end Sets

end Universe
