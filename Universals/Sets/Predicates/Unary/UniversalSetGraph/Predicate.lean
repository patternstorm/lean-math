import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Definitions.UniversalSetGraphPredicate
import Universals.Sets.Predicates.Unary.UniversalSetGraph.Properties

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Universal set operation graph
--
-- The graph of the universal set constant: relates a set `X : Set U` to the
-- constant exactly when `X` contains all elements.
--
--   pred X  ≡  ∀ x : U.Particular, x ∈ₛₑₜ X
--
-- The unary congruence is auto-derived by the typeclass machinery: the body
-- `universal_set_graph_pred` is `@[reducible]`, and `x ∈ₛₑₜ X` is a congruent
-- binary predicate in `X` for each fixed `x`, so universal quantification
-- preserves congruence. Left-totality and right-determinacy are imported
-- from the `Properties/` folder.
noncomputable def universal_set_graph {U: Universal}: ConstantOperationGraph (𝐒𝐞𝐭 U) := ConstantOperationGraph.fromCongPred
    (universal_set_graph_pred (U := U))
    (universal_set_graph_left_totality)
    (universal_set_graph_right_determinacy)


end Sets

end Universe
