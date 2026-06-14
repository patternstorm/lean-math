import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Ternary.Definitions.UnionGraphPredicate
import Universals.Sets.Predicates.Ternary.UnionGraph.Properties

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Union operation graph
--
-- The graph of the union operation: relates `A B : Set U` to `C : Set U`
-- exactly when `C`'s members are precisely those in `A` or in `B`.
--
--   pred A B C  ≡  ∀ x : U.Particular, x ∈ₛₑₜ C ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B)
--
-- The ternary congruence is **auto-derived** by the typeclass machinery:
-- the body `union_graph_pred` (a `@[reducible]` def) unfolds during synthesis,
-- and the chain `congruent_ternary_from_fibers → congruent_universal →
-- congruent_iff → (congruent_disjunction, fiber_*_binary_congruent_unary,
-- congruent_constant)` produces a `CongruentTernary` instance, which the
-- `CoeDep` coercion turns into a `CongruentTernaryPredicate`. Left-totality
-- and right-determinacy are imported from the `Properties/` folder.
noncomputable def union_graph {U: Universal}: BinaryOperationGraph (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) := BinaryOperationGraph.fromCongPred
    (union_graph_pred (U := U) : CongruentTernaryPredicate (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U))
    (union_graph_left_totality (U := U))
    (union_graph_right_determinacy (U := U))


end Sets

end Universe
