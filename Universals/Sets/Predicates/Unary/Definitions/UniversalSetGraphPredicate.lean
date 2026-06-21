import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Universal set graph predicate
-- "S is the universal set": the body predicate underlying `universal_set_graph`.
-- Factored out as a plain `@[reducible] def` so the graph value, its
-- left-totality / right-determinacy theorems, and any downstream consumer
-- can all reference the same notion by name.
@[reducible] def universal_set_graph_pred {U: Universal} (S: Set U): Prop := ∀ (x: U.Particular), x ∈ₛₑₜ S


end Sets

end Universe
