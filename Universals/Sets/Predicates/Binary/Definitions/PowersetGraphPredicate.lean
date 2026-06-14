import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Inclusion.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Powerset graph predicate
-- "P is the powerset of S": the body predicate underlying `powerset_graph`.
-- Factored out as a plain `def` so the graph value (`Predicate.lean`), its
-- left-totality / right-determinacy theorems (`Properties/*.lean`), and any
-- future downstream consumer can all reference the same notion by name.
@[reducible] def powerset_graph_pred {U: Universal} (S: Set U) (P: Set (𝐒𝐞𝐭 U)): Prop := ∀ (S': Set U), S' ∈ₛₑₜ P ↔ S' ⊆ₛₑₜ S


end Sets

end Universe
