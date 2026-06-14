import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Union graph predicate
-- "C is the union of A and B": the body predicate underlying `union_graph`.
-- Factored out as a plain `def` so the graph value (`Predicate.lean`), its
-- left-totality / right-determinacy theorems (`Properties/*.lean`), and any
-- future downstream consumer can all reference the same notion by name.
@[reducible] def union_graph_pred {U: Universal} (A: Set U) (B: Set U) (C: Set U): Prop := ∀ (x: U.Particular), x ∈ₛₑₜ C ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B)


end Sets

end Universe
