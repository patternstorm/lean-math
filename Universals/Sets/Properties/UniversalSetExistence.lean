import Logic
import Universe
import Universals.Sets.Operations.Constants.UniversalSet.Constant
import Universals.Sets.Predicates.Unary.UniversalSetGraph

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- The `Universal Set` exists.
--
-- In contrast to ZFC, where the universal set does not exist (due to Russell's paradox
-- and restricted comprehension), our predicate-based approach allows the universal set
-- to exist: the predicate `x: U.Particular ↦ True` is well-formed and its extension is the set of
-- all particulars.
--
-- Existence is obtained directly from the graph's left-totality obligation.
theorem universal_set_existence : ∃ (S: Set U), ∀ (x: U.Particular), x ∈ₛₑₜ S := universal_set_graph.ltot

end Sets

end Universe
