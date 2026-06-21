import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.UniversalSetGraph
import Universals.Sets.Operations.Constants.UniversalSet.Constant

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- The `Universal Set` contains all `Particulars`.
-- Derived directly from the satisfies axiom `universal_set.satisfies`, which
-- unfolds (via the `@[reducible]` `universal_set_graph_pred`) to `∀ x, x ∈ₛₑₜ Uₛₑₜ`.
-- Proof by Kimi K2.7, 2026-06-21
theorem universal_set_contains_all_elements {U: Universal}: ∀ (x: U.Particular), x ∈ₛₑₜ Uₛₑₜ := universal_set.satisfies


end Sets

end Universe
