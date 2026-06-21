import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.EmptySetGraph

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # The `Empty Set` operation
--
-- The `constant` macro takes `empty_set_graph` as input and introduces:
-- - `empty_set_sym : Set U`                                       (opaque axiom — the constant symbol)
-- - `empty_set_def : ∀ (X: Set U), (empty_set_sym =ₛₑₜ X) ↔ empty_set_graph.pred X`   (axiom — defining equation)
-- - `empty_set     : ConstantOperation (𝐒𝐞𝐭 U)`                   (the bundled constant operation value)
constant empty_set : (𝐒𝐞𝐭 U) from empty_set_graph
notation "∅ₛₑₜ" => empty_set.op

end Sets

end Universe
