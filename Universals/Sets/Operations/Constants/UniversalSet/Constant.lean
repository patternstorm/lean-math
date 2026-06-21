import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.UniversalSetGraph

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # The `Universal Set` operation
--
-- The `constant` macro takes `universal_set_graph` as input and introduces:
-- - `universal_set_sym : Set U`                                       (opaque axiom — the constant symbol)
-- - `universal_set_satisfies : universal_set_graph.pred universal_set_sym`   (axiom — satisfies equation)
-- - `universal_set     : ConstantOperation (𝐒𝐞𝐭 U)`                   (the bundled constant operation value)
constant universal_set : (𝐒𝐞𝐭 U) from universal_set_graph
notation "Uₛₑₜ" => universal_set.op

end Sets

end Universe
