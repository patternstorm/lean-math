import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Universals.Singleton.Predicates.Binary.SingletonOfGraph
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Singleton Of Operation
--
-- Constructs the singleton set {x} for a given element x.
-- Returns a particular of the Singleton sub-universal (a set proven to be a singleton).
--
-- The `unary_operation` macro takes `singleton_of_graph` as input and introduces:
-- - `singleton_of_sym : U.Particular → SingletonSet U`                      (opaque axiom)
-- - `singleton_of_satisfies : ∀ x, singleton_of_graph.pred x (singleton_of_sym x)` (satisfies axiom)
-- - `singleton_of : UnaryOperation U (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U)`                    (bundled operation value)
unary_operation singleton_of : U ⟴ (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) from singleton_of_graph
macro "{" x:term "}ₛₑₜ" : term => `(singleton_of.op $x)

end Sets

end Universe
