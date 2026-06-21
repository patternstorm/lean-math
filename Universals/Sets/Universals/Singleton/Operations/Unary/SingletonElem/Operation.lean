import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.SingletonElemGraph
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Singleton Element Extraction
--
-- Extracts the unique element from a singleton set.
--
-- The `unary_operation` macro takes `singleton_elem_graph` as input and introduces:
-- - `singleton_elem_sym : SingletonSet U → U.Particular`              (opaque axiom)
-- - `singleton_elem_satisfies : ∀ S, singleton_elem_graph.pred S (singleton_elem_sym S)` (satisfies axiom)
-- - `singleton_elem : UnaryOperation (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) U`            (bundled operation value)
unary_operation singleton_elem : (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) ⟴ U from singleton_elem_graph
prefix:max "⊙" => singleton_elem.op

end Sets

end Universe
