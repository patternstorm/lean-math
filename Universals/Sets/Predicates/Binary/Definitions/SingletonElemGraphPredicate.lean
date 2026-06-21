import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Singleton element graph predicate
-- "S maps to y under singleton-element extraction": the body predicate
-- underlying `singleton_elem_graph`.
--
-- A `SingletonSet U` is a subtype of `Set U` whose carrier `S.val` is a
-- singleton. The graph holds when `y` is a member of that carrier.
@[reducible] def singleton_elem_graph_pred {U: Universal} (S: SingletonSet U) (y: U.Particular): Prop := y ∈ₛₑₜ S


end Sets

end Universe
