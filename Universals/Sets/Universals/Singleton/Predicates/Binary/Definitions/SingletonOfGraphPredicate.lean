import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Singleton-of graph predicate
-- "x maps to S under singleton construction": the body predicate underlying
-- `singleton_of_graph`.
--
-- A `SingletonSet U` is a subuniversal of `Set U`. The graph holds when every
-- particular belongs to `S` exactly when it equals `x`.
@[reducible] def singleton_of_graph_pred {U: Universal} (x: U.Particular) (S: SingletonSet U): Prop :=
  ∀ (y: U.Particular), y ∈ₛₑₜ S ↔ y =₍U₎ x


end Sets

end Universe
