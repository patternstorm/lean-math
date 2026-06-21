import Logic
import Universe
import Universals.Sets.Operations.Constants.EmptySet.Constant
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Operations.Constants.EmptySet.Properties.ContainsNoElements

namespace Universe
namespace Sets

open Logic
open Logic.PC₁

-- The `Empty Set` exists.
--
-- In ZFC, the empty set is either postulated via the Axiom of Empty Set, or derived
-- from the Axiom of Infinity plus Separation. This creates a curious dependency: the
-- simplest set (empty) relies on the existence of an infinite set — foundationally
-- backwards.
--
-- Our predicate-based approach avoids this. The predicate `x: U.Particular ↦ False` is well-formed
-- over any Universal, regardless of what else exists. The empty set is simply the
-- extension of this trivially valid predicate — no infinite sets required.

theorem empty_set_existence: ∃ (S: Set U), ∀ (x: U.Particular), x ∉ₛₑₜ S := empty_set_graph.ltot

end Sets

end Universe
