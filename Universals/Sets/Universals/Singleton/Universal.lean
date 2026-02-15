import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Singleton.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Singleton Universal
-- The sub-universal of Set U whose particulars are singleton sets.
-- A particular of this universal is a set S bundled with a proof that
-- ∃!₍U₎ (x : U.Particular), x ∈ₛₑₜ S.
def SingletonSet (U: Universal): Universal := sub_universal (Set U) singleton_predicate

end Sets

end Universe
