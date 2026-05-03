import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Singleton.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Singleton Universal
-- The refined universal of Set U whose particulars are singleton sets.
-- A particular of this universal is a set S bundled with a proof that
-- ∃!₍U₎ (x : U.Particular), x ∈ₛₑₜ S.
@[reducible] def SingletonSetUniversal (U: Universal): Universal := (𝐒𝐞𝐭 U) ↾ singleton_predicate
notation "𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭" => SingletonSetUniversal

def SingletonSet (U: Universal): Type := (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U).Particular


end Sets

end Universe
