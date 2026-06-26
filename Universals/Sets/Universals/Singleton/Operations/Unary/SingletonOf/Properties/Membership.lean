import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Universals.Singleton.Predicates.Binary.SingletonOfGraph
import Universals.Sets.Universals.Singleton.Universal
import Universals.Sets.Universals.Singleton.Operations.Unary.SingletonOf.Operation

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Singleton-of membership characterization
--
-- The singleton set `{x}ₛₑₜ` contains exactly the element `x`.
-- Derived from the satisfies axiom `singleton_of.satisfies`, which
-- unfolds to `∀ y, y ∈ₛₑₜ {x}ₛₑₜ ↔ y =₍U₎ x`.
--
-- Proof by Kimi K2.7, 2026-06-26
theorem singleton_of_membership {U: Universal}: ∀ (x: U.Particular), ∀ (y: U.Particular), y ∈ₛₑₜ {x}ₛₑₜ ↔ y =₍U₎ x := by
  have h₁: ∀ (x: U.Particular), ∀ (y: U.Particular), y ∈ₛₑₜ {x}ₛₑₜ ↔ y =₍U₎ x := singleton_of.satisfies
  iterate h₁


end Sets

end Universe
