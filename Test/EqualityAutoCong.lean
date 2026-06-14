import Universals.Sets

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Test: auto-cong fires on equality bodies via the framework's
-- `congruent_equal_to` / `congruent_equal_from` instances.
--
-- Coverage:
--   - the generic `=₍U₎` notation
--   - composition with other connectives (∨, ∧, etc.)
--   - the Universal-specific alias `=ₛₑₜ` (works because the alias is defined
--     to expand via `=₍SetsUniversal _₎`, preserving the universe parameter
--     in the elaborated form so the auto-cong instances can match)

example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ x =₍U₎ a) := inferInstance
example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ a =₍U₎ x) := inferInstance
example {U: Universal} (a b: U.Particular) : CongruentUnary U (x: U.Particular ↦ x =₍U₎ a ∨ x =₍U₎ b) := inferInstance
example {U: Universal} (A: Set U) : CongruentUnary (𝐒𝐞𝐭 U) (S: Set U ↦ S =ₛₑₜ A) := inferInstance

end Sets

end Universe
