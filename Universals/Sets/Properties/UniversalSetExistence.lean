import Logic
import Universe
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Operations.Constants.UniversalSet.Constant
import Universals.Sets.Operations.Constants.UniversalSet.Properties.ContainsAllElements

namespace Universe

namespace Sets

-- The `Universal Set` exists and contains all `Particulars`.
--
-- Note: The `def universal_set` is a Lean definition that names a specific predicate,
-- but in first-order logic, a definition alone does not constitute an existence proof.
-- This theorem provides the actual FOL existence claim (∃), using `Uₛₑₜ` as the witness.
-- This is necessary because our framework is based on FOL, not type theory — existence
-- must be stated explicitly with ∃, even when we have a concrete definition.
--
-- In contrast to ZFC, where the universal set does not exist (due to Russell's paradox
-- and restricted comprehension), our predicate-based approach allows the universal set
-- to exist: the predicate `x: U.Particular ↦ True` is well-formed and its extension is the set of
-- all particulars.
theorem universal_set_existence : ∃ (S: Set U), ∀ (x: U.Particular), x ∈ₛₑₜ S := by
  have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ Uₛₑₜ := universal_set_contains_all_elements
  have h₂: ∃ (S: Set U), ∀ (x: U.Particular), x ∈ₛₑₜ S := by exists_intro h₁, Uₛₑₜ
  iterate h₂

end Sets

end Universe
