import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Operations.Constants.UniversalSet.Constant

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem universal_set_contains_all_elements {U: Universal}: ∀ (x: U.Particular), x ∈ₛₑₜ Uₛₑₜ := by forall_intro
    variable (u: U.Particular)
    have h₁: (Uₛₑₜ).pred u := by true_intro
    have h₂: u ∈ₛₑₜ Uₛₑₜ ↔ (Uₛₑₜ).pred u := by forall_elim mem.def, u, Uₛₑₜ
    have h₃: u ∈ₛₑₜ Uₛₑₜ := PC₀.deductive_eq_r2l h₂ h₁
    iterate h₃
end Sets

end Universe
