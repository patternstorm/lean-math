import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Operations.Constants.UniversalSet.Constant

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

theorem universal_set_contains_all_elements {U: Universal}: ∀ (x: U.Particular), x ∈ₛₑₜ Uₛₑₜ := by forall_intro
    variable (u: U.Particular)
    have h₁: (Uₛₑₜ).pred u := by true_intro
    have h₂: ∀ (x: U.Particular), x ∈ₛₑₜ Uₛₑₜ ↔ (Uₛₑₜ).pred x := by forall_elim mem_def, Uₛₑₜ
    have h₃: u ∈ₛₑₜ Uₛₑₜ ↔ (Uₛₑₜ).pred u := by forall_elim h₂, u
    have h₄: u ∈ₛₑₜ Uₛₑₜ := PC₀.deductive_eq_r2l h₃ h₁
    iterate h₄
end Sets

end Universe
