import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Operations.Constants.EmptySet.Constant

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- The `Empty Set` contains no `Particulars`.
theorem empty_set_contains_no_elements {U: Universal}: ∀ (x: U.Particular), x ∉ₛₑₜ ∅ₛₑₜ := by forall_intro
    variable (u: U.Particular)
    have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ ∅ₛₑₜ ↔ (∅ₛₑₜ).pred x := by forall_elim mem_def, ∅ₛₑₜ
    have h₂: u ∈ₛₑₜ ∅ₛₑₜ ↔ (∅ₛₑₜ).pred u := by forall_elim h₁, u
    have h₃: (u ∈ₛₑₜ ∅ₛₑₜ) → False := by
      assume (h₃₁: u ∈ₛₑₜ ∅ₛₑₜ)
      have h₃₂: (∅ₛₑₜ).pred u := PC₀.deductive_eq_l2r h₂ h₃₁
      iterate h₃₂
    have h₄: ¬(u ∈ₛₑₜ ∅ₛₑₜ) := by reductio_ad_absurdum h₃
    have h₅: (u ∉ₛₑₜ ∅ₛₑₜ) ↔ ¬(u ∈ₛₑₜ ∅ₛₑₜ) := not_mem_iff_neg_mem
    have h₆: u ∉ₛₑₜ ∅ₛₑₜ := PC₀.deductive_eq_r2l h₅ h₄
    iterate h₆

end Sets

end Universe
