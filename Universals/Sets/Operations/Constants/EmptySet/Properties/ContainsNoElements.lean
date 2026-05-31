import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Properties.NonMembershipIsNegatedMembership
import Universals.Sets.Operations.Constants.EmptySet.Constant

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- The `Empty Set` contains no `Particulars`.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem empty_set_contains_no_elements {U: Universal}: ∀ (x: U.Particular), x ∉ₛₑₜ ∅ₛₑₜ := by forall_intro
    variable (u: U.Particular)
    have h₁: u ∈ₛₑₜ ∅ₛₑₜ ↔ (∅ₛₑₜ).pred u := by forall_elim mem.def, u, ∅ₛₑₜ
    have h₂: (u ∈ₛₑₜ ∅ₛₑₜ) → False := by
      assume (h₂₁: u ∈ₛₑₜ ∅ₛₑₜ)
      have h₂₂: (∅ₛₑₜ).pred u := PC₀.deductive_eq_l2r h₁ h₂₁
      iterate h₂₂
    have h₃: ¬(u ∈ₛₑₜ ∅ₛₑₜ) := by reductio_ad_absurdum h₂
    have h₄: (u ∉ₛₑₜ ∅ₛₑₜ) ↔ ¬(u ∈ₛₑₜ ∅ₛₑₜ) := not_mem_is_neg_mem
    have h₅: u ∉ₛₑₜ ∅ₛₑₜ := PC₀.deductive_eq_r2l h₄ h₃
    iterate h₅

end Sets

end Universe
