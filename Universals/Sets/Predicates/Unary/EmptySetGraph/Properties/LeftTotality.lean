import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Definitions.EmptySetGraphPredicate
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Properties.NonMembershipIsNegatedMembership
import Universals.Sets.Definitions.SetComprehension.Definition

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Left-totality of the empty set graph
--
-- There exists a set whose members are exactly none of them. Witness:
-- the set comprehension `{ x: U.Particular | False }`, which expresses the
-- "contains no elements" property by construction.
--
-- Proof by Kimi K2.7, 2026-06-20
theorem empty_set_graph_left_totality {U: Universal}: ∃ (E: Set U), empty_set_graph_pred E := by
  let E: Set U := { x: U.Particular | False }
  have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ E ↔ False := by forall_intro
    variable(x: U.Particular)
    have h₁₁: x ∈ₛₑₜ E ↔ False := by forall_elim mem.def, x, E
    iterate h₁₁
  have h₂: ∀ (x: U.Particular), x ∉ₛₑₜ E := by forall_intro
    variable(x: U.Particular)
    have h₂₁: x ∈ₛₑₜ E ↔ False := by forall_elim h₁, x
    have h₂₂: x ∉ₛₑₜ E ↔ ¬(x ∈ₛₑₜ E) := not_mem_is_neg_mem
    have h₂₃: ¬(x ∈ₛₑₜ E) := by
      assume(h₂₃₁: x ∈ₛₑₜ E)
      have h₂₃₂: False := PC₀.deductive_eq_l2r h₂₁ h₂₃₁
      iterate h₂₃₂
    have h₂₄: x ∉ₛₑₜ E := PC₀.deductive_eq_r2l h₂₂ h₂₃
    iterate h₂₄
  have h₃: ∃ (E: Set U), empty_set_graph_pred E := by exists_intro h₂, E
  iterate h₃


end Sets

end Universe
