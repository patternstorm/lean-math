import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Definitions.UniversalSetGraphPredicate
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Definitions.SetComprehension.Definition

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Left-totality of the universal set graph
--
-- There exists a set that contains every particular. Witness:
-- the set comprehension `{ _: U.Particular | True }`, which expresses the
-- "contains all elements" property by construction.
--
-- Proof by Kimi K2.7, 2026-06-21
theorem universal_set_graph_left_totality {U: Universal}: ∃ (S: Set U), universal_set_graph_pred S := by
  let S: Set U := { _: U.Particular | True }
  have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ S := by forall_intro
    variable(x: U.Particular)
    have h₁₁: x ∈ₛₑₜ S ↔ True := by forall_elim mem.def, x, S
    have h₁₂: True := by true_intro
    have h₁₃: x ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₁₁ h₁₂
    iterate h₁₃
  have h₂: ∃ (S: Set U), universal_set_graph_pred S := by exists_intro h₁, S
  iterate h₂


end Sets

end Universe
