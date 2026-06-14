import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Inclusion.Predicate
import Universals.Sets.Definitions.SetComprehension.Definition
import Universals.Sets.Predicates.Binary.Definitions.PowersetGraphPredicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Left-totality of the powerset graph
--
-- For every set `S`, there exists a set `P` whose members are exactly the
-- subsets of `S`. Witness: the set comprehension `{ S' : Set U | S' ⊆ₛₑₜ S }`,
-- which expresses exactly the "P is the set of subsets of S" property by
-- construction. The universal property then follows by `mem.def` at the witness.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem powerset_graph_left_totality {U: Universal}: ∀ (S: Set U), ∃ (P: Set (𝐒𝐞𝐭 U)), powerset_graph_pred S P := by forall_intro
  variable(S: Set U)
  let P : Set (𝐒𝐞𝐭 U) := { S' : Set U | S' ⊆ₛₑₜ S } with (subsets_of S).cong
  have h₁: ∀ (S': Set U), S' ∈ₛₑₜ P ↔ S' ⊆ₛₑₜ S := by forall_intro
    variable(S': Set U)
    have h₁₁: S' ∈ₛₑₜ P ↔ S' ⊆ₛₑₜ S := by forall_elim mem.def, S', P
    iterate h₁₁
  have h₂: ∃ (P: Set (𝐒𝐞𝐭 U)), powerset_graph_pred S P := by exists_intro h₁, P
  iterate h₂


end Sets

end Universe
