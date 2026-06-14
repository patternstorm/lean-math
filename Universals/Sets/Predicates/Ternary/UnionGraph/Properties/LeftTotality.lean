import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Definitions.SetComprehension.Definition
import Universals.Sets.Predicates.Ternary.Definitions.UnionGraphPredicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Left-totality of the union graph
--
-- For every pair of sets `A` and `B`, there exists a set `C` whose members are
-- exactly those in `A` or in `B`. Witness: the set comprehension
-- `{ x : U.Particular | x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B }`, which expresses the union's
-- defining property by construction. The universal property then follows by
-- `mem.def` at the witness.
--
-- Congruence of the comprehension body is auto-derived via the typeclass
-- machinery: `congruent_disjunction` over `mem A` and `mem B` (each a
-- `CongruentUnary` predicate via `FiberSecondPreservesCongruence`).
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem union_graph_left_totality {U: Universal}: ∀ (A: Set U), ∀ (B: Set U), ∃ (C: Set U), union_graph_pred A B C := by forall_intro
  variable(A: Set U)
  variable(B: Set U)
  let C : Set U := { x : U.Particular | x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B }
  have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ C ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by forall_intro
    variable(x: U.Particular)
    have h₁₁: x ∈ₛₑₜ C ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by forall_elim mem.def, x, C
    iterate h₁₁
  have h₂: ∃ (C: Set U), union_graph_pred A B C := by exists_intro h₁, C
  iterate h₂


end Sets

end Universe
