import Logic
import Universe
import Logic.NaturalDeduction.Rules
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Singleton.Predicate
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Definitions.SingletonElemGraphPredicate
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND


-- # Left-totality of the singleton-element graph
--
-- Every singleton set has at least one member: `particular_satisfies_refinement`
-- gives `is_singleton S.val` (the refinement predicate of `𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U`),
-- which (via `is_singleton.def`) is `∃!₍U₎ x, x ∈ₛₑₜ S`. Dropping the
-- uniqueness conjunct via `unique_existence_implies_existence` yields the
-- witness.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem singleton_elem_graph_left_totality {U: Universal}: ∀ (S: SingletonSet U), ∃ (y: U.Particular), singleton_elem_graph_pred S y := by forall_intro
  variable(A: SingletonSet U)
  have h₁: is_singleton (U:=U) A := by forall_elim particular_satisfies_refinement, A
  have h₂: is_singleton (U:=U) A ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := by forall_elim is_singleton.def, (A : Set U)
  have h₃: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := PC₀.deductive_eq_l2r h₂ h₁
  have h₄: ∃ (y: U.Particular), singleton_elem_graph_pred A y := unique_existence_implies_existence h₃
  iterate h₄


end Sets

end Universe
