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


-- # Right-determinacy of the singleton-element graph
--
-- A singleton set has exactly one member: any two members must be equal in
-- `U`. `particular_satisfies_refinement` gives `is_singleton S.val`, which
-- (via `is_singleton.def`) is `∃!₍U₎ x, x ∈ₛₑₜ S`. Collapsing two witnesses
-- via `unique_existence_implies_uniqueness` yields the result.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem singleton_elem_graph_right_determinacy {U: Universal}: ∀ (S: SingletonSet U), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), singleton_elem_graph_pred S y₁ ∧ singleton_elem_graph_pred S y₂ → y₁ =₍U₎ y₂ := by forall_intro
  variable(A: SingletonSet U)
  have h₁: is_singleton (U:=U) A := by forall_elim particular_satisfies_refinement, A
  have h₂: is_singleton (U:=U) A ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := by forall_elim is_singleton.def, (A : Set U)
  have h₃: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := PC₀.deductive_eq_l2r h₂ h₁
  have h₄: ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), singleton_elem_graph_pred A y₁ ∧ singleton_elem_graph_pred A y₂ → y₁ =₍U₎ y₂ := unique_existence_implies_uniqueness h₃
  iterate h₄


end Sets

end Universe
