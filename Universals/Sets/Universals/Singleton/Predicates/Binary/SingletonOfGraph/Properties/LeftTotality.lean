import Logic
import Universe
import Logic.NaturalDeduction.Rules
import Universals.Sets.Universal
import Universals.Sets.Definitions.SetComprehension.Definition
import Universals.Sets.Predicates.Unary.Singleton.Predicate
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Universals.Singleton.Predicates.Binary.Definitions.SingletonOfGraphPredicate
import Universals.Sets.Universals.Singleton.Universal
import Universals.Sets.Universals.Singleton.Particular

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND


-- # Left-totality of the singleton-of graph
--
-- For every `x : U.Particular` there is a singleton set whose only element is
-- `x`. The witness is the set comprehension `{ y : U.Particular | y =₍U₎ x }`;
-- its membership predicate is exactly equality to `x`, so `x` is the unique
-- member.
--
-- Proof by Kimi K2.7, 2026-06-26
theorem singleton_of_graph_left_totality {U: Universal}: ∀ (x: U.Particular), ∃ (S: SingletonSet U), singleton_of_graph_pred x S := by forall_intro
  variable(x: U.Particular)
  let X: Set U := { y: U.Particular | y =₍U₎ x }
  -- Membership in X is exactly equality to x.
  have h₁: ∀ (y: U.Particular), y ∈ₛₑₜ X ↔ y =₍U₎ x := by forall_intro
    variable(y: U.Particular)
    have h₁₁: y ∈ₛₑₜ X ↔ y =₍U₎ x := by forall_elim mem.def, y, X
    iterate h₁₁
  -- x belongs to X by reflexivity.
  have h₂: x ∈ₛₑₜ X := by
    have h₂₁: x ∈ₛₑₜ X ↔ x =₍U₎ x := by forall_elim h₁, x
    have h₂₂: x =₍U₎ x := by forall_elim U.eq.refl, x
    have h₂₃: x ∈ₛₑₜ X := PC₀.deductive_eq_r2l h₂₁ h₂₂
    iterate h₂₃
  -- Every member of X equals x.
  have h₃: ∀ (y: U.Particular), y ∈ₛₑₜ X → y =₍U₎ x := by forall_intro
    variable(y: U.Particular)
    assume(h₄: y ∈ₛₑₜ X)
    have h₅: y ∈ₛₑₜ X ↔ y =₍U₎ x := by forall_elim h₁, y
    have h₆: y =₍U₎ x := PC₀.deductive_eq_l2r h₅ h₄
    iterate h₆
  -- Package existence + uniqueness for the unique-existence quantifier.
  have h₄: ∃!₍U₎ (y: U.Particular), y ∈ₛₑₜ X := unique_existence_intro x h₂ h₃
  -- Convert to the opaque `is_singleton` predicate.
  have h₅: is_singleton X ↔ ∃!₍U₎ (y: U.Particular), y ∈ₛₑₜ X := by forall_elim is_singleton.def, X
  have h₆: is_singleton X := PC₀.deductive_eq_r2l h₅ h₄
  -- Convert X to SingletonSet
  let X: SingletonSet U := as_singleton X h₆
  have h₇: ∃ (S: SingletonSet U), singleton_of_graph_pred x S := by exists_intro h₁, X
  iterate h₇


end Sets

end Universe
