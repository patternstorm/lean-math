import Logic
import Universe
import Logic.NaturalDeduction.Rules
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Universals.Singleton.Predicates.Binary.Definitions.SingletonOfGraphPredicate
import Universals.Sets.Properties.SetExtensionality
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND


-- # Right-determinacy of the singleton-of graph
--
-- If two singleton sets both characterize the same element `x`, they have the
-- same members and therefore the same underlying set. Refined-universal
-- equality on `SingletonSet U` is exactly equality of the underlying sets.
--
-- Proof by Kimi K2.7, 2026-06-26
theorem singleton_of_graph_right_determinacy {U: Universal}: ∀ (x: U.Particular), ∀ (S₁: SingletonSet U), ∀ (S₂: SingletonSet U), singleton_of_graph_pred x S₁ ∧ singleton_of_graph_pred x S₂ → (S₁: Set U) =ₛₑₜ (S₂: Set U) := by forall_intro
  variable(x: U.Particular)
  variable(S₁: SingletonSet U)
  variable(S₂: SingletonSet U)
  assume(h₁: singleton_of_graph_pred x S₁ ∧ singleton_of_graph_pred x S₂)
  have h₂: singleton_of_graph_pred x S₁ := by and_elim h₁
  have h₃: singleton_of_graph_pred x S₂ := by and_elim h₁
  -- Pointwise membership equivalence in the underlying sets.
  have h₄: ∀ (y: U.Particular), y ∈ₛₑₜ S₁ ↔ y ∈ₛₑₜ S₂ := by forall_intro
    variable(y: U.Particular)
    have h₄₁: y ∈ₛₑₜ S₁ ↔ y =₍U₎ x := by forall_elim h₂, y
    have h₄₂: y ∈ₛₑₜ S₂ ↔ y =₍U₎ x := by forall_elim h₃, y
    -- Forward: y ∈ S₁ → y = x → y ∈ S₂
    have h₄₃: y ∈ₛₑₜ S₁ → y ∈ₛₑₜ S₂ := by
      assume(h₅: y ∈ₛₑₜ S₁)
      have h₆: y =₍U₎ x := PC₀.deductive_eq_l2r h₄₁ h₅
      have h₇: y ∈ₛₑₜ S₂ := PC₀.deductive_eq_r2l h₄₂ h₆
      iterate h₇
    -- Backward: y ∈ S₂ → y = x → y ∈ S₁
    have h₄₄: y ∈ₛₑₜ S₂ → y ∈ₛₑₜ S₁ := by
      assume(h₅: y ∈ₛₑₜ S₂)
      have h₆: y =₍U₎ x := PC₀.deductive_eq_l2r h₄₂ h₅
      have h₇: y ∈ₛₑₜ S₁ := PC₀.deductive_eq_r2l h₄₁ h₆
      iterate h₇
    have h₄₅: y ∈ₛₑₜ S₁ ↔ y ∈ₛₑₜ S₂ := by iff_intro h₄₃, h₄₄
    iterate h₄₅
  -- Apply set extensionality to the underlying sets.
  have h₅: (S₁ : Set U) =ₛₑₜ (S₂ : Set U) ↔ (∀ (y: U.Particular), y ∈ₛₑₜ S₁ ↔ y ∈ₛₑₜ S₂) := by forall_elim set_extensionality, (S₁ : Set U), (S₂ : Set U)
  have h₆: (S₁ : Set U) =ₛₑₜ (S₂ : Set U) := PC₀.deductive_eq_r2l h₅ h₄
  iterate h₆


end Sets

end Universe
