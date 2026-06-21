import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Definitions.EmptySetGraphPredicate
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Properties.NonMembershipIsNegatedMembership
import Universals.Sets.Properties.SetExtensionality

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Right-determinacy of the empty set graph
--
-- If two sets both contain no elements, they are set-equal by extensionality:
-- for every `x`, neither set contains `x`, so they agree pointwise on membership.
--
-- Proof by Kimi K2.7 (claude-opus-4-7), 2026-06-20
theorem empty_set_graph_right_determinacy {U: Universal}: ∀ (X: Set U), ∀ (Y: Set U), empty_set_graph_pred X ∧ empty_set_graph_pred Y → X =ₛₑₜ Y := by forall_intro
  variable(E₁: Set U)
  variable(E₂: Set U)
  assume(h₁: empty_set_graph_pred E₁ ∧ empty_set_graph_pred E₂)
  have h₂: empty_set_graph_pred E₁ := by and_elim h₁
  have h₃: empty_set_graph_pred E₂ := by and_elim h₁
  -- Pointwise membership equivalence: every x is in neither set.
  have h₄: ∀ (x: U.Particular), x ∈ₛₑₜ E₁ ↔ x ∈ₛₑₜ E₂ := by forall_intro
    variable(x: U.Particular)
    have h₄₁: x ∉ₛₑₜ E₁ := by forall_elim h₂, x
    have h₄₂: x ∉ₛₑₜ E₂ := by forall_elim h₃, x
    have h₄₃: x ∉ₛₑₜ E₁ ↔ ¬(x ∈ₛₑₜ E₁) := not_mem_is_neg_mem
    have h₄₄: x ∉ₛₑₜ E₂ ↔ ¬(x ∈ₛₑₜ E₂) := not_mem_is_neg_mem
    have h₄₅: ¬(x ∈ₛₑₜ E₁) := PC₀.deductive_eq_l2r h₄₃ h₄₁
    have h₄₆: ¬(x ∈ₛₑₜ E₂) := PC₀.deductive_eq_l2r h₄₄ h₄₂
    have h₄₇: x ∈ₛₑₜ E₁ → x ∈ₛₑₜ E₂ := by
      assume(h₄₇₁: x ∈ₛₑₜ E₁)
      have h₄₇₂: x ∈ₛₑₜ E₂ := by contradiction h₄₇₁, h₄₅
      iterate h₄₇₂
    have h₄₈: x ∈ₛₑₜ E₂ → x ∈ₛₑₜ E₁ := by
      assume(h₄₈₁: x ∈ₛₑₜ E₂)
      have h₄₈₂: x ∈ₛₑₜ E₁ := by contradiction h₄₈₁, h₄₆
      iterate h₄₈₂
    have h₄₉: x ∈ₛₑₜ E₁ ↔ x ∈ₛₑₜ E₂ := by iff_intro h₄₇, h₄₈
    iterate h₄₉
  -- Apply set extensionality.
  have h₅: E₁ =ₛₑₜ E₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ E₁ ↔ x ∈ₛₑₜ E₂) := by forall_elim set_extensionality, E₁, E₂
  have h₆: E₁ =ₛₑₜ E₂ := PC₀.deductive_eq_r2l h₅ h₄
  iterate h₆


end Sets

end Universe
