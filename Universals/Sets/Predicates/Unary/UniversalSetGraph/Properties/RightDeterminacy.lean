import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Definitions.UniversalSetGraphPredicate
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Properties.SetExtensionality

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Right-determinacy of the universal set graph
--
-- If two sets both contain all elements, they are set-equal by extensionality:
-- for every `x`, both sets contain `x`, so they agree pointwise on membership.
--
-- Proof by Kimi K2.7, 2026-06-21
theorem universal_set_graph_right_determinacy {U: Universal}: ∀ (X: Set U), ∀ (Y: Set U), universal_set_graph_pred X ∧ universal_set_graph_pred Y → X =ₛₑₜ Y := by forall_intro
  variable(X: Set U)
  variable(Y: Set U)
  assume(h₁: universal_set_graph_pred X ∧ universal_set_graph_pred Y)
  have h₂: universal_set_graph_pred X := by and_elim h₁
  have h₃: universal_set_graph_pred Y := by and_elim h₁
  -- Pointwise membership equivalence: every x is in both sets.
  have h₄: ∀ (x: U.Particular), x ∈ₛₑₜ X ↔ x ∈ₛₑₜ Y := by forall_intro
    variable(x: U.Particular)
    have h₄₁: x ∈ₛₑₜ X := by forall_elim h₂, x
    have h₄₂: x ∈ₛₑₜ Y := by forall_elim h₃, x
    have h₄₃: x ∈ₛₑₜ X → x ∈ₛₑₜ Y := by
      assume(h: x ∈ₛₑₜ X)
      iterate h₄₂
    have h₄₄: x ∈ₛₑₜ Y → x ∈ₛₑₜ X := by
      assume(h: x ∈ₛₑₜ Y)
      iterate h₄₁
    have h₄₅: x ∈ₛₑₜ X ↔ x ∈ₛₑₜ Y := by iff_intro h₄₃, h₄₄
    iterate h₄₅
  -- Apply set extensionality.
  have h₅: X =ₛₑₜ Y ↔ (∀ (x: U.Particular), x ∈ₛₑₜ X ↔ x ∈ₛₑₜ Y) := by forall_elim set_extensionality, X, Y
  have h₆: X =ₛₑₜ Y := PC₀.deductive_eq_r2l h₅ h₄
  iterate h₆


end Sets

end Universe
