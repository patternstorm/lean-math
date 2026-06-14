import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Inclusion.Predicate
import Universals.Sets.Properties.SetExtensionality
import Universals.Sets.Predicates.Binary.Definitions.PowersetGraphPredicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Right-determinacy of the powerset graph
--
-- If two sets `P₁` and `P₂` both have the subset-membership-characterizing
-- property "their members are exactly the subsets of `S`", they are set-equal.
-- The proof routes through set extensionality: both `P₁` and `P₂` agree
-- pointwise on membership (each member is a subset of `S`), so they are equal.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem powerset_graph_right_determinacy {U: Universal}: ∀ (S: Set U), ∀ (P₁: Set (𝐒𝐞𝐭 U)), ∀ (P₂: Set (𝐒𝐞𝐭 U)),
      powerset_graph_pred S P₁ ∧ powerset_graph_pred S P₂ → P₁ =ₛₑₜ P₂ := by forall_intro
  variable(S: Set U)
  variable(P₁: Set (𝐒𝐞𝐭 U))
  variable(P₂: Set (𝐒𝐞𝐭 U))
  assume(h₁: powerset_graph_pred S P₁ ∧ powerset_graph_pred S P₂)
  have h₂: ∀ (S': Set U), S' ∈ₛₑₜ P₁ ↔ S' ⊆ₛₑₜ S := by and_elim h₁
  have h₃: ∀ (S': Set U), S' ∈ₛₑₜ P₂ ↔ S' ⊆ₛₑₜ S := by and_elim h₁
  -- Derive pointwise membership equivalence between P₁ and P₂ via the shared
  -- subset characterization.
  have h₄: ∀ (S': Set U), S' ∈ₛₑₜ P₁ ↔ S' ∈ₛₑₜ P₂ := by forall_intro
    variable(S': Set U)
    have h₄₁: S' ∈ₛₑₜ P₁ ↔ S' ⊆ₛₑₜ S := by forall_elim h₂, S'
    have h₄₂: S' ∈ₛₑₜ P₂ ↔ S' ⊆ₛₑₜ S := by forall_elim h₃, S'
    have h₄₃: S' ∈ₛₑₜ P₁ → S' ∈ₛₑₜ P₂ := by
      assume(h₄₃₁: S' ∈ₛₑₜ P₁)
      have h₄₃₂: S' ⊆ₛₑₜ S := PC₀.deductive_eq_l2r h₄₁ h₄₃₁
      have h₄₃₃: S' ∈ₛₑₜ P₂ := PC₀.deductive_eq_r2l h₄₂ h₄₃₂
      iterate h₄₃₃
    have h₄₄: S' ∈ₛₑₜ P₂ → S' ∈ₛₑₜ P₁ := by
      assume(h₄₄₁: S' ∈ₛₑₜ P₂)
      have h₄₄₂: S' ⊆ₛₑₜ S := PC₀.deductive_eq_l2r h₄₂ h₄₄₁
      have h₄₄₃: S' ∈ₛₑₜ P₁ := PC₀.deductive_eq_r2l h₄₁ h₄₄₂
      iterate h₄₄₃
    have h₄₅: S' ∈ₛₑₜ P₁ ↔ S' ∈ₛₑₜ P₂ := by iff_intro h₄₃, h₄₄
    iterate h₄₅
  -- Apply set extensionality to conclude P₁ =ₛₑₜ P₂.
  have h₅: ∀ (P: Set (𝐒𝐞𝐭 U)), P₁ =ₛₑₜ P ↔ (∀ (S': Set U), S' ∈ₛₑₜ P₁ ↔ S' ∈ₛₑₜ P) := by forall_elim set_extensionality, P₁
  have h₆: P₁ =ₛₑₜ P₂ ↔ (∀ (S': Set U), S' ∈ₛₑₜ P₁ ↔ S' ∈ₛₑₜ P₂) := by forall_elim h₅, P₂
  have h₇: P₁ =ₛₑₜ P₂ := PC₀.deductive_eq_r2l h₆ h₄
  iterate h₇


end Sets

end Universe
