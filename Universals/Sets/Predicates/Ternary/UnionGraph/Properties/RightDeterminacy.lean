import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Properties.SetExtensionality
import Universals.Sets.Predicates.Ternary.Definitions.UnionGraphPredicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Right-determinacy of the union graph
--
-- If two sets `C₁` and `C₂` both have "their members are exactly those in `A`
-- or `B`", they are set-equal. The proof routes through set extensionality:
-- both `C₁` and `C₂` agree pointwise on membership (each member is in `A` or
-- in `B`), so they are equal.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem union_graph_right_determinacy {U: Universal}: ∀ (A: Set U), ∀ (B: Set U), ∀ (C₁: Set U), ∀ (C₂: Set U),
      union_graph_pred A B C₁ ∧ union_graph_pred A B C₂ → C₁ =ₛₑₜ C₂ := by forall_intro
  variable(A: Set U)
  variable(B: Set U)
  variable(C₁: Set U)
  variable(C₂: Set U)
  assume(h₁: union_graph_pred A B C₁ ∧ union_graph_pred A B C₂)
  have h₂: ∀ (x: U.Particular), x ∈ₛₑₜ C₁ ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by and_elim h₁
  have h₃: ∀ (x: U.Particular), x ∈ₛₑₜ C₂ ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by and_elim h₁
  -- Derive pointwise membership equivalence between C₁ and C₂ via the shared
  -- "in A or in B" characterization.
  have h₄: ∀ (x: U.Particular), x ∈ₛₑₜ C₁ ↔ x ∈ₛₑₜ C₂ := by forall_intro
    variable(x: U.Particular)
    have h₄₁: x ∈ₛₑₜ C₁ ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by forall_elim h₂, x
    have h₄₂: x ∈ₛₑₜ C₂ ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by forall_elim h₃, x
    have h₄₃: x ∈ₛₑₜ C₁ → x ∈ₛₑₜ C₂ := by
      assume(h₄₃₁: x ∈ₛₑₜ C₁)
      have h₄₃₂: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₄₁ h₄₃₁
      have h₄₃₃: x ∈ₛₑₜ C₂ := PC₀.deductive_eq_r2l h₄₂ h₄₃₂
      iterate h₄₃₃
    have h₄₄: x ∈ₛₑₜ C₂ → x ∈ₛₑₜ C₁ := by
      assume(h₄₄₁: x ∈ₛₑₜ C₂)
      have h₄₄₂: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₄₂ h₄₄₁
      have h₄₄₃: x ∈ₛₑₜ C₁ := PC₀.deductive_eq_r2l h₄₁ h₄₄₂
      iterate h₄₄₃
    have h₄₅: x ∈ₛₑₜ C₁ ↔ x ∈ₛₑₜ C₂ := by iff_intro h₄₃, h₄₄
    iterate h₄₅
  -- Apply set extensionality to conclude C₁ =ₛₑₜ C₂.
  have h₅: ∀ (C: Set U), C₁ =ₛₑₜ C ↔ (∀ (x: U.Particular), x ∈ₛₑₜ C₁ ↔ x ∈ₛₑₜ C) := by forall_elim set_extensionality, C₁
  have h₆: C₁ =ₛₑₜ C₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ C₁ ↔ x ∈ₛₑₜ C₂) := by forall_elim h₅, C₂
  have h₇: C₁ =ₛₑₜ C₂ := PC₀.deductive_eq_r2l h₆ h₄
  iterate h₇


end Sets

end Universe
