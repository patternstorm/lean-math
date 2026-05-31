import Logic
import Universe
import Universals.Sets.Predicates.Binary.Membership.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- ## Predicate equivalence is equivalent to membership equivalence
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem pred_eq_iff_mem_eq {A B: Set U} {u: U.Particular}: (A.pred u ↔ B.pred u) ↔ (u ∈ₛₑₜ A ↔ u ∈ₛₑₜ B) := by
  have h₁: mem u A ↔ A.pred u := by forall_elim mem.def, u, A
  have h₂: mem u B ↔ B.pred u := by forall_elim mem.def, u, B
  have h₃: (A.pred u ↔ B.pred u) → (u ∈ₛₑₜ A ↔ u ∈ₛₑₜ B) := by
    assume (h₃₁: A.pred u ↔ B.pred u)
    have h₃₂: u ∈ₛₑₜ A → u ∈ₛₑₜ B := by
      assume (h₃₂₁: u ∈ₛₑₜ A)
      have h₃₂₂: A.pred u := PC₀.deductive_eq_l2r h₁ h₃₂₁
      have h₃₂₃: B.pred u := PC₀.deductive_eq_l2r h₃₁ h₃₂₂
      have h₃₂₄: u ∈ₛₑₜ B := PC₀.deductive_eq_r2l h₂ h₃₂₃
      iterate h₃₂₄
    have h₃₃: u ∈ₛₑₜ B → u ∈ₛₑₜ A := by
      assume (h₃₃₁: u ∈ₛₑₜ B)
      have h₃₃₂: B.pred u := PC₀.deductive_eq_l2r h₂ h₃₃₁
      have h₃₃₃: A.pred u := PC₀.deductive_eq_r2l h₃₁ h₃₃₂
      have h₃₃₄: u ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₁ h₃₃₃
      iterate h₃₃₄
    iff_intro h₃₂, h₃₃
  have h₄: (u ∈ₛₑₜ A ↔ u ∈ₛₑₜ B) → (A.pred u ↔ B.pred u) := by
    assume (h₄₁: u ∈ₛₑₜ A ↔ u ∈ₛₑₜ B)
    have h₄₂: A.pred u → B.pred u := by
      assume (h₄₂₁: A.pred u)
      have h₄₂₂: u ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₁ h₄₂₁
      have h₄₂₃: u ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₄₁ h₄₂₂
      have h₄₂₄: B.pred u := PC₀.deductive_eq_l2r h₂ h₄₂₃
      iterate h₄₂₄
    have h₄₃: B.pred u → A.pred u := by
      assume (h₄₃₁: B.pred u)
      have h₄₃₂: u ∈ₛₑₜ B := PC₀.deductive_eq_r2l h₂ h₄₃₁
      have h₄₃₃: u ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₄₁ h₄₃₂
      have h₄₃₄: A.pred u := PC₀.deductive_eq_l2r h₁ h₄₃₃
      iterate h₄₃₄
    iff_intro h₄₂, h₄₃
  iff_intro h₃, h₄

end Sets

end Universe
