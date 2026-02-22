import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Operations.Binary.Union.Operation

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND

-- Well-definedness: union respects membership
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
theorem union_mem: ∀ (A: Set U), ∀ (B: Set U), ∀ (x: U.Particular),
  x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by forall_intro
  variable(A: Set U)
  variable(B: Set U)
  variable(x: U.Particular)

  -- mem_def for each set
  have h₁: ∀ (y: U.Particular), y ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (A ∪ₛₑₜ B).pred y := by forall_elim mem_def, (A ∪ₛₑₜ B)
  have h₂: x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (A ∪ₛₑₜ B).pred x := by forall_elim h₁, x
  have h₃: ∀ (y: U.Particular), y ∈ₛₑₜ A ↔ A.pred y := by forall_elim mem_def, A
  have h₄: x ∈ₛₑₜ A ↔ A.pred x := by forall_elim h₃, x
  have h₅: ∀ (y: U.Particular), y ∈ₛₑₜ B ↔ B.pred y := by forall_elim mem_def, B
  have h₆: x ∈ₛₑₜ B ↔ B.pred x := by forall_elim h₅, x

  -- union_def
  have h₇: ∀ (B': Set U), ∀ (y: U.Particular), (A ∪ₛₑₜ B').pred y ↔ A.pred y ∨ B'.pred y := by forall_elim union_def, A
  have h₈: ∀ (y: U.Particular), (A ∪ₛₑₜ B).pred y ↔ A.pred y ∨ B.pred y := by forall_elim h₇, B
  have h₉: (A ∪ₛₑₜ B).pred x ↔ A.pred x ∨ B.pred x := by forall_elim h₈, x

  -- Forward: x ∈ₛₑₜ (A ∪ₛₑₜ B) → x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B
  have h₁₀: x ∈ₛₑₜ (A ∪ₛₑₜ B) → x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by
    assume(h₁₀₁: x ∈ₛₑₜ (A ∪ₛₑₜ B))
    have h₁₀₂: (A ∪ₛₑₜ B).pred x := PC₀.deductive_eq_l2r h₂ h₁₀₁
    have h₁₀₃: A.pred x ∨ B.pred x := PC₀.deductive_eq_l2r h₉ h₁₀₂
    have h₁₀₄: A.pred x → x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by
      assume(h₁₀₄₁: A.pred x)
      have h₁₀₄₂: x ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₄ h₁₀₄₁
      have h₁₀₄₃: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by or_intro h₁₀₄₂
      iterate h₁₀₄₃
    have h₁₀₅: B.pred x → x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by
      assume(h₁₀₅₁: B.pred x)
      have h₁₀₅₂: x ∈ₛₑₜ B := PC₀.deductive_eq_r2l h₆ h₁₀₅₁
      have h₁₀₅₃: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by or_intro h₁₀₅₂
      iterate h₁₀₅₃
    have h₁₀₆: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by or_elimination h₁₀₃, h₁₀₄, h₁₀₅
    iterate h₁₀₆

  -- Backward: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B → x ∈ₛₑₜ (A ∪ₛₑₜ B)
  have h₁₁: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B → x ∈ₛₑₜ (A ∪ₛₑₜ B) := by
    assume(h₁₁₁: x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B)
    have h₁₁₂: x ∈ₛₑₜ A → x ∈ₛₑₜ (A ∪ₛₑₜ B) := by
      assume(h₁₁₂₁: x ∈ₛₑₜ A)
      have h₁₁₂₂: A.pred x := PC₀.deductive_eq_l2r h₄ h₁₁₂₁
      have h₁₁₂₃: A.pred x ∨ B.pred x := by or_intro h₁₁₂₂
      have h₁₁₂₄: (A ∪ₛₑₜ B).pred x := PC₀.deductive_eq_r2l h₉ h₁₁₂₃
      have h₁₁₂₅: x ∈ₛₑₜ (A ∪ₛₑₜ B) := PC₀.deductive_eq_r2l h₂ h₁₁₂₄
      iterate h₁₁₂₅
    have h₁₁₃: x ∈ₛₑₜ B → x ∈ₛₑₜ (A ∪ₛₑₜ B) := by
      assume(h₁₁₃₁: x ∈ₛₑₜ B)
      have h₁₁₃₂: B.pred x := PC₀.deductive_eq_l2r h₆ h₁₁₃₁
      have h₁₁₃₃: A.pred x ∨ B.pred x := by or_intro h₁₁₃₂
      have h₁₁₃₄: (A ∪ₛₑₜ B).pred x := PC₀.deductive_eq_r2l h₉ h₁₁₃₃
      have h₁₁₃₅: x ∈ₛₑₜ (A ∪ₛₑₜ B) := PC₀.deductive_eq_r2l h₂ h₁₁₃₄
      iterate h₁₁₃₅
    have h₁₁₄: x ∈ₛₑₜ (A ∪ₛₑₜ B) := by or_elimination h₁₁₁, h₁₁₂, h₁₁₃
    iterate h₁₁₄

  have h₁₂: x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B := by iff_intro h₁₀, h₁₁
  iterate h₁₂

end Sets

end Universe
