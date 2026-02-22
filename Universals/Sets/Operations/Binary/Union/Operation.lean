import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND

-- # Union Operation
-- The union of sets A and B contains exactly the elements in A or in B.
axiom union: Set U → Set U → Set U
infixl:65 " ∪ₛₑₜ " => union

axiom union_def: ∀ (A: Set U), ∀ (B: Set U), ∀ (x: U.Particular),
  (A ∪ₛₑₜ B).pred x ↔ A.pred x ∨ B.pred x

-- For fixed A, union_with maps B to A ∪ B, congruent in B.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
noncomputable def union_with (A: Set U): CongruentUnaryOperation (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) :=
  let op: Set U → Set U := (B: Set U ↦ A ∪ₛₑₜ B)
  let cong: ∀ (B₁: Set U), ∀ (B₂: Set U), B₁ =ₛₑₜ B₂ → (A ∪ₛₑₜ B₁ =ₛₑₜ A ∪ₛₑₜ B₂) := by forall_intro
    variable(B₁: Set U)
    variable(B₂: Set U)

    -- eq_def for the output sets
    have h₁: ∀ (S₂: Set U), (A ∪ₛₑₜ B₁) =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), (A ∪ₛₑₜ B₁).pred x ↔ S₂.pred x) := by forall_elim eq_def, (A ∪ₛₑₜ B₁)
    have h₂: (A ∪ₛₑₜ B₁) =ₛₑₜ (A ∪ₛₑₜ B₂) ↔ (∀ (x: U.Particular), (A ∪ₛₑₜ B₁).pred x ↔ (A ∪ₛₑₜ B₂).pred x) := by forall_elim h₁, (A ∪ₛₑₜ B₂)

    -- eq_def for B₁ =ₛₑₜ B₂
    have h₃: ∀ (S₂: Set U), B₁ =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), B₁.pred x ↔ S₂.pred x) := by forall_elim eq_def, B₁
    have h₄: B₁ =ₛₑₜ B₂ ↔ (∀ (x: U.Particular), B₁.pred x ↔ B₂.pred x) := by forall_elim h₃, B₂

    -- union_def instantiations
    have h₅: ∀ (B: Set U), ∀ (x: U.Particular), (A ∪ₛₑₜ B).pred x ↔ A.pred x ∨ B.pred x := by forall_elim union_def, A
    have h₆: ∀ (x: U.Particular), (A ∪ₛₑₜ B₁).pred x ↔ A.pred x ∨ B₁.pred x := by forall_elim h₅, B₁
    have h₇: ∀ (x: U.Particular), (A ∪ₛₑₜ B₂).pred x ↔ A.pred x ∨ B₂.pred x := by forall_elim h₅, B₂

    assume(h₈: B₁ =ₛₑₜ B₂)
    have h₉: ∀ (x: U.Particular), B₁.pred x ↔ B₂.pred x := PC₀.deductive_eq_l2r h₄ h₈

    -- Prove ∀ x, (A ∪ₛₑₜ B₁).pred x ↔ (A ∪ₛₑₜ B₂).pred x
    have h₁₀: ∀ (x: U.Particular), (A ∪ₛₑₜ B₁).pred x ↔ (A ∪ₛₑₜ B₂).pred x := by forall_intro
      variable(x: U.Particular)

      have h₁₀₁: (A ∪ₛₑₜ B₁).pred x ↔ A.pred x ∨ B₁.pred x := by forall_elim h₆, x
      have h₁₀₂: (A ∪ₛₑₜ B₂).pred x ↔ A.pred x ∨ B₂.pred x := by forall_elim h₇, x
      have h₁₀₃: B₁.pred x ↔ B₂.pred x := by forall_elim h₉, x

      -- Forward: (A ∪ₛₑₜ B₁).pred x → (A ∪ₛₑₜ B₂).pred x
      have h₁₀₄: (A ∪ₛₑₜ B₁).pred x → (A ∪ₛₑₜ B₂).pred x := by
        assume(h₁₀₄₁: (A ∪ₛₑₜ B₁).pred x)
        have h₁₀₄₂: A.pred x ∨ B₁.pred x := PC₀.deductive_eq_l2r h₁₀₁ h₁₀₄₁
        have h₁₀₄₃: A.pred x → A.pred x ∨ B₂.pred x := by
          assume(h₁₀₄₃₁: A.pred x)
          have h₁₀₄₃₂: A.pred x ∨ B₂.pred x := by or_intro h₁₀₄₃₁
          iterate h₁₀₄₃₂
        have h₁₀₄₄: B₁.pred x → A.pred x ∨ B₂.pred x := by
          assume(h₁₀₄₄₁: B₁.pred x)
          have h₁₀₄₄₂: B₂.pred x := PC₀.deductive_eq_l2r h₁₀₃ h₁₀₄₄₁
          have h₁₀₄₄₃: A.pred x ∨ B₂.pred x := by or_intro h₁₀₄₄₂
          iterate h₁₀₄₄₃
        have h₁₀₄₅: A.pred x ∨ B₂.pred x := by or_elimination h₁₀₄₂, h₁₀₄₃, h₁₀₄₄
        have h₁₀₄₆: (A ∪ₛₑₜ B₂).pred x := PC₀.deductive_eq_r2l h₁₀₂ h₁₀₄₅
        iterate h₁₀₄₆

      -- Backward: (A ∪ₛₑₜ B₂).pred x → (A ∪ₛₑₜ B₁).pred x
      have h₁₀₅: (A ∪ₛₑₜ B₂).pred x → (A ∪ₛₑₜ B₁).pred x := by
        assume(h₁₀₅₁: (A ∪ₛₑₜ B₂).pred x)
        have h₁₀₅₂: A.pred x ∨ B₂.pred x := PC₀.deductive_eq_l2r h₁₀₂ h₁₀₅₁
        have h₁₀₅₃: A.pred x → A.pred x ∨ B₁.pred x := by
          assume(h₁₀₅₃₁: A.pred x)
          have h₁₀₅₃₂: A.pred x ∨ B₁.pred x := by or_intro h₁₀₅₃₁
          iterate h₁₀₅₃₂
        have h₁₀₅₄: B₂.pred x → A.pred x ∨ B₁.pred x := by
          assume(h₁₀₅₄₁: B₂.pred x)
          have h₁₀₅₄₂: B₁.pred x := PC₀.deductive_eq_r2l h₁₀₃ h₁₀₅₄₁
          have h₁₀₅₄₃: A.pred x ∨ B₁.pred x := by or_intro h₁₀₅₄₂
          iterate h₁₀₅₄₃
        have h₁₀₅₅: A.pred x ∨ B₁.pred x := by or_elimination h₁₀₅₂, h₁₀₅₃, h₁₀₅₄
        have h₁₀₅₆: (A ∪ₛₑₜ B₁).pred x := PC₀.deductive_eq_r2l h₁₀₁ h₁₀₅₅
        iterate h₁₀₅₆

      have h₁₀₆: (A ∪ₛₑₜ B₁).pred x ↔ (A ∪ₛₑₜ B₂).pred x := by iff_intro h₁₀₄, h₁₀₅
      iterate h₁₀₆

    have h₁₁: (A ∪ₛₑₜ B₁) =ₛₑₜ (A ∪ₛₑₜ B₂) := PC₀.deductive_eq_r2l h₂ h₁₀
    iterate h₁₁
  { op := op, cong := cong }

-- Full binary operation, congruent in both arguments.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
noncomputable def union_operation: CongruentBinaryOperation (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) :=
  let op: Set U → CongruentUnaryOperation (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) := (A: Set U ↦ union_with A)
  let cong: ∀ (A₁: Set U), ∀ (A₂: Set U), ∀ (B: Set U), A₁ =ₛₑₜ A₂ → ((A₁ ∪ₛₑₜ B) =ₛₑₜ (A₂ ∪ₛₑₜ B)) := by forall_intro
    variable(A₁: Set U)
    variable(A₂: Set U)
    variable(B: Set U)

    -- eq_def for the output sets
    have h₁: ∀ (S₂: Set U), (A₁ ∪ₛₑₜ B) =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), (A₁ ∪ₛₑₜ B).pred x ↔ S₂.pred x) := by forall_elim eq_def, (A₁ ∪ₛₑₜ B)
    have h₂: (A₁ ∪ₛₑₜ B) =ₛₑₜ (A₂ ∪ₛₑₜ B) ↔ (∀ (x: U.Particular), (A₁ ∪ₛₑₜ B).pred x ↔ (A₂ ∪ₛₑₜ B).pred x) := by forall_elim h₁, (A₂ ∪ₛₑₜ B)

    -- eq_def for A₁ =ₛₑₜ A₂
    have h₃: ∀ (S₂: Set U), A₁ =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), A₁.pred x ↔ S₂.pred x) := by forall_elim eq_def, A₁
    have h₄: A₁ =ₛₑₜ A₂ ↔ (∀ (x: U.Particular), A₁.pred x ↔ A₂.pred x) := by forall_elim h₃, A₂

    -- union_def instantiations
    have h₅₁: ∀ (B': Set U), ∀ (x: U.Particular), (A₁ ∪ₛₑₜ B').pred x ↔ A₁.pred x ∨ B'.pred x := by forall_elim union_def, A₁
    have h₅₂: ∀ (x: U.Particular), (A₁ ∪ₛₑₜ B).pred x ↔ A₁.pred x ∨ B.pred x := by forall_elim h₅₁, B
    have h₅₃: ∀ (B': Set U), ∀ (x: U.Particular), (A₂ ∪ₛₑₜ B').pred x ↔ A₂.pred x ∨ B'.pred x := by forall_elim union_def, A₂
    have h₅₄: ∀ (x: U.Particular), (A₂ ∪ₛₑₜ B).pred x ↔ A₂.pred x ∨ B.pred x := by forall_elim h₅₃, B

    assume(h₆: A₁ =ₛₑₜ A₂)
    have h₇: ∀ (x: U.Particular), A₁.pred x ↔ A₂.pred x := PC₀.deductive_eq_l2r h₄ h₆

    -- Prove ∀ x, (A₁ ∪ₛₑₜ B).pred x ↔ (A₂ ∪ₛₑₜ B).pred x
    have h₈: ∀ (x: U.Particular), (A₁ ∪ₛₑₜ B).pred x ↔ (A₂ ∪ₛₑₜ B).pred x := by forall_intro
      variable(x: U.Particular)

      have h₈₁: (A₁ ∪ₛₑₜ B).pred x ↔ A₁.pred x ∨ B.pred x := by forall_elim h₅₂, x
      have h₈₂: (A₂ ∪ₛₑₜ B).pred x ↔ A₂.pred x ∨ B.pred x := by forall_elim h₅₄, x
      have h₈₃: A₁.pred x ↔ A₂.pred x := by forall_elim h₇, x

      -- Forward: (A₁ ∪ₛₑₜ B).pred x → (A₂ ∪ₛₑₜ B).pred x
      have h₈₄: (A₁ ∪ₛₑₜ B).pred x → (A₂ ∪ₛₑₜ B).pred x := by
        assume(h₈₄₁: (A₁ ∪ₛₑₜ B).pred x)
        have h₈₄₂: A₁.pred x ∨ B.pred x := PC₀.deductive_eq_l2r h₈₁ h₈₄₁
        have h₈₄₃: A₁.pred x → A₂.pred x ∨ B.pred x := by
          assume(h₈₄₃₁: A₁.pred x)
          have h₈₄₃₂: A₂.pred x := PC₀.deductive_eq_l2r h₈₃ h₈₄₃₁
          have h₈₄₃₃: A₂.pred x ∨ B.pred x := by or_intro h₈₄₃₂
          iterate h₈₄₃₃
        have h₈₄₄: B.pred x → A₂.pred x ∨ B.pred x := by
          assume(h₈₄₄₁: B.pred x)
          have h₈₄₄₂: A₂.pred x ∨ B.pred x := by or_intro h₈₄₄₁
          iterate h₈₄₄₂
        have h₈₄₅: A₂.pred x ∨ B.pred x := by or_elimination h₈₄₂, h₈₄₃, h₈₄₄
        have h₈₄₆: (A₂ ∪ₛₑₜ B).pred x := PC₀.deductive_eq_r2l h₈₂ h₈₄₅
        iterate h₈₄₆

      -- Backward: (A₂ ∪ₛₑₜ B).pred x → (A₁ ∪ₛₑₜ B).pred x
      have h₈₅: (A₂ ∪ₛₑₜ B).pred x → (A₁ ∪ₛₑₜ B).pred x := by
        assume(h₈₅₁: (A₂ ∪ₛₑₜ B).pred x)
        have h₈₅₂: A₂.pred x ∨ B.pred x := PC₀.deductive_eq_l2r h₈₂ h₈₅₁
        have h₈₅₃: A₂.pred x → A₁.pred x ∨ B.pred x := by
          assume(h₈₅₃₁: A₂.pred x)
          have h₈₅₃₂: A₁.pred x := PC₀.deductive_eq_r2l h₈₃ h₈₅₃₁
          have h₈₅₃₃: A₁.pred x ∨ B.pred x := by or_intro h₈₅₃₂
          iterate h₈₅₃₃
        have h₈₅₄: B.pred x → A₁.pred x ∨ B.pred x := by
          assume(h₈₅₄₁: B.pred x)
          have h₈₅₄₂: A₁.pred x ∨ B.pred x := by or_intro h₈₅₄₁
          iterate h₈₅₄₂
        have h₈₅₅: A₁.pred x ∨ B.pred x := by or_elimination h₈₅₂, h₈₅₃, h₈₅₄
        have h₈₅₆: (A₁ ∪ₛₑₜ B).pred x := PC₀.deductive_eq_r2l h₈₁ h₈₅₅
        iterate h₈₅₆

      have h₈₆: (A₁ ∪ₛₑₜ B).pred x ↔ (A₂ ∪ₛₑₜ B).pred x := by iff_intro h₈₄, h₈₅
      iterate h₈₆

    have h₉: (A₁ ∪ₛₑₜ B) =ₛₑₜ (A₂ ∪ₛₑₜ B) := PC₀.deductive_eq_r2l h₂ h₈
    iterate h₉
  { op := op, cong := cong }
end Sets

end Universe
