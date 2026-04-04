import Universe
import Logic
import Universals.Relations.Universal

/-!
# Quasi-Reflexive Relations

An endo-relation is quasi-reflexive if every particular that participates in
a related pair is related to itself.

```
is_quasi_reflexive R ↔ ∀ a b : U.Particular, R.pred (a ⋈ b) → R.pred (a ⋈ a) ∧ R.pred (b ⋈ b)
```

Only meaningful for endo-relations (Rel U U).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Dyads

axiom is_quasi_reflexive: Rel U U → Prop
axiom is_quasi_reflexive_def: ∀ (R: Rel U U), is_quasi_reflexive R ↔
  ∀ (a: U.Particular), ∀ (b: U.Particular), R.pred (a ⋈ b) → R.pred (a ⋈ a) ∧ R.pred (b ⋈ b)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
def quasi_reflexive_predicate (U: Universal): CongruentUnaryPredicate (𝐑𝐞𝐥 U U) :=
  let pred: Rel U U → Prop := (R: Rel U U ↦ is_quasi_reflexive R)
  let cong: ∀ (R₁: Rel U U), ∀ (R₂: Rel U U), R₁ =ᵣₑₗ R₂ → (pred R₁ ↔ pred R₂) := by forall_intro
    variable(R₁: Rel U U)
    variable(R₂: Rel U U)
    assume(h₁: R₁ =ᵣₑₗ R₂)

    -- Unfold is_quasi_reflexive for both relations
    have h₂: is_quasi_reflexive R₁ ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), R₁.pred (a ⋈ b) → R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := by forall_elim is_quasi_reflexive_def, R₁
    have h₃: is_quasi_reflexive R₂ ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), R₂.pred (a ⋈ b) → R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := by forall_elim is_quasi_reflexive_def, R₂

    -- R₁ =ₛₑₜ R₂ gives pointwise predicate equivalence
    have h₄: ∀ (S₂: Set (U ⧓ U)), R₁ =ₛₑₜ S₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ S₂.pred d) := by forall_elim eq_def, R₁
    have h₅: R₁ =ₛₑₜ R₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d) := by forall_elim h₄, R₂
    have h₆: ∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d := PC₀.deductive_eq_l2r h₅ h₁

    -- Forward: is_quasi_reflexive R₁ → is_quasi_reflexive R₂
    have h₇: is_quasi_reflexive R₁ → is_quasi_reflexive R₂ := by
      assume(h₇₁: is_quasi_reflexive R₁)
      have h₇₂: ∀ (a: U.Particular), ∀ (b: U.Particular), R₁.pred (a ⋈ b) → R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := PC₀.deductive_eq_l2r h₂ h₇₁
      have h₇₃: ∀ (a: U.Particular), ∀ (b: U.Particular), R₂.pred (a ⋈ b) → R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := by forall_intro
        variable(a: U.Particular)
        variable(b: U.Particular)
        have h₇₃₁: R₁.pred (a ⋈ b) ↔ R₂.pred (a ⋈ b) := by forall_elim h₆, (a ⋈ b)
        have h₇₃₂: R₁.pred (a ⋈ a) ↔ R₂.pred (a ⋈ a) := by forall_elim h₆, (a ⋈ a)
        have h₇₃₃: R₁.pred (b ⋈ b) ↔ R₂.pred (b ⋈ b) := by forall_elim h₆, (b ⋈ b)
        -- Instantiate quasi-reflexive for R₁
        have h₇₃₄: ∀ (b': U.Particular), R₁.pred (a ⋈ b') → R₁.pred (a ⋈ a) ∧ R₁.pred (b' ⋈ b') := by forall_elim h₇₂, a
        have h₇₃₅: R₁.pred (a ⋈ b) → R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := by forall_elim h₇₃₄, b
        -- Chain: R₂ → R₁ → R₁ → R₂
        have h₇₃₆: R₂.pred (a ⋈ b) → R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := by
          assume(h₇₃₆₁: R₂.pred (a ⋈ b))
          have h₇₃₆₂: R₁.pred (a ⋈ b) := PC₀.deductive_eq_r2l h₇₃₁ h₇₃₆₁
          have h₇₃₆₃: R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := by modus_ponens h₇₃₅, h₇₃₆₂
          have h₇₃₆₄: R₁.pred (a ⋈ a) := by and_elim h₇₃₆₃
          have h₇₃₆₅: R₁.pred (b ⋈ b) := by and_elim h₇₃₆₃
          have h₇₃₆₆: R₂.pred (a ⋈ a) := PC₀.deductive_eq_l2r h₇₃₂ h₇₃₆₄
          have h₇₃₆₇: R₂.pred (b ⋈ b) := PC₀.deductive_eq_l2r h₇₃₃ h₇₃₆₅
          have h₇₃₆₈: R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := by and_intro h₇₃₆₆, h₇₃₆₇
          iterate h₇₃₆₈
        iterate h₇₃₆
      have h₇₄: is_quasi_reflexive R₂ := PC₀.deductive_eq_r2l h₃ h₇₃
      iterate h₇₄

    -- Backward: is_quasi_reflexive R₂ → is_quasi_reflexive R₁
    have h₈: is_quasi_reflexive R₂ → is_quasi_reflexive R₁ := by
      assume(h₈₁: is_quasi_reflexive R₂)
      have h₈₂: ∀ (a: U.Particular), ∀ (b: U.Particular), R₂.pred (a ⋈ b) → R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := PC₀.deductive_eq_l2r h₃ h₈₁
      have h₈₃: ∀ (a: U.Particular), ∀ (b: U.Particular), R₁.pred (a ⋈ b) → R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := by forall_intro
        variable(a: U.Particular)
        variable(b: U.Particular)
        have h₈₃₁: R₁.pred (a ⋈ b) ↔ R₂.pred (a ⋈ b) := by forall_elim h₆, (a ⋈ b)
        have h₈₃₂: R₁.pred (a ⋈ a) ↔ R₂.pred (a ⋈ a) := by forall_elim h₆, (a ⋈ a)
        have h₈₃₃: R₁.pred (b ⋈ b) ↔ R₂.pred (b ⋈ b) := by forall_elim h₆, (b ⋈ b)
        have h₈₃₄: ∀ (b': U.Particular), R₂.pred (a ⋈ b') → R₂.pred (a ⋈ a) ∧ R₂.pred (b' ⋈ b') := by forall_elim h₈₂, a
        have h₈₃₅: R₂.pred (a ⋈ b) → R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := by forall_elim h₈₃₄, b
        have h₈₃₆: R₁.pred (a ⋈ b) → R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := by
          assume(h₈₃₆₁: R₁.pred (a ⋈ b))
          have h₈₃₆₂: R₂.pred (a ⋈ b) := PC₀.deductive_eq_l2r h₈₃₁ h₈₃₆₁
          have h₈₃₆₃: R₂.pred (a ⋈ a) ∧ R₂.pred (b ⋈ b) := by modus_ponens h₈₃₅, h₈₃₆₂
          have h₈₃₆₄: R₂.pred (a ⋈ a) := by and_elim h₈₃₆₃
          have h₈₃₆₅: R₂.pred (b ⋈ b) := by and_elim h₈₃₆₃
          have h₈₃₆₆: R₁.pred (a ⋈ a) := PC₀.deductive_eq_r2l h₈₃₂ h₈₃₆₄
          have h₈₃₆₇: R₁.pred (b ⋈ b) := PC₀.deductive_eq_r2l h₈₃₃ h₈₃₆₅
          have h₈₃₆₈: R₁.pred (a ⋈ a) ∧ R₁.pred (b ⋈ b) := by and_intro h₈₃₆₆, h₈₃₆₇
          iterate h₈₃₆₈
        iterate h₈₃₆
      have h₈₄: is_quasi_reflexive R₁ := PC₀.deductive_eq_r2l h₂ h₈₃
      iterate h₈₄

    have h₉: is_quasi_reflexive R₁ ↔ is_quasi_reflexive R₂ := by iff_intro h₇, h₈
    iterate h₉
  { pred := pred, cong := cong }

end Relations

end Universe
