import Universe
import Logic
import Universals.Relations.Universal

/-!
# Relation Symmetry

An endo-relation is symmetric if whenever a is related to b, then b
is related to a.

```
is_symmetric R ↔ ∀ a b : U.Particular, R.pred (a ⋈ b) → R.pred (b ⋈ a)
```

Only meaningful for endo-relations (Rel U U).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Dyads

axiom is_symmetric: Rel U U → Prop
axiom is_symmetric_def: ∀ (R: Rel U U), is_symmetric R ↔
  ∀ (a: U.Particular), ∀ (b: U.Particular), R.pred (a ⋈ b) → R.pred (b ⋈ a)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
def symmetric_predicate (U: Universal): CongruentUnaryPredicate (𝐑𝐞𝐥 U U) :=
  let pred: Rel U U → Prop := (R: Rel U U ↦ is_symmetric R)
  let cong: ∀ (R₁: Rel U U), ∀ (R₂: Rel U U), R₁ =ᵣₑₗ R₂ → (pred R₁ ↔ pred R₂) := by forall_intro
    variable(R₁: Rel U U)
    variable(R₂: Rel U U)
    assume(h₁: R₁ =ᵣₑₗ R₂)

    -- Unfold is_symmetric for both relations
    have h₂: is_symmetric R₁ ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), R₁.pred (a ⋈ b) → R₁.pred (b ⋈ a) := by forall_elim is_symmetric_def, R₁
    have h₃: is_symmetric R₂ ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), R₂.pred (a ⋈ b) → R₂.pred (b ⋈ a) := by forall_elim is_symmetric_def, R₂

    -- R₁ =ₛₑₜ R₂ gives pointwise predicate equivalence
    have h₄: ∀ (S₂: Set (U ⧓ U)), R₁ =ₛₑₜ S₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ S₂.pred d) := by forall_elim eq_def, R₁
    have h₅: R₁ =ₛₑₜ R₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d) := by forall_elim h₄, R₂
    have h₆: ∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d := PC₀.deductive_eq_l2r h₅ h₁

    -- Forward: is_symmetric R₁ → is_symmetric R₂
    have h₇: is_symmetric R₁ → is_symmetric R₂ := by
      assume(h₇₁: is_symmetric R₁)
      have h₇₂: ∀ (a: U.Particular), ∀ (b: U.Particular), R₁.pred (a ⋈ b) → R₁.pred (b ⋈ a) := PC₀.deductive_eq_l2r h₂ h₇₁
      have h₇₃: ∀ (a: U.Particular), ∀ (b: U.Particular), R₂.pred (a ⋈ b) → R₂.pred (b ⋈ a) := by forall_intro
        variable(a: U.Particular)
        variable(b: U.Particular)
        -- Predicate equivalences for (a ⋈ b) and (b ⋈ a)
        have h₇₃₁: R₁.pred (a ⋈ b) ↔ R₂.pred (a ⋈ b) := by forall_elim h₆, (a ⋈ b)
        have h₇₃₂: R₁.pred (b ⋈ a) ↔ R₂.pred (b ⋈ a) := by forall_elim h₆, (b ⋈ a)
        -- Symmetry in R₁
        have h₇₃₃: ∀ (b': U.Particular), R₁.pred (a ⋈ b') → R₁.pred (b' ⋈ a) := by forall_elim h₇₂, a
        have h₇₃₄: R₁.pred (a ⋈ b) → R₁.pred (b ⋈ a) := by forall_elim h₇₃₃, b
        -- Chain: R₂ → R₁ → R₁ → R₂
        have h₇₃₅: R₂.pred (a ⋈ b) → R₂.pred (b ⋈ a) := by
          assume(h₇₃₅₁: R₂.pred (a ⋈ b))
          have h₇₃₅₂: R₁.pred (a ⋈ b) := PC₀.deductive_eq_r2l h₇₃₁ h₇₃₅₁
          have h₇₃₅₃: R₁.pred (b ⋈ a) := by modus_ponens h₇₃₄, h₇₃₅₂
          have h₇₃₅₄: R₂.pred (b ⋈ a) := PC₀.deductive_eq_l2r h₇₃₂ h₇₃₅₃
          iterate h₇₃₅₄
        iterate h₇₃₅
      have h₇₄: is_symmetric R₂ := PC₀.deductive_eq_r2l h₃ h₇₃
      iterate h₇₄

    -- Backward: is_symmetric R₂ → is_symmetric R₁
    have h₈: is_symmetric R₂ → is_symmetric R₁ := by
      assume(h₈₁: is_symmetric R₂)
      have h₈₂: ∀ (a: U.Particular), ∀ (b: U.Particular), R₂.pred (a ⋈ b) → R₂.pred (b ⋈ a) := PC₀.deductive_eq_l2r h₃ h₈₁
      have h₈₃: ∀ (a: U.Particular), ∀ (b: U.Particular), R₁.pred (a ⋈ b) → R₁.pred (b ⋈ a) := by forall_intro
        variable(a: U.Particular)
        variable(b: U.Particular)
        have h₈₃₁: R₁.pred (a ⋈ b) ↔ R₂.pred (a ⋈ b) := by forall_elim h₆, (a ⋈ b)
        have h₈₃₂: R₁.pred (b ⋈ a) ↔ R₂.pred (b ⋈ a) := by forall_elim h₆, (b ⋈ a)
        have h₈₃₃: ∀ (b': U.Particular), R₂.pred (a ⋈ b') → R₂.pred (b' ⋈ a) := by forall_elim h₈₂, a
        have h₈₃₄: R₂.pred (a ⋈ b) → R₂.pred (b ⋈ a) := by forall_elim h₈₃₃, b
        have h₈₃₅: R₁.pred (a ⋈ b) → R₁.pred (b ⋈ a) := by
          assume(h₈₃₅₁: R₁.pred (a ⋈ b))
          have h₈₃₅₂: R₂.pred (a ⋈ b) := PC₀.deductive_eq_l2r h₈₃₁ h₈₃₅₁
          have h₈₃₅₃: R₂.pred (b ⋈ a) := by modus_ponens h₈₃₄, h₈₃₅₂
          have h₈₃₅₄: R₁.pred (b ⋈ a) := PC₀.deductive_eq_r2l h₈₃₂ h₈₃₅₃
          iterate h₈₃₅₄
        iterate h₈₃₅
      have h₈₄: is_symmetric R₁ := PC₀.deductive_eq_r2l h₂ h₈₃
      iterate h₈₄

    have h₉: is_symmetric R₁ ↔ is_symmetric R₂ := by iff_intro h₇, h₈
    iterate h₉
  { pred := pred, cong := cong }

end Relations

end Universe
