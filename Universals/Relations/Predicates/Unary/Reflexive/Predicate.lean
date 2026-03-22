import Universe
import Logic
import Universals.Relations.Universal

/-!
# Relation Reflexivity

An endo-relation is reflexive if every element is related to itself.

```
is_reflexive R ↔ ∀ a : U.Particular, R.pred (a ⋈ a)
```

Only meaningful for endo-relations (Rel U U).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Dyads

axiom is_reflexive: Rel U U → Prop
axiom is_reflexive_def: ∀ (R: Rel U U), is_reflexive R ↔ ∀ (a: U.Particular), R.pred (a ⋈ a)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
def reflexive_predicate (U: Universal): CongruentUnaryPredicate (𝐑𝐞𝐥 U U) :=
  let pred: Rel U U → Prop := (R: Rel U U ↦ is_reflexive R)
  let cong: ∀ (R₁: Rel U U), ∀ (R₂: Rel U U), R₁ =ᵣₑₗ R₂ → (pred R₁ ↔ pred R₂) := by forall_intro
    variable(R₁: Rel U U)
    variable(R₂: Rel U U)
    assume(h₁: R₁ =ᵣₑₗ R₂)

    -- Unfold is_reflexive for both relations
    have h₂: is_reflexive R₁ ↔ ∀ (a: U.Particular), R₁.pred (a ⋈ a) := by forall_elim is_reflexive_def, R₁
    have h₃: is_reflexive R₂ ↔ ∀ (a: U.Particular), R₂.pred (a ⋈ a) := by forall_elim is_reflexive_def, R₂

    -- R₁ =ₛₑₜ R₂ gives pointwise predicate equivalence
    have h₄: ∀ (S₂: Set (U ⧓ U)), R₁ =ₛₑₜ S₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ S₂.pred d) := by forall_elim eq_def, R₁
    have h₅: R₁ =ₛₑₜ R₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d) := by forall_elim h₄, R₂
    have h₆: ∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d := PC₀.deductive_eq_l2r h₅ h₁

    -- Forward: is_reflexive R₁ → is_reflexive R₂
    have h₇: is_reflexive R₁ → is_reflexive R₂ := by
      assume(h₇₁: is_reflexive R₁)
      have h₇₂: ∀ (a: U.Particular), R₁.pred (a ⋈ a) := PC₀.deductive_eq_l2r h₂ h₇₁
      have h₇₃: ∀ (a: U.Particular), R₂.pred (a ⋈ a) := by forall_intro
        variable(a: U.Particular)
        have h₇₃₁: R₁.pred (a ⋈ a) := by forall_elim h₇₂, a
        have h₇₃₂: R₁.pred (a ⋈ a) ↔ R₂.pred (a ⋈ a) := by forall_elim h₆, (a ⋈ a)
        have h₇₃₃: R₂.pred (a ⋈ a) := PC₀.deductive_eq_l2r h₇₃₂ h₇₃₁
        iterate h₇₃₃
      have h₇₄: is_reflexive R₂ := PC₀.deductive_eq_r2l h₃ h₇₃
      iterate h₇₄

    -- Backward: is_reflexive R₂ → is_reflexive R₁
    have h₈: is_reflexive R₂ → is_reflexive R₁ := by
      assume(h₈₁: is_reflexive R₂)
      have h₈₂: ∀ (a: U.Particular), R₂.pred (a ⋈ a) := PC₀.deductive_eq_l2r h₃ h₈₁
      have h₈₃: ∀ (a: U.Particular), R₁.pred (a ⋈ a) := by forall_intro
        variable(a: U.Particular)
        have h₈₃₁: R₂.pred (a ⋈ a) := by forall_elim h₈₂, a
        have h₈₃₂: R₁.pred (a ⋈ a) ↔ R₂.pred (a ⋈ a) := by forall_elim h₆, (a ⋈ a)
        have h₈₃₃: R₁.pred (a ⋈ a) := PC₀.deductive_eq_r2l h₈₃₂ h₈₃₁
        iterate h₈₃₃
      have h₈₄: is_reflexive R₁ := PC₀.deductive_eq_r2l h₂ h₈₃
      iterate h₈₄

    have h₉: is_reflexive R₁ ↔ is_reflexive R₂ := by iff_intro h₇, h₈
    iterate h₉
  { pred := pred, cong := cong }

end Relations

end Universe
