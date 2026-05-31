import Universe
import Logic
import Universals.Relations.Universal

/-!
# Relation Reflexivity

An endo-relation is reflexive if every element is related to itself.

```
is_reflexive.pred R ↔ ∀ a : U.Particular, R a a
```

Only meaningful for endo-relations (Rel U U).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁

-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-30
def is_reflexive: CongruentUnaryPredicate (𝐑𝐞𝐥 U U) :=
  let pred: Rel U U → Prop := (R: Rel U U ↦ ∀ (a: U.Particular), R a a)
  let cong: ∀ (R₁: Rel U U), ∀ (R₂: Rel U U), R₁ =ᵣₑₗ R₂ → (pred R₁ ↔ pred R₂) := by forall_intro
    variable(R₁: Rel U U)
    variable(R₂: Rel U U)
    assume(h₁: R₁ =ᵣₑₗ R₂)

    -- Unfold relation equality to pointwise iff on the binary predicate
    have h₂: ∀ (R₂': Rel U U), R₁ =ᵣₑₗ R₂' ↔ ∀ (x: U.Particular), ∀ (y: U.Particular), (R₁.pred x).pred y ↔ (R₂'.pred x).pred y := by forall_elim eq_def, R₁
    have h₃: R₁ =ᵣₑₗ R₂ ↔ ∀ (x: U.Particular), ∀ (y: U.Particular), (R₁.pred x).pred y ↔ (R₂.pred x).pred y := by forall_elim h₂, R₂
    have h₄: ∀ (x: U.Particular), ∀ (y: U.Particular), (R₁.pred x).pred y ↔ (R₂.pred x).pred y := PC₀.deductive_eq_l2r h₃ h₁

    -- Forward: pred R₁ → pred R₂
    have h₅: pred R₁ → pred R₂ := by
      assume(h₅₁: pred R₁)
      have h₅₂: ∀ (a: U.Particular), R₂ a a := by forall_intro
        variable(a: U.Particular)
        have h₅₂₁: R₁ a a := by forall_elim h₅₁, a
        have h₅₂₂: ∀ (y: U.Particular), (R₁.pred a).pred y ↔ (R₂.pred a).pred y := by forall_elim h₄, a
        have h₅₂₃: (R₁.pred a).pred a ↔ (R₂.pred a).pred a := by forall_elim h₅₂₂, a
        have h₅₂₄: R₂ a a := PC₀.deductive_eq_l2r h₅₂₃ h₅₂₁
        iterate h₅₂₄
      iterate h₅₂

    -- Backward: pred R₂ → pred R₁
    have h₆: pred R₂ → pred R₁ := by
      assume(h₆₁: pred R₂)
      have h₆₂: ∀ (a: U.Particular), R₁ a a := by forall_intro
        variable(a: U.Particular)
        have h₆₂₁: R₂ a a := by forall_elim h₆₁, a
        have h₆₂₂: ∀ (y: U.Particular), (R₁.pred a).pred y ↔ (R₂.pred a).pred y := by forall_elim h₄, a
        have h₆₂₃: (R₁.pred a).pred a ↔ (R₂.pred a).pred a := by forall_elim h₆₂₂, a
        have h₆₂₄: R₁ a a := PC₀.deductive_eq_r2l h₆₂₃ h₆₂₁
        iterate h₆₂₄
      iterate h₆₂

    have h₇: pred R₁ ↔ pred R₂ := by iff_intro h₅, h₆
    iterate h₇
  { pred := pred, cong := cong }

end Relations

end Universe
