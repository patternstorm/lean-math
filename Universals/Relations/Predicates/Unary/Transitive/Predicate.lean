import Universe
import Logic
import Universals.Relations.Universal

/-!
# Relation Transitivity

An endo-relation is transitive if whenever a is related to b and b is
related to c, then a is related to c.

```
is_transitive R ↔ ∀ a b c : U.Particular,
  R.pred (a ⋈ b) ∧ R.pred (b ⋈ c) → R.pred (a ⋈ c)
```

Only meaningful for endo-relations (Rel U U).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Dyads

axiom is_transitive: Rel U U → Prop
axiom is_transitive_def: ∀ (R: Rel U U), is_transitive R ↔
  ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular),
    R.pred (a ⋈ b) ∧ R.pred (b ⋈ c) → R.pred (a ⋈ c)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
def transitive_predicate (U: Universal): CongruentUnaryPredicate (𝐑𝐞𝐥 U U) :=
  let pred: Rel U U → Prop := (R: Rel U U ↦ is_transitive R)
  let cong: ∀ (R₁: Rel U U), ∀ (R₂: Rel U U), R₁ =ᵣₑₗ R₂ → (pred R₁ ↔ pred R₂) := by forall_intro
    variable(R₁: Rel U U)
    variable(R₂: Rel U U)
    assume(h₁: R₁ =ᵣₑₗ R₂)

    -- Unfold is_transitive for both relations
    have h₂: is_transitive R₁ ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c) → R₁.pred (a ⋈ c) := by forall_elim is_transitive_def, R₁
    have h₃: is_transitive R₂ ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c) → R₂.pred (a ⋈ c) := by forall_elim is_transitive_def, R₂

    -- R₁ =ᵣₑₗ R₂ gives pointwise predicate equivalence
    have h₄: ∀ (S₂: Set (U ⧓ U)), R₁ =ₛₑₜ S₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ S₂.pred d) := by forall_elim eq_def, R₁
    have h₅: R₁ =ₛₑₜ R₂ ↔ (∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d) := by forall_elim h₄, R₂
    have h₆: ∀ (d: U ⋈ U), R₁.pred d ↔ R₂.pred d := PC₀.deductive_eq_l2r h₅ h₁

    -- Forward: is_transitive R₁ → is_transitive R₂
    have h₇: is_transitive R₁ → is_transitive R₂ := by
      assume(h₇₁: is_transitive R₁)
      have h₇₂: ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c) → R₁.pred (a ⋈ c) := PC₀.deductive_eq_l2r h₂ h₇₁
      have h₇₃: ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c) → R₂.pred (a ⋈ c) := by forall_intro
        variable(a: U.Particular)
        variable(b: U.Particular)
        variable(c: U.Particular)
        -- Predicate equivalences
        have h₇₃₁: R₁.pred (a ⋈ b) ↔ R₂.pred (a ⋈ b) := by forall_elim h₆, (a ⋈ b)
        have h₇₃₂: R₁.pred (b ⋈ c) ↔ R₂.pred (b ⋈ c) := by forall_elim h₆, (b ⋈ c)
        have h₇₃₃: R₁.pred (a ⋈ c) ↔ R₂.pred (a ⋈ c) := by forall_elim h₆, (a ⋈ c)
        -- Transitivity in R₁
        have h₇₃₄: ∀ (b': U.Particular), ∀ (c': U.Particular), R₁.pred (a ⋈ b') ∧ R₁.pred (b' ⋈ c') → R₁.pred (a ⋈ c') := by forall_elim h₇₂, a
        have h₇₃₅: ∀ (c': U.Particular), R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c') → R₁.pred (a ⋈ c') := by forall_elim h₇₃₄, b
        have h₇₃₆: R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c) → R₁.pred (a ⋈ c) := by forall_elim h₇₃₅, c
        -- Chain: R₂ → R₁ → R₁ → R₂
        have h₇₃₇: R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c) → R₂.pred (a ⋈ c) := by
          assume(h₇₃₇₁: R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c))
          have h₇₃₇₂: R₂.pred (a ⋈ b) := by and_elim h₇₃₇₁
          have h₇₃₇₃: R₂.pred (b ⋈ c) := by and_elim h₇₃₇₁
          have h₇₃₇₄: R₁.pred (a ⋈ b) := PC₀.deductive_eq_r2l h₇₃₁ h₇₃₇₂
          have h₇₃₇₅: R₁.pred (b ⋈ c) := PC₀.deductive_eq_r2l h₇₃₂ h₇₃₇₃
          have h₇₃₇₆: R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c) := by and_intro h₇₃₇₄, h₇₃₇₅
          have h₇₃₇₇: R₁.pred (a ⋈ c) := by modus_ponens h₇₃₆, h₇₃₇₆
          have h₇₃₇₈: R₂.pred (a ⋈ c) := PC₀.deductive_eq_l2r h₇₃₃ h₇₃₇₇
          iterate h₇₃₇₈
        iterate h₇₃₇
      have h₇₄: is_transitive R₂ := PC₀.deductive_eq_r2l h₃ h₇₃
      iterate h₇₄

    -- Backward: is_transitive R₂ → is_transitive R₁
    have h₈: is_transitive R₂ → is_transitive R₁ := by
      assume(h₈₁: is_transitive R₂)
      have h₈₂: ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c) → R₂.pred (a ⋈ c) := PC₀.deductive_eq_l2r h₃ h₈₁
      have h₈₃: ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c) → R₁.pred (a ⋈ c) := by forall_intro
        variable(a: U.Particular)
        variable(b: U.Particular)
        variable(c: U.Particular)
        have h₈₃₁: R₁.pred (a ⋈ b) ↔ R₂.pred (a ⋈ b) := by forall_elim h₆, (a ⋈ b)
        have h₈₃₂: R₁.pred (b ⋈ c) ↔ R₂.pred (b ⋈ c) := by forall_elim h₆, (b ⋈ c)
        have h₈₃₃: R₁.pred (a ⋈ c) ↔ R₂.pred (a ⋈ c) := by forall_elim h₆, (a ⋈ c)
        have h₈₃₄: ∀ (b': U.Particular), ∀ (c': U.Particular), R₂.pred (a ⋈ b') ∧ R₂.pred (b' ⋈ c') → R₂.pred (a ⋈ c') := by forall_elim h₈₂, a
        have h₈₃₅: ∀ (c': U.Particular), R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c') → R₂.pred (a ⋈ c') := by forall_elim h₈₃₄, b
        have h₈₃₆: R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c) → R₂.pred (a ⋈ c) := by forall_elim h₈₃₅, c
        have h₈₃₇: R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c) → R₁.pred (a ⋈ c) := by
          assume(h₈₃₇₁: R₁.pred (a ⋈ b) ∧ R₁.pred (b ⋈ c))
          have h₈₃₇₂: R₁.pred (a ⋈ b) := by and_elim h₈₃₇₁
          have h₈₃₇₃: R₁.pred (b ⋈ c) := by and_elim h₈₃₇₁
          have h₈₃₇₄: R₂.pred (a ⋈ b) := PC₀.deductive_eq_l2r h₈₃₁ h₈₃₇₂
          have h₈₃₇₅: R₂.pred (b ⋈ c) := PC₀.deductive_eq_l2r h₈₃₂ h₈₃₇₃
          have h₈₃₇₆: R₂.pred (a ⋈ b) ∧ R₂.pred (b ⋈ c) := by and_intro h₈₃₇₄, h₈₃₇₅
          have h₈₃₇₇: R₂.pred (a ⋈ c) := by modus_ponens h₈₃₆, h₈₃₇₆
          have h₈₃₇₈: R₁.pred (a ⋈ c) := PC₀.deductive_eq_r2l h₈₃₃ h₈₃₇₇
          iterate h₈₃₇₈
        iterate h₈₃₇
      have h₈₄: is_transitive R₁ := PC₀.deductive_eq_r2l h₂ h₈₃
      iterate h₈₄

    have h₉: is_transitive R₁ ↔ is_transitive R₂ := by iff_intro h₇, h₈
    iterate h₉
  { pred := pred, cong := cong }

end Relations

end Universe
