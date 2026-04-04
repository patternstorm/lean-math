import Universals.Relations.Predicates.Unary.PartialEquivalenceRelation.Predicate
import Universals.Relations.Predicates.Unary.QuasiReflexive.Predicate

/-!
# Partial Equivalence Relations are Quasi-Reflexive

If a relation is a partial equivalence relation (symmetric and transitive),
then it is quasi-reflexive: every particular that participates in a related
pair is related to itself.

```
∀ R, is_partial_equivalence_relation R → is_quasi_reflexive R
```

Proof: From R(a, b), by symmetry R(b, a). By transitivity of R(a, b) and
R(b, a) we get R(a, a). By transitivity of R(b, a) and R(a, b) we get R(b, b).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
theorem per_is_quasi_reflexive: ∀ (R: Rel U U),
  is_partial_equivalence_relation R → is_quasi_reflexive R := by forall_intro
  variable(R: Rel U U)
  assume(h₁: is_partial_equivalence_relation R)

  -- Unfold PER: symmetric ∧ transitive
  have h₂: is_partial_equivalence_relation R ↔ is_symmetric R ∧ is_transitive R := by forall_elim is_partial_equivalence_relation_def, R
  have h₃: is_symmetric R ∧ is_transitive R := PC₀.deductive_eq_l2r h₂ h₁
  have h₄: is_symmetric R := by and_elim h₃
  have h₅: is_transitive R := by and_elim h₃

  -- Unfold symmetry
  have h₆: is_symmetric R ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), R.pred (a ⋈ b) → R.pred (b ⋈ a) := by forall_elim is_symmetric_def, R
  have h₇: ∀ (a: U.Particular), ∀ (b: U.Particular), R.pred (a ⋈ b) → R.pred (b ⋈ a) := PC₀.deductive_eq_l2r h₆ h₄

  -- Unfold transitivity
  have h₈: is_transitive R ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R.pred (a ⋈ b) ∧ R.pred (b ⋈ c) → R.pred (a ⋈ c) := by forall_elim is_transitive_def, R
  have h₉: ∀ (a: U.Particular), ∀ (b: U.Particular), ∀ (c: U.Particular), R.pred (a ⋈ b) ∧ R.pred (b ⋈ c) → R.pred (a ⋈ c) := PC₀.deductive_eq_l2r h₈ h₅

  -- Show quasi-reflexivity
  have h₁₀: ∀ (a: U.Particular), ∀ (b: U.Particular), R.pred (a ⋈ b) → R.pred (a ⋈ a) ∧ R.pred (b ⋈ b) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h₁₀₁: R.pred (a ⋈ b))

    -- By symmetry: R(b, a)
    have h₁₀₂: ∀ (b': U.Particular), R.pred (a ⋈ b') → R.pred (b' ⋈ a) := by forall_elim h₇, a
    have h₁₀₃: R.pred (a ⋈ b) → R.pred (b ⋈ a) := by forall_elim h₁₀₂, b
    have h₁₀₄: R.pred (b ⋈ a) := by modus_ponens h₁₀₃, h₁₀₁

    -- By transitivity: R(a, b) ∧ R(b, a) → R(a, a)
    have h₁₀₅: ∀ (b': U.Particular), ∀ (c: U.Particular), R.pred (a ⋈ b') ∧ R.pred (b' ⋈ c) → R.pred (a ⋈ c) := by forall_elim h₉, a
    have h₁₀₆: ∀ (c: U.Particular), R.pred (a ⋈ b) ∧ R.pred (b ⋈ c) → R.pred (a ⋈ c) := by forall_elim h₁₀₅, b
    have h₁₀₇: R.pred (a ⋈ b) ∧ R.pred (b ⋈ a) → R.pred (a ⋈ a) := by forall_elim h₁₀₆, a
    have h₁₀₈: R.pred (a ⋈ b) ∧ R.pred (b ⋈ a) := by and_intro h₁₀₁, h₁₀₄
    have h₁₀₉: R.pred (a ⋈ a) := by modus_ponens h₁₀₇, h₁₀₈

    -- By transitivity: R(b, a) ∧ R(a, b) → R(b, b)
    have h₁₁₀: ∀ (b': U.Particular), ∀ (c: U.Particular), R.pred (b ⋈ b') ∧ R.pred (b' ⋈ c) → R.pred (b ⋈ c) := by forall_elim h₉, b
    have h₁₁₁: ∀ (c: U.Particular), R.pred (b ⋈ a) ∧ R.pred (a ⋈ c) → R.pred (b ⋈ c) := by forall_elim h₁₁₀, a
    have h₁₁₂: R.pred (b ⋈ a) ∧ R.pred (a ⋈ b) → R.pred (b ⋈ b) := by forall_elim h₁₁₁, b
    have h₁₁₃: R.pred (b ⋈ a) ∧ R.pred (a ⋈ b) := by and_intro h₁₀₄, h₁₀₁
    have h₁₁₄: R.pred (b ⋈ b) := by modus_ponens h₁₁₂, h₁₁₃

    -- Combine
    have h₁₁₅: R.pred (a ⋈ a) ∧ R.pred (b ⋈ b) := by and_intro h₁₀₉, h₁₁₄
    iterate h₁₁₅

  -- Fold back to is_quasi_reflexive
  have h₁₁: is_quasi_reflexive R ↔ ∀ (a: U.Particular), ∀ (b: U.Particular), R.pred (a ⋈ b) → R.pred (a ⋈ a) ∧ R.pred (b ⋈ b) := by forall_elim is_quasi_reflexive_def, R
  have h₁₂: is_quasi_reflexive R := PC₀.deductive_eq_r2l h₁₁ h₁₀
  iterate h₁₂

end Relations

end Universe
