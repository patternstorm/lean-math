import Universe
import Logic
import Universals.Relations.Universal
import Universals.Relations.Predicates.Unary.Symmetric.Predicate
import Universals.Relations.Predicates.Unary.Transitive.Predicate

/-!
# Partial Equivalence Relations

An endo-relation is a partial equivalence relation if it is symmetric and
transitive. Unlike a full equivalence relation, a partial equivalence relation
need not be reflexive on the whole universal — but it is quasi-reflexive,
meaning every participating particular is related to itself.

```
is_partial_equivalence_relation R ↔ is_symmetric R ∧ is_transitive R
```

Only meaningful for endo-relations (Rel U U).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Dyads

axiom is_partial_equivalence_relation: Rel U U → Prop
axiom is_partial_equivalence_relation_def: ∀ (R: Rel U U), is_partial_equivalence_relation R ↔
  is_symmetric R ∧ is_transitive R

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
def partial_equivalence_relation_predicate (U: Universal): CongruentUnaryPredicate (𝐑𝐞𝐥 U U) :=
  let sym_trans: CongruentUnaryPredicate (𝐑𝐞𝐥 U U) := conjunction_preserves_congruence (symmetric_predicate U) (transitive_predicate U)
  let pred: Rel U U → Prop := (R: Rel U U ↦ is_partial_equivalence_relation R)
  let cong: ∀ (R₁: Rel U U), ∀ (R₂: Rel U U), R₁ =ᵣₑₗ R₂ → (is_partial_equivalence_relation R₁ ↔ is_partial_equivalence_relation R₂) := by forall_intro
    variable(R₁: Rel U U)
    variable(R₂: Rel U U)
    assume(h₁: R₁ =ᵣₑₗ R₂)

    -- Unfold partial equivalence relation for both
    have h₂: is_partial_equivalence_relation R₁ ↔ is_symmetric R₁ ∧ is_transitive R₁ := by forall_elim is_partial_equivalence_relation_def, R₁
    have h₃: is_partial_equivalence_relation R₂ ↔ is_symmetric R₂ ∧ is_transitive R₂ := by forall_elim is_partial_equivalence_relation_def, R₂

    -- Conjunction congruence
    have h₄: ∀ (R: Rel U U), R₁ =ᵣₑₗ R → (sym_trans.pred R₁ ↔ sym_trans.pred R) := by forall_elim sym_trans.cong, R₁
    have h₅: R₁ =ᵣₑₗ R₂ → (sym_trans.pred R₁ ↔ sym_trans.pred R₂) := by forall_elim h₄, R₂
    have h₆: sym_trans.pred R₁ ↔ sym_trans.pred R₂ := by modus_ponens h₅, h₁

    -- Chain: is_per R₁ ↔ conjunction R₁ ↔ conjunction R₂ ↔ is_per R₂
    have h₇: is_partial_equivalence_relation R₁ → is_partial_equivalence_relation R₂ := by
      assume(h₇₁: is_partial_equivalence_relation R₁)
      have h₇₂: is_symmetric R₁ ∧ is_transitive R₁ := PC₀.deductive_eq_l2r h₂ h₇₁
      have h₇₃: is_symmetric R₂ ∧ is_transitive R₂ := PC₀.deductive_eq_l2r h₆ h₇₂
      have h₇₄: is_partial_equivalence_relation R₂ := PC₀.deductive_eq_r2l h₃ h₇₃
      iterate h₇₄

    have h₈: is_partial_equivalence_relation R₂ → is_partial_equivalence_relation R₁ := by
      assume(h₈₁: is_partial_equivalence_relation R₂)
      have h₈₂: is_symmetric R₂ ∧ is_transitive R₂ := PC₀.deductive_eq_l2r h₃ h₈₁
      have h₈₃: is_symmetric R₁ ∧ is_transitive R₁ := PC₀.deductive_eq_r2l h₆ h₈₂
      have h₈₄: is_partial_equivalence_relation R₁ := PC₀.deductive_eq_r2l h₂ h₈₃
      iterate h₈₄

    have h₉: is_partial_equivalence_relation R₁ ↔ is_partial_equivalence_relation R₂ := by iff_intro h₇, h₈
    iterate h₉
  { pred := pred, cong := cong }

end Relations

end Universe
