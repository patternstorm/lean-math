import Universals.Correspondences.Predicates.Ternary.CoClassification.Predicate
import Universals.Relations.Universal

/-!
# Co-Classification Relation

A correspondence `C: U₁ ⭢ᶜ U₂` induces a binary relation on the target
universal U₂: two target particulars are **co-classified** iff they belong
to the same class in the basis — some source particular co-classifies both.

```
(co_classification C).pred (b₁ ⋈ b₂)  ↔  ∃ a : U₁, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ)
```

This relation is always reflexive on the range and always symmetric.
It is not always transitive — transitivity fails when classes overlap
without being identical.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads
open Relations

-- # Constructed relation via relation_from
noncomputable def co_classification_rel (C: U₁ ⭢ᶜ U₂): Rel U₂ U₂ :=
  relation_from (co_classified_by C)

-- # Operation symbol (axiom — signature only)
axiom co_classification: U₁ ⭢ᶜ U₂ → Rel U₂ U₂

-- # Defining axiom using relation equality
axiom co_classification_def: ∀ (C: U₁ ⭢ᶜ U₂), co_classification C =ᵣₑₗ co_classification_rel C

-- # Bridge: derive pointwise definition from relation-equality axiom
-- This recovers the old-style ∀ b₁ b₂, pred (b₁ ⋈ b₂) ↔ ∃ a, ... form.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
theorem co_classification_unfold: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
  (co_classification C).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by forall_intro
  variable(C: U₁ ⭢ᶜ U₂)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)

  -- co_classification_def → pointwise pred equivalence via eq_def
  have hdef: co_classification C =ᵣₑₗ co_classification_rel C := by forall_elim co_classification_def, C
  have h₁: ∀ (R₂: Set (U₂ ⧓ U₂)), co_classification C =ₛₑₜ R₂ ↔ (∀ (d: U₂ ⋈ U₂), (co_classification C).pred d ↔ R₂.pred d) := by forall_elim eq_def, co_classification C
  have h₂: co_classification C =ₛₑₜ co_classification_rel C ↔ (∀ (d: U₂ ⋈ U₂), (co_classification C).pred d ↔ (co_classification_rel C).pred d) := by forall_elim h₁, co_classification_rel C
  have h₃: ∀ (d: U₂ ⋈ U₂), (co_classification C).pred d ↔ (co_classification_rel C).pred d := PC₀.deductive_eq_l2r h₂ hdef
  have h₄: (co_classification C).pred (b₁ ⋈ b₂) ↔ (co_classification_rel C).pred (b₁ ⋈ b₂) := by forall_elim h₃, (b₁ ⋈ b₂)

  -- uncurry_def unfolds the constructed relation to the binary predicate
  let R: U₂.Particular → U₂.Particular → Prop :=
    (x: U₂.Particular, y: U₂.Particular ↦ ((co_classified_by C).pred x).pred y)
  have h₅: ∀ (x: U₂.Particular), ∀ (y: U₂.Particular), (uncurry R) (x ⋈ y) ↔ R x y := uncurry_def R
  have h₆: ∀ (y: U₂.Particular), (uncurry R) (b₁ ⋈ y) ↔ R b₁ y := by forall_elim h₅, b₁
  have h₇: (uncurry R) (b₁ ⋈ b₂) ↔ R b₁ b₂ := by forall_elim h₆, b₂

  -- Chain: (co_classification C).pred (b₁ ⋈ b₂) ↔ (uncurry R) (b₁ ⋈ b₂) ↔ R b₁ b₂
  -- (co_classification_rel C).pred = uncurry R by def unfolding
  -- R b₁ b₂ = ∃ a, b₁ ∈ₛₑₜ C(↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C(↑{a}ₛₑₜ) by def unfolding
  have h₈: (co_classification C).pred (b₁ ⋈ b₂) → ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by
    assume(ha: (co_classification C).pred (b₁ ⋈ b₂))
    have hb: (co_classification_rel C).pred (b₁ ⋈ b₂) := PC₀.deductive_eq_l2r h₄ ha
    have hc: R b₁ b₂ := PC₀.deductive_eq_l2r h₇ hb
    iterate hc

  have h₉: (∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ)) → (co_classification C).pred (b₁ ⋈ b₂) := by
    assume(ha: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
    have hb: (uncurry R) (b₁ ⋈ b₂) := PC₀.deductive_eq_r2l h₇ ha
    have hc: (co_classification C).pred (b₁ ⋈ b₂) := PC₀.deductive_eq_r2l h₄ hb
    iterate hc

  have h₁₀: (co_classification C).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by iff_intro h₈, h₉
  iterate h₁₀

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
theorem co_classification_cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂),
  C₁ =→ᶜ C₂ → co_classification C₁ =ᵣₑₗ co_classification C₂ := by forall_intro
  variable(C₁: U₁ ⭢ᶜ U₂)
  variable(C₂: U₁ ⭢ᶜ U₂)
  assume(h₁: C₁ =→ᶜ C₂)

  -- Set extensionality for the result (relations are sets of dyads)
  have h₂: ∀ (R₂: Set (U₂ ⧓ U₂)), co_classification C₁ =ₛₑₜ R₂ ↔ (∀ (d: U₂ ⋈ U₂), (co_classification C₁).pred d ↔ R₂.pred d) := by forall_elim eq_def, co_classification C₁
  have h₃: co_classification C₁ =ₛₑₜ co_classification C₂ ↔ (∀ (d: U₂ ⋈ U₂), (co_classification C₁).pred d ↔ (co_classification C₂).pred d) := by forall_elim h₂, co_classification C₂

  -- Ternary predicate cong: when C₁ =→ᶜ C₂, the predicates agree at any (b₁, b₂)
  have h₄₁: ∀ (C₂': U₁ ⭢ᶜ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    C₁ =→ᶜ C₂' → ((co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂' b₁).pred b₂) := by forall_elim co_classification_predicate.cong, C₁
  have h₄₂: ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    C₁ =→ᶜ C₂ → ((co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂) := by forall_elim h₄₁, C₂

  -- co_classification_unfold for both correspondences
  have h₅: ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    (co_classification C₁).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim co_classification_unfold, C₁
  have h₆: ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    (co_classification C₂).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim co_classification_unfold, C₂

  have h₇: ∀ (d: U₂ ⋈ U₂), (co_classification C₁).pred d ↔ (co_classification C₂).pred d := by forall_intro
    variable(d: U₂ ⋈ U₂)

    -- Decompose d via exhaustiveness
    have h₇₁: ∃ (b₁: U₂.Particular), ∃ (b₂: U₂.Particular), d 🟰 (b₁ ⋈ b₂) := by forall_elim exhaustiveness, d
    have ⟨(b₁: U₂.Particular), (h₇₂: ∃ (b₂: U₂.Particular), d 🟰 (b₁ ⋈ b₂))⟩ := exists_elim h₇₁
    have ⟨(b₂: U₂.Particular), (h₇₃: d 🟰 (b₁ ⋈ b₂))⟩ := exists_elim h₇₂

    -- Transfer .pred d ↔ .pred (b₁ ⋈ b₂) via Leibniz substitution
    let lpred₁: U₂ ⋈ U₂ → Prop := (x: U₂ ⋈ U₂ ↦ (co_classification C₁).pred x)
    have h₇₄: ∀ (x: U₂ ⋈ U₂), ∀ (y: U₂ ⋈ U₂), x 🟰 y → (lpred₁ x ↔ lpred₁ y) := by forall_elim leibniz_eq_subs, lpred₁
    have h₇₅: ∀ (y: U₂ ⋈ U₂), d 🟰 y → (lpred₁ d ↔ lpred₁ y) := by forall_elim h₇₄, d
    have h₇₆: d 🟰 (b₁ ⋈ b₂) → (lpred₁ d ↔ lpred₁ (b₁ ⋈ b₂)) := by forall_elim h₇₅, (b₁ ⋈ b₂)
    have h₇₇: (co_classification C₁).pred d ↔ (co_classification C₁).pred (b₁ ⋈ b₂) := by modus_ponens h₇₆, h₇₃

    let lpred₂: U₂ ⋈ U₂ → Prop := (x: U₂ ⋈ U₂ ↦ (co_classification C₂).pred x)
    have h₇₈: ∀ (x: U₂ ⋈ U₂), ∀ (y: U₂ ⋈ U₂), x 🟰 y → (lpred₂ x ↔ lpred₂ y) := by forall_elim leibniz_eq_subs, lpred₂
    have h₇₉: ∀ (y: U₂ ⋈ U₂), d 🟰 y → (lpred₂ d ↔ lpred₂ y) := by forall_elim h₇₈, d
    have h₇₁₀: d 🟰 (b₁ ⋈ b₂) → (lpred₂ d ↔ lpred₂ (b₁ ⋈ b₂)) := by forall_elim h₇₉, (b₁ ⋈ b₂)
    have h₇₁₁: (co_classification C₂).pred d ↔ (co_classification C₂).pred (b₁ ⋈ b₂) := by modus_ponens h₇₁₀, h₇₃

    -- Instantiate co_classification_unfold at (b₁, b₂)
    have h₇₁₂: ∀ (b₂': U₂.Particular), (co_classification C₁).pred (b₁ ⋈ b₂') ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim h₅, b₁
    have h₇₁₃: (co_classification C₁).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by forall_elim h₇₁₂, b₂

    have h₇₁₄: ∀ (b₂': U₂.Particular), (co_classification C₂).pred (b₁ ⋈ b₂') ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆, b₁
    have h₇₁₅: (co_classification C₂).pred (b₁ ⋈ b₂) ↔ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₇₁₄, b₂

    -- Ternary predicate cong at (b₁, b₂): the core transfer in one step
    have h₇₁₆: ∀ (b₂': U₂.Particular), C₁ =→ᶜ C₂ → ((co_classified_with C₁ b₁).pred b₂' ↔ (co_classified_with C₂ b₁).pred b₂') := by forall_elim h₄₂, b₁
    have h₇₁₇: C₁ =→ᶜ C₂ → ((co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂) := by forall_elim h₇₁₆, b₂
    have h₇₁₈: (co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂ := by modus_ponens h₇₁₇, h₁

    -- Forward: pred_C₁ d → pred_C₁ (b₁⋈b₂) → ∃a...C₁ → ∃a...C₂ → pred_C₂ (b₁⋈b₂) → pred_C₂ d
    have h₇₁₉: (co_classification C₁).pred d → (co_classification C₂).pred d := by
      assume(ha: (co_classification C₁).pred d)
      have hb: (co_classification C₁).pred (b₁ ⋈ b₂) := PC₀.deductive_eq_l2r h₇₇ ha
      have hc: (co_classified_with C₁ b₁).pred b₂ := PC₀.deductive_eq_l2r h₇₁₃ hb
      have hd: (co_classified_with C₂ b₁).pred b₂ := PC₀.deductive_eq_l2r h₇₁₈ hc
      have he: (co_classification C₂).pred (b₁ ⋈ b₂) := PC₀.deductive_eq_r2l h₇₁₅ hd
      have hf: (co_classification C₂).pred d := PC₀.deductive_eq_r2l h₇₁₁ he
      iterate hf

    -- Backward: pred_C₂ d → pred_C₂ (b₁⋈b₂) → ∃a...C₂ → ∃a...C₁ → pred_C₁ (b₁⋈b₂) → pred_C₁ d
    have h₇₂₀: (co_classification C₂).pred d → (co_classification C₁).pred d := by
      assume(ha: (co_classification C₂).pred d)
      have hb: (co_classification C₂).pred (b₁ ⋈ b₂) := PC₀.deductive_eq_l2r h₇₁₁ ha
      have hc: (co_classified_with C₂ b₁).pred b₂ := PC₀.deductive_eq_l2r h₇₁₅ hb
      have hd: (co_classified_with C₁ b₁).pred b₂ := PC₀.deductive_eq_r2l h₇₁₈ hc
      have he: (co_classification C₁).pred (b₁ ⋈ b₂) := PC₀.deductive_eq_r2l h₇₁₃ hd
      have hf: (co_classification C₁).pred d := PC₀.deductive_eq_r2l h₇₇ he
      iterate hf

    have h₇₂₁: (co_classification C₁).pred d ↔ (co_classification C₂).pred d := by iff_intro h₇₁₉, h₇₂₀
    iterate h₇₂₁

  have h₈: co_classification C₁ =ᵣₑₗ co_classification C₂ := PC₀.deductive_eq_r2l h₃ h₇
  iterate h₈

-- Co-classification as a congruent unary operation from correspondences to endo-relations.
noncomputable def co_classification_operation (U₁: Universal) (U₂: Universal): CongruentUnaryOperation (U₁ ➞ᶜ U₂) (𝐑𝐞𝐥 U₂ U₂) :=
  let op: U₁ ⭢ᶜ U₂ → Rel U₂ U₂ := co_classification
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂ → (co_classification C₁ =ᵣₑₗ co_classification C₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    have h₁: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → co_classification C₁ =ᵣₑₗ co_classification C₂' := by forall_elim co_classification_cong, C₁
    have h₂: C₁ =→ᶜ C₂ → co_classification C₁ =ᵣₑₗ co_classification C₂ := by forall_elim h₁, C₂
    assume(h₃: C₁ =→ᶜ C₂)
    have h₄: co_classification C₁ =ᵣₑₗ co_classification C₂ := by modus_ponens h₂, h₃
    iterate h₄
  { op := op, cong := cong }

end Correspondences

end Universe
