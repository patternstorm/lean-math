import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Application.Operation
import Universals.Sets

/-!
# Correspondence Composition

Given `C₂: U₂ ⭢ᶜ U₃` and `C₁: U₁ ⭢ᶜ U₂`, their composition is a
correspondence `U₁ ⭢ᶜ U₃` whose classification chains through both:

```
(C₂ ∘ᶜ C₁)(a) = C₂(C₁(a))
```

At the arrow level, an arrow `(a ⭢ᵃ S)` is in `C₂ ∘ᶜ C₁` iff
`S` equals the result of applying C₂ to the set, i.e. classification, produced by C₁
from the singleton `{a}ₛₑₜ`.

Composition is a binary operation on correspondences, congruent in
both arguments.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Arrows

axiom compose: (U₂ ⭢ᶜ U₃) → (U₁ ⭢ᶜ U₂) → (U₁ ⭢ᶜ U₃)
infixr:90 " ∘ᶜ " => compose

axiom compose_def: ∀ (C₂: U₂ ⭢ᶜ U₃), ∀ (C₁: U₁ ⭢ᶜ U₂),
  ∀ (a: U₁.Particular), ∀ (S: Set U₃), (a ⭢ᵃ S) ∈ₛₑₜ (C₂ ∘ᶜ C₁) ↔ S =ₛₑₜ C₂ (C₁ (↑{a}ₛₑₜ))

-- Congruence in C₁ (second argument), fixing C₂.
-- If C =→ᶜ C' then C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ C'.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
theorem compose_cong_inner: ∀ (C₂: U₂ ⭢ᶜ U₃), ∀ (C: U₁ ⭢ᶜ U₂), ∀ (C': U₁ ⭢ᶜ U₂),
  C =→ᶜ C' → C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ C' := by forall_intro
  variable(C₂: U₂ ⭢ᶜ U₃)
  variable(C: U₁ ⭢ᶜ U₂)
  variable(C': U₁ ⭢ᶜ U₂)
  assume(h₁: C =→ᶜ C')

  -- From C =→ᶜ C', derive: for all S, C S =ₛₑₜ C' S
  have h₂: ∀ (D: U₁ ⭢ᶜ U₂), C =→ᶜ D → ∀ (S: Set U₁), C S =ₛₑₜ D S := by forall_elim apply_cong_first, C
  have h₃: C =→ᶜ C' → ∀ (S: Set U₁), C S =ₛₑₜ C' S := by forall_elim h₂, C'
  have h₄: ∀ (S: Set U₁), C S =ₛₑₜ C' S := by modus_ponens h₃, h₁

  -- From C S =ₛₑₜ C' S, derive C₂ (C S) =ₛₑₜ C₂ (C' S) via apply_cong_second
  have h₅: ∀ (S₁: Set U₂), ∀ (S₂: Set U₂), S₁ =ₛₑₜ S₂ → C₂ S₁ =ₛₑₜ C₂ S₂ := by forall_elim apply_cong_second, C₂

  -- Set extensionality for C₂ ∘ᶜ C =ₛₑₜ C₂ ∘ᶜ C'
  have h₆: ∀ (S: Set (U₁ ➞ᵃ (𝐒𝐞𝐭 U₃))), C₂ ∘ᶜ C =ₛₑₜ S ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f ∈ₛₑₜ C₂ ∘ᶜ C ↔ f ∈ₛₑₜ S) := by forall_elim set_extensionality, C₂ ∘ᶜ C
  have h₇: C₂ ∘ᶜ C =ₛₑₜ C₂ ∘ᶜ C' ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f ∈ₛₑₜ C₂ ∘ᶜ C ↔ f ∈ₛₑₜ C₂ ∘ᶜ C') := by forall_elim h₆, C₂ ∘ᶜ C'

  -- Prove pointwise membership equivalence
  have h₈: ∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f ∈ₛₑₜ C₂ ∘ᶜ C ↔ f ∈ₛₑₜ C₂ ∘ᶜ C' := by forall_intro
    variable(f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃))

    -- Decompose f via exhaustiveness
    have h₈₁: ∃ (a: U₁.Particular), ∃ (W: (𝐒𝐞𝐭 U₃).Particular), f 🟰 (a ⭢ᵃ W) := by forall_elim exhaustiveness, f
    have ⟨(a: U₁.Particular), (h₈₂: ∃ (W: (𝐒𝐞𝐭 U₃).Particular), f 🟰 (a ⭢ᵃ W))⟩ := exists_elim h₈₁
    have ⟨(W: Set U₃), (h₈₃: f 🟰 (a ⭢ᵃ W))⟩ := exists_elim h₈₂

    -- Leibniz transfer: f ∈ₛₑₜ X ↔ (a ⭢ᵃ W) ∈ₛₑₜ X for any set X
    let pred_mem₁: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)) → Prop := (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃) ↦ x ∈ₛₑₜ C₂ ∘ᶜ C)
    have h₈₄: ∀ (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), x 🟰 y → (pred_mem₁ x ↔ pred_mem₁ y) := by forall_elim leibniz_eq_subs, pred_mem₁
    have h₈₅: ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f 🟰 y → (pred_mem₁ f ↔ pred_mem₁ y) := by forall_elim h₈₄, f
    have h₈₆: f 🟰 (a ⭢ᵃ W) → (pred_mem₁ f ↔ pred_mem₁ (a ⭢ᵃ W)) := by forall_elim h₈₅, (a ⭢ᵃ W)
    have h₈₇: f ∈ₛₑₜ C₂ ∘ᶜ C ↔ (a ⭢ᵃ W) ∈ₛₑₜ C₂ ∘ᶜ C := by modus_ponens h₈₆, h₈₃

    let pred_mem₂: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)) → Prop := (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃) ↦ x ∈ₛₑₜ C₂ ∘ᶜ C')
    have h₈₈: ∀ (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), x 🟰 y → (pred_mem₂ x ↔ pred_mem₂ y) := by forall_elim leibniz_eq_subs, pred_mem₂
    have h₈₉: ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f 🟰 y → (pred_mem₂ f ↔ pred_mem₂ y) := by forall_elim h₈₈, f
    have h₈₁₀: f 🟰 (a ⭢ᵃ W) → (pred_mem₂ f ↔ pred_mem₂ (a ⭢ᵃ W)) := by forall_elim h₈₉, (a ⭢ᵃ W)
    have h₈₁₁: f ∈ₛₑₜ C₂ ∘ᶜ C' ↔ (a ⭢ᵃ W) ∈ₛₑₜ C₂ ∘ᶜ C' := by modus_ponens h₈₁₀, h₈₃

    -- compose_def for both sides
    have h₈₁₂: ∀ (C₁': U₁ ⭢ᶜ U₂), ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C₂ ∘ᶜ C₁') ↔ W' =ₛₑₜ C₂ (C₁' (↑{a'}ₛₑₜ)) := by forall_elim compose_def, C₂
    have h₈₁₃: ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C₂ ∘ᶜ C) ↔ W' =ₛₑₜ C₂ (C (↑{a'}ₛₑₜ)) := by forall_elim h₈₁₂, C
    have h₈₁₄: ∀ (W': Set U₃), (a ⭢ᵃ W') ∈ₛₑₜ (C₂ ∘ᶜ C) ↔ W' =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) := by forall_elim h₈₁₃, a
    have h₈₁₅: (a ⭢ᵃ W) ∈ₛₑₜ (C₂ ∘ᶜ C) ↔ W =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) := by forall_elim h₈₁₄, W

    have h₈₁₆: ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C₂ ∘ᶜ C') ↔ W' =ₛₑₜ C₂ (C' (↑{a'}ₛₑₜ)) := by forall_elim h₈₁₂, C'
    have h₈₁₇: ∀ (W': Set U₃), (a ⭢ᵃ W') ∈ₛₑₜ (C₂ ∘ᶜ C') ↔ W' =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := by forall_elim h₈₁₆, a
    have h₈₁₈: (a ⭢ᵃ W) ∈ₛₑₜ (C₂ ∘ᶜ C') ↔ W =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := by forall_elim h₈₁₇, W

    -- Key: C (↑{a}ₛₑₜ) =ₛₑₜ C' (↑{a}ₛₑₜ)
    have h₈₁₉: C (↑{a}ₛₑₜ) =ₛₑₜ C' (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)

    -- Hence C₂ (C (↑{a}ₛₑₜ)) =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ))
    have h₈₂₀: ∀ (S₂: Set U₂), C (↑{a}ₛₑₜ) =ₛₑₜ S₂ → C₂ (C (↑{a}ₛₑₜ)) =ₛₑₜ C₂ S₂ := by forall_elim h₅, C (↑{a}ₛₑₜ)
    have h₈₂₁: C (↑{a}ₛₑₜ) =ₛₑₜ C' (↑{a}ₛₑₜ) → C₂ (C (↑{a}ₛₑₜ)) =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := by forall_elim h₈₂₀, C' (↑{a}ₛₑₜ)
    have h₈₂₂: C₂ (C (↑{a}ₛₑₜ)) =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := by modus_ponens h₈₂₁, h₈₁₉

    -- Forward: f ∈ C₂ ∘ᶜ C → f ∈ C₂ ∘ᶜ C'
    have h₈₂₃: f ∈ₛₑₜ C₂ ∘ᶜ C → f ∈ₛₑₜ C₂ ∘ᶜ C' := by
      assume(h₈₂₃₁: f ∈ₛₑₜ C₂ ∘ᶜ C)
      have h₈₂₃₂: (a ⭢ᵃ W) ∈ₛₑₜ C₂ ∘ᶜ C := PC₀.deductive_eq_l2r h₈₇ h₈₂₃₁
      have h₈₂₃₃: W =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₈₁₅ h₈₂₃₂
      -- W =ₛₑₜ C₂ (C ...) and C₂ (C ...) =ₛₑₜ C₂ (C' ...)
      -- So W =ₛₑₜ C₂ (C' ...) by transitivity
      have h₈₂₃₄: W =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) ∧ C₂ (C (↑{a}ₛₑₜ)) =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := by and_intro h₈₂₃₃, h₈₂₂
      have h₈₂₃₅: W =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := (𝐒𝐞𝐭 U₃).eq.trans W (C₂ (C (↑{a}ₛₑₜ))) (C₂ (C' (↑{a}ₛₑₜ))) h₈₂₃₄
      have h₈₂₃₆: (a ⭢ᵃ W) ∈ₛₑₜ C₂ ∘ᶜ C' := PC₀.deductive_eq_r2l h₈₁₈ h₈₂₃₅
      have h₈₂₃₇: f ∈ₛₑₜ C₂ ∘ᶜ C' := PC₀.deductive_eq_r2l h₈₁₁ h₈₂₃₆
      iterate h₈₂₃₇

    -- Backward: f ∈ C₂ ∘ᶜ C' → f ∈ C₂ ∘ᶜ C
    have h₈₂₄: f ∈ₛₑₜ C₂ ∘ᶜ C' → f ∈ₛₑₜ C₂ ∘ᶜ C := by
      assume(h₈₂₄₁: f ∈ₛₑₜ C₂ ∘ᶜ C')
      have h₈₂₄₂: (a ⭢ᵃ W) ∈ₛₑₜ C₂ ∘ᶜ C' := PC₀.deductive_eq_l2r h₈₁₁ h₈₂₄₁
      have h₈₂₄₃: W =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₈₁₈ h₈₂₄₂
      -- Reverse: C₂ (C' ...) =ₛₑₜ C₂ (C ...)
      have h₈₂₄₄: C₂ (C' (↑{a}ₛₑₜ)) =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) := (𝐒𝐞𝐭 U₃).eq.sym (C₂ (C (↑{a}ₛₑₜ))) (C₂ (C' (↑{a}ₛₑₜ))) h₈₂₂
      have h₈₂₄₅: W =ₛₑₜ C₂ (C' (↑{a}ₛₑₜ)) ∧ C₂ (C' (↑{a}ₛₑₜ)) =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) := by and_intro h₈₂₄₃, h₈₂₄₄
      have h₈₂₄₆: W =ₛₑₜ C₂ (C (↑{a}ₛₑₜ)) := (𝐒𝐞𝐭 U₃).eq.trans W (C₂ (C' (↑{a}ₛₑₜ))) (C₂ (C (↑{a}ₛₑₜ))) h₈₂₄₅
      have h₈₂₄₇: (a ⭢ᵃ W) ∈ₛₑₜ C₂ ∘ᶜ C := PC₀.deductive_eq_r2l h₈₁₅ h₈₂₄₆
      have h₈₂₄₈: f ∈ₛₑₜ C₂ ∘ᶜ C := PC₀.deductive_eq_r2l h₈₇ h₈₂₄₇
      iterate h₈₂₄₈

    have h₈₂₅: f ∈ₛₑₜ C₂ ∘ᶜ C ↔ f ∈ₛₑₜ C₂ ∘ᶜ C' := by iff_intro h₈₂₃, h₈₂₄
    iterate h₈₂₅

  have h₉: C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ C' := PC₀.deductive_eq_r2l h₇ h₈
  iterate h₉

-- Congruence in C₂ (first argument), fixing C₁.
-- If C =→ᶜ C' then C ∘ᶜ C₁ =→ᶜ C' ∘ᶜ C₁.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
theorem compose_cong_outer: ∀ (C: U₂ ⭢ᶜ U₃), ∀ (C': U₂ ⭢ᶜ U₃), ∀ (C₁: U₁ ⭢ᶜ U₂),
  C =→ᶜ C' → C ∘ᶜ C₁ =→ᶜ C' ∘ᶜ C₁ := by forall_intro
  variable(C: U₂ ⭢ᶜ U₃)
  variable(C': U₂ ⭢ᶜ U₃)
  variable(C₁: U₁ ⭢ᶜ U₂)
  assume(h₁: C =→ᶜ C')

  -- From C =→ᶜ C', derive: for all S, C S =ₛₑₜ C' S
  have h₂: ∀ (C₂': U₂ ⭢ᶜ U₃), C =→ᶜ C₂' → ∀ (S: Set U₂), C S =ₛₑₜ C₂' S := by forall_elim apply_cong_first, C
  have h₃: C =→ᶜ C' → ∀ (S: Set U₂), C S =ₛₑₜ C' S := by forall_elim h₂, C'
  have h₄: ∀ (S: Set U₂), C S =ₛₑₜ C' S := by modus_ponens h₃, h₁

  -- Set extensionality for C ∘ᶜ C₁ =ₛₑₜ C' ∘ᶜ C₁
  have h₅: ∀ (R₂: Set (U₁ ➞ᵃ (𝐒𝐞𝐭 U₃))), C ∘ᶜ C₁ =ₛₑₜ R₂ ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f ∈ₛₑₜ C ∘ᶜ C₁ ↔ f ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C ∘ᶜ C₁
  have h₆: C ∘ᶜ C₁ =ₛₑₜ C' ∘ᶜ C₁ ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f ∈ₛₑₜ C ∘ᶜ C₁ ↔ f ∈ₛₑₜ C' ∘ᶜ C₁) := by forall_elim h₅, C' ∘ᶜ C₁

  -- Prove pointwise membership equivalence
  have h₇: ∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f ∈ₛₑₜ C ∘ᶜ C₁ ↔ f ∈ₛₑₜ C' ∘ᶜ C₁ := by forall_intro
    variable(f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃))

    -- Decompose f via exhaustiveness
    have h₇₁: ∃ (a: U₁.Particular), ∃ (W: (𝐒𝐞𝐭 U₃).Particular), f 🟰 (a ⭢ᵃ W) := by forall_elim exhaustiveness, f
    have ⟨(a: U₁.Particular), (h₇₂: ∃ (W: (𝐒𝐞𝐭 U₃).Particular), f 🟰 (a ⭢ᵃ W))⟩ := exists_elim h₇₁
    have ⟨(W: Set U₃), (h₇₃: f 🟰 (a ⭢ᵃ W))⟩ := exists_elim h₇₂

    -- Leibniz transfer: f ∈ₛₑₜ X ↔ (a ⭢ᵃ W) ∈ₛₑₜ X
    let pred_mem₁: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)) → Prop := (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃) ↦ x ∈ₛₑₜ C ∘ᶜ C₁)
    have h₇₄: ∀ (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), x 🟰 y → (pred_mem₁ x ↔ pred_mem₁ y) := by forall_elim leibniz_eq_subs, pred_mem₁
    have h₇₅: ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f 🟰 y → (pred_mem₁ f ↔ pred_mem₁ y) := by forall_elim h₇₄, f
    have h₇₆: f 🟰 (a ⭢ᵃ W) → (pred_mem₁ f ↔ pred_mem₁ (a ⭢ᵃ W)) := by forall_elim h₇₅, (a ⭢ᵃ W)
    have h₇₇: f ∈ₛₑₜ C ∘ᶜ C₁ ↔ (a ⭢ᵃ W) ∈ₛₑₜ C ∘ᶜ C₁ := by modus_ponens h₇₆, h₇₃

    let pred_mem₂: (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)) → Prop := (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃) ↦ x ∈ₛₑₜ C' ∘ᶜ C₁)
    have h₇₈: ∀ (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), x 🟰 y → (pred_mem₂ x ↔ pred_mem₂ y) := by forall_elim leibniz_eq_subs, pred_mem₂
    have h₇₉: ∀ (y: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₃)), f 🟰 y → (pred_mem₂ f ↔ pred_mem₂ y) := by forall_elim h₇₈, f
    have h₇₁₀: f 🟰 (a ⭢ᵃ W) → (pred_mem₂ f ↔ pred_mem₂ (a ⭢ᵃ W)) := by forall_elim h₇₉, (a ⭢ᵃ W)
    have h₇₁₁: f ∈ₛₑₜ C' ∘ᶜ C₁ ↔ (a ⭢ᵃ W) ∈ₛₑₜ C' ∘ᶜ C₁ := by modus_ponens h₇₁₀, h₇₃

    -- compose_def for both sides
    have h₇₁₂: ∀ (C₂': U₂ ⭢ᶜ U₃), ∀ (C₁': U₁ ⭢ᶜ U₂), ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C₂' ∘ᶜ C₁') ↔ W' =ₛₑₜ C₂' (C₁' (↑{a'}ₛₑₜ)) := compose_def
    have h₇₁₃: ∀ (C₁': U₁ ⭢ᶜ U₂), ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C ∘ᶜ C₁') ↔ W' =ₛₑₜ C (C₁' (↑{a'}ₛₑₜ)) := by forall_elim h₇₁₂, C
    have h₇₁₄: ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C ∘ᶜ C₁) ↔ W' =ₛₑₜ C (C₁ (↑{a'}ₛₑₜ)) := by forall_elim h₇₁₃, C₁
    have h₇₁₅: ∀ (W': Set U₃), (a ⭢ᵃ W') ∈ₛₑₜ (C ∘ᶜ C₁) ↔ W' =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) := by forall_elim h₇₁₄, a
    have h₇₁₆: (a ⭢ᵃ W) ∈ₛₑₜ (C ∘ᶜ C₁) ↔ W =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) := by forall_elim h₇₁₅, W

    have h₇₁₇: ∀ (C₁': U₁ ⭢ᶜ U₂), ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C' ∘ᶜ C₁') ↔ W' =ₛₑₜ C' (C₁' (↑{a'}ₛₑₜ)) := by forall_elim h₇₁₂, C'
    have h₇₁₈: ∀ (a': U₁.Particular), ∀ (W': Set U₃), (a' ⭢ᵃ W') ∈ₛₑₜ (C' ∘ᶜ C₁) ↔ W' =ₛₑₜ C' (C₁ (↑{a'}ₛₑₜ)) := by forall_elim h₇₁₇, C₁
    have h₇₁₉: ∀ (W': Set U₃), (a ⭢ᵃ W') ∈ₛₑₜ (C' ∘ᶜ C₁) ↔ W' =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) := by forall_elim h₇₁₈, a
    have h₇₂₀: (a ⭢ᵃ W) ∈ₛₑₜ (C' ∘ᶜ C₁) ↔ W =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) := by forall_elim h₇₁₉, W

    -- Key: C (C₁ (↑{a}ₛₑₜ)) =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ))
    have h₇₂₁: C (C₁ (↑{a}ₛₑₜ)) =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) := by forall_elim h₄, C₁ (↑{a}ₛₑₜ)

    -- Forward: f ∈ C ∘ᶜ C₁ → f ∈ C' ∘ᶜ C₁
    have h₇₂₂: f ∈ₛₑₜ C ∘ᶜ C₁ → f ∈ₛₑₜ C' ∘ᶜ C₁ := by
      assume(h₇₂₂₁: f ∈ₛₑₜ C ∘ᶜ C₁)
      have h₇₂₂₂: (a ⭢ᵃ W) ∈ₛₑₜ C ∘ᶜ C₁ := PC₀.deductive_eq_l2r h₇₇ h₇₂₂₁
      have h₇₂₂₃: W =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₇₁₆ h₇₂₂₂
      have h₇₂₂₄: W =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) ∧ C (C₁ (↑{a}ₛₑₜ)) =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) := by and_intro h₇₂₂₃, h₇₂₁
      have h₇₂₂₅: W =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) := (𝐒𝐞𝐭 U₃).eq.trans W (C (C₁ (↑{a}ₛₑₜ))) (C' (C₁ (↑{a}ₛₑₜ))) h₇₂₂₄
      have h₇₂₂₆: (a ⭢ᵃ W) ∈ₛₑₜ C' ∘ᶜ C₁ := PC₀.deductive_eq_r2l h₇₂₀ h₇₂₂₅
      have h₇₂₂₇: f ∈ₛₑₜ C' ∘ᶜ C₁ := PC₀.deductive_eq_r2l h₇₁₁ h₇₂₂₆
      iterate h₇₂₂₇

    -- Backward: f ∈ C' ∘ᶜ C₁ → f ∈ C ∘ᶜ C₁
    have h₇₂₃: f ∈ₛₑₜ C' ∘ᶜ C₁ → f ∈ₛₑₜ C ∘ᶜ C₁ := by
      assume(h₇₂₃₁: f ∈ₛₑₜ C' ∘ᶜ C₁)
      have h₇₂₃₂: (a ⭢ᵃ W) ∈ₛₑₜ C' ∘ᶜ C₁ := PC₀.deductive_eq_l2r h₇₁₁ h₇₂₃₁
      have h₇₂₃₃: W =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) := PC₀.deductive_eq_l2r h₇₂₀ h₇₂₃₂
      have h₇₂₃₄: C' (C₁ (↑{a}ₛₑₜ)) =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) := (𝐒𝐞𝐭 U₃).eq.sym (C (C₁ (↑{a}ₛₑₜ))) (C' (C₁ (↑{a}ₛₑₜ))) h₇₂₁
      have h₇₂₃₅: W =ₛₑₜ C' (C₁ (↑{a}ₛₑₜ)) ∧ C' (C₁ (↑{a}ₛₑₜ)) =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) := by and_intro h₇₂₃₃, h₇₂₃₄
      have h₇₂₃₆: W =ₛₑₜ C (C₁ (↑{a}ₛₑₜ)) := (𝐒𝐞𝐭 U₃).eq.trans W (C' (C₁ (↑{a}ₛₑₜ))) (C (C₁ (↑{a}ₛₑₜ))) h₇₂₃₅
      have h₇₂₃₇: (a ⭢ᵃ W) ∈ₛₑₜ C ∘ᶜ C₁ := PC₀.deductive_eq_r2l h₇₁₆ h₇₂₃₆
      have h₇₂₃₈: f ∈ₛₑₜ C ∘ᶜ C₁ := PC₀.deductive_eq_r2l h₇₇ h₇₂₃₇
      iterate h₇₂₃₈

    have h₇₂₄: f ∈ₛₑₜ C ∘ᶜ C₁ ↔ f ∈ₛₑₜ C' ∘ᶜ C₁ := by iff_intro h₇₂₂, h₇₂₃
    iterate h₇₂₄

  have h₈: C ∘ᶜ C₁ =→ᶜ C' ∘ᶜ C₁ := PC₀.deductive_eq_r2l h₆ h₇
  iterate h₈

-- For fixed C₂, compose maps correspondences to correspondences, congruent in C₁.
noncomputable def compose_with (C₂: U₂ ⭢ᶜ U₃): CongruentUnaryOperation (U₁ ➞ᶜ U₂) (U₁ ➞ᶜ U₃) :=
  let op: U₁ ⭢ᶜ U₂ → U₁ ⭢ᶜ U₃ := (C₁: U₁ ⭢ᶜ U₂ ↦ C₂ ∘ᶜ C₁)
  let cong: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (C': U₁ ⭢ᶜ U₂), C =→ᶜ C' → (C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ C') := by forall_intro
    variable(C: U₁ ⭢ᶜ U₂)
    variable(C': U₁ ⭢ᶜ U₂)
    have h₁: ∀ (A: U₁ ⭢ᶜ U₂), ∀ (B: U₁ ⭢ᶜ U₂),
      A =→ᶜ B → C₂ ∘ᶜ A =→ᶜ C₂ ∘ᶜ B := by forall_elim compose_cong_inner, C₂
    have h₂: ∀ (B: U₁ ⭢ᶜ U₂), C =→ᶜ B → C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ B := by forall_elim h₁, C
    have h₃: C =→ᶜ C' → C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ C' := by forall_elim h₂, C'
    assume(h₄: C =→ᶜ C')
    have h₅: C₂ ∘ᶜ C =→ᶜ C₂ ∘ᶜ C' := by modus_ponens h₃, h₄
    iterate h₅
  { op := op, cong := cong }

-- Full binary operation, congruent in both arguments.
noncomputable def compose_operation: CongruentBinaryOperation (U₂ ➞ᶜ U₃) (U₁ ➞ᶜ U₂) (U₁ ➞ᶜ U₃) :=
  let op: U₂ ⭢ᶜ U₃ → CongruentUnaryOperation (U₁ ➞ᶜ U₂) (U₁ ➞ᶜ U₃) := (C₂: U₂ ⭢ᶜ U₃ ↦ compose_with C₂)
  let cong: ∀ (C: U₂ ⭢ᶜ U₃), ∀ (C': U₂ ⭢ᶜ U₃), ∀ (C₁: U₁ ⭢ᶜ U₂),
    C =→ᶜ C' → ((compose_with C).op C₁ =→ᶜ (compose_with C').op C₁) := by forall_intro
    variable(C: U₂ ⭢ᶜ U₃)
    variable(C': U₂ ⭢ᶜ U₃)
    variable(C₁: U₁ ⭢ᶜ U₂)
    have h₁: ∀ (A: U₂ ⭢ᶜ U₃), ∀ (B: U₁ ⭢ᶜ U₂), C =→ᶜ A → C ∘ᶜ B =→ᶜ A ∘ᶜ B := by forall_elim compose_cong_outer, C
    have h₂: ∀ (B: U₁ ⭢ᶜ U₂), C =→ᶜ C' → C ∘ᶜ B =→ᶜ C' ∘ᶜ B := by forall_elim h₁, C'
    have h₃: C =→ᶜ C' → C ∘ᶜ C₁ =→ᶜ C' ∘ᶜ C₁ := by forall_elim h₂, C₁
    assume(h₄: C =→ᶜ C')
    have h₅: C ∘ᶜ C₁ =→ᶜ C' ∘ᶜ C₁ := by modus_ponens h₃, h₄
    iterate h₅
  { op := op, cong := cong }

end Correspondences

end Universe
