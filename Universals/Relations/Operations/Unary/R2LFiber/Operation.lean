import Universals.Relations.Universal
import Universals.Correspondences.Universal
import Universals.Sets
import Universals.Dyads

/-!
# Right-to-Left Fiber

-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets

-- Proof by GPT-5.4, 2026-03-08
theorem r2l_fiber_pred_cong {U₁: Universal} (R: Rel U₁ U₂) (b: U₂.Particular):
  ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), x =₍U₁₎ y → (R.pred (x ⋈ b) ↔ R.pred (y ⋈ b)) := by forall_intro
  variable(x₁: U₁.Particular)
  variable(x₂: U₁.Particular)
  assume(h₁: x₁ =₍U₁₎ x₂)
  have h₂: b =₍U₂₎ b := U₂.eq.refl b
  have h₃: x₁ =₍U₁₎ x₂ ∧ b =₍U₂₎ b := by and_intro h₁, h₂
  have h₄: ∀ (b₁: U₂.Particular), ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (x₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ x₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim Dyads.eq_def, x₁
  have h₅: ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (x₁ ⋈ b) =ₗₓₗ (a₂ ⋈ b₂) ↔ x₁ =₍U₁₎ a₂ ∧ b =₍U₂₎ b₂ := by forall_elim h₄, b
  have h₆: ∀ (b₂: U₂.Particular),
    (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b₂) ↔ x₁ =₍U₁₎ x₂ ∧ b =₍U₂₎ b₂ := by forall_elim h₅, x₂
  have h₇: (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b) ↔ x₁ =₍U₁₎ x₂ ∧ b =₍U₂₎ b := by forall_elim h₆, b
  have h₈: (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b) := PC₀.deductive_eq_r2l h₇ h₃
  have h₉: ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂), d₁ =ₗₓₗ d₂ → (R.pred d₁ ↔ R.pred d₂) := R.cong
  have h₁₀: ∀ (d₂: U₁ ⋈ U₂), (x₁ ⋈ b) =ₗₓₗ d₂ → (R.pred (x₁ ⋈ b) ↔ R.pred d₂) := by forall_elim h₉, (x₁ ⋈ b)
  have h₁₁: (x₁ ⋈ b) =ₗₓₗ (x₂ ⋈ b) → (R.pred (x₁ ⋈ b) ↔ R.pred (x₂ ⋈ b)) := by forall_elim h₁₀, (x₂ ⋈ b)
  have h₁₂: R.pred (x₁ ⋈ b) ↔ R.pred (x₂ ⋈ b) := by modus_ponens h₁₁, h₈
  iterate h₁₂

axiom r2l_fiber: Rel U₁ U₂ → U₂.Particular → Set U₁

-- # Axiom definition
axiom r2l_fiber_def: ∀ (R: Rel U₁ U₂), ∀ (b: U₂.Particular),
  r2l_fiber R b =ₛₑₜ { x: U₁.Particular | R.pred (x ⋈ b) } with r2l_fiber_pred_cong R b

-- # Congruence in R: equal relations produce equal fibers
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem r2l_fiber_cong_rel: ∀ (R₁: Rel U₁ U₂), ∀ (R₂: Rel U₁ U₂), ∀ (b: U₂.Particular),
  R₁ =ᵣₑₗ R₂ → (r2l_fiber R₁ b =ₛₑₜ r2l_fiber R₂ b) := by forall_intro
  variable(R₁: Rel U₁ U₂)
  variable(R₂: Rel U₁ U₂)
  variable(b: U₂.Particular)
  assume(h₁: R₁ =ᵣₑₗ R₂)
  -- Unfold relation equality: ∀ d, R₁.pred d ↔ R₂.pred d
  have h₂: ∀ (S₂: Rel U₁ U₂), R₁ =ₛₑₜ S₂ ↔ ∀ (d: U₁ ⋈ U₂), R₁.pred d ↔ S₂.pred d := by forall_elim eq_def, R₁
  have h₃: R₁ =ₛₑₜ R₂ ↔ ∀ (d: U₁ ⋈ U₂), R₁.pred d ↔ R₂.pred d := by forall_elim h₂, R₂
  have h₄: ∀ (d: U₁ ⋈ U₂), R₁.pred d ↔ R₂.pred d := PC₀.deductive_eq_l2r h₃ h₁
  -- Name the fiber comprehension sets
  let F₁ : Set U₁ := {x: U₁.Particular | R₁.pred (x ⋈ b)} with r2l_fiber_pred_cong R₁ b
  let F₂ : Set U₁ := {x: U₁.Particular | R₂.pred (x ⋈ b)} with r2l_fiber_pred_cong R₂ b
  -- Fiber axiom: r2l_fiber Rᵢ b =ₛₑₜ Fᵢ
  have h₅: r2l_fiber R₁ b =ₛₑₜ F₁ := r2l_fiber_def R₁ b
  have h₆: r2l_fiber R₂ b =ₛₑₜ F₂ := r2l_fiber_def R₂ b
  -- Unfold fiber set equalities to predicate level via eq_def
  have h₇: ∀ (S₂: Set U₁), (r2l_fiber R₁ b) =ₛₑₜ S₂ ↔ ∀ (z: U₁.Particular), (r2l_fiber R₁ b).pred z ↔ S₂.pred z := by forall_elim eq_def, (r2l_fiber R₁ b)
  have h₈: (r2l_fiber R₁ b) =ₛₑₜ F₁ ↔ ∀ (z: U₁.Particular), (r2l_fiber R₁ b).pred z ↔ F₁.pred z := by forall_elim h₇, F₁
  have h₉: ∀ (z: U₁.Particular), (r2l_fiber R₁ b).pred z ↔ F₁.pred z := PC₀.deductive_eq_l2r h₈ h₅
  have h₁₀: ∀ (S₂: Set U₁), (r2l_fiber R₂ b) =ₛₑₜ S₂ ↔ ∀ (z: U₁.Particular), (r2l_fiber R₂ b).pred z ↔ S₂.pred z := by forall_elim eq_def, (r2l_fiber R₂ b)
  have h₁₁: (r2l_fiber R₂ b) =ₛₑₜ F₂ ↔ ∀ (z: U₁.Particular), (r2l_fiber R₂ b).pred z ↔ F₂.pred z := by forall_elim h₁₀, F₂
  have h₁₂: ∀ (z: U₁.Particular), (r2l_fiber R₂ b).pred z ↔ F₂.pred z := PC₀.deductive_eq_l2r h₁₁ h₆
  -- Goal via eq_def
  have h₁₃: (r2l_fiber R₁ b) =ₛₑₜ (r2l_fiber R₂ b) ↔ ∀ (z: U₁.Particular), (r2l_fiber R₁ b).pred z ↔ (r2l_fiber R₂ b).pred z := by forall_elim h₇, (r2l_fiber R₂ b)
  have h₁₄: ∀ (z: U₁.Particular), (r2l_fiber R₁ b).pred z ↔ (r2l_fiber R₂ b).pred z := by forall_intro
    variable(z: U₁.Particular)
    have h₁₄₁: (r2l_fiber R₁ b).pred z ↔ F₁.pred z := by forall_elim h₉, z
    have h₁₄₂: (r2l_fiber R₂ b).pred z ↔ F₂.pred z := by forall_elim h₁₂, z
    have h₁₄₃: R₁.pred (z ⋈ b) ↔ R₂.pred (z ⋈ b) := by forall_elim h₄, (z ⋈ b)
    have h₁₄₄: (r2l_fiber R₁ b).pred z → (r2l_fiber R₂ b).pred z := by
      assume(h₁₄₄₁: (r2l_fiber R₁ b).pred z)
      have h₁₄₄₂: R₁.pred (z ⋈ b) := PC₀.deductive_eq_l2r h₁₄₁ h₁₄₄₁
      have h₁₄₄₃: R₂.pred (z ⋈ b) := PC₀.deductive_eq_l2r h₁₄₃ h₁₄₄₂
      have h₁₄₄₄: (r2l_fiber R₂ b).pred z := PC₀.deductive_eq_r2l h₁₄₂ h₁₄₄₃
      iterate h₁₄₄₄
    have h₁₄₅: (r2l_fiber R₂ b).pred z → (r2l_fiber R₁ b).pred z := by
      assume(h₁₄₅₁: (r2l_fiber R₂ b).pred z)
      have h₁₄₅₂: R₂.pred (z ⋈ b) := PC₀.deductive_eq_l2r h₁₄₂ h₁₄₅₁
      have h₁₄₅₃: R₁.pred (z ⋈ b) := PC₀.deductive_eq_r2l h₁₄₃ h₁₄₅₂
      have h₁₄₅₄: (r2l_fiber R₁ b).pred z := PC₀.deductive_eq_r2l h₁₄₁ h₁₄₅₃
      iterate h₁₄₅₄
    have h₁₄₆: (r2l_fiber R₁ b).pred z ↔ (r2l_fiber R₂ b).pred z := by iff_intro h₁₄₄, h₁₄₅
    iterate h₁₄₆
  have h₁₅: r2l_fiber R₁ b =ₛₑₜ r2l_fiber R₂ b := PC₀.deductive_eq_r2l h₁₃ h₁₄
  iterate h₁₅

-- # Congruence in b: equal individuals produce equal fibers
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem r2l_fiber_cong_arg: ∀ (R: Rel U₁ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
  b₁ =₍U₂₎ b₂ → (r2l_fiber R b₁ =ₛₑₜ r2l_fiber R b₂) := by forall_intro
  variable(R: Rel U₁ U₂)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  assume(h₁: b₁ =₍U₂₎ b₂)
  -- Name the fiber comprehension sets
  let F₁ : Set U₁ := {x: U₁.Particular | R.pred (x ⋈ b₁)} with r2l_fiber_pred_cong R b₁
  let F₂ : Set U₁ := {x: U₁.Particular | R.pred (x ⋈ b₂)} with r2l_fiber_pred_cong R b₂
  -- Fiber axiom: r2l_fiber R bᵢ =ₛₑₜ Fᵢ
  have h₂: r2l_fiber R b₁ =ₛₑₜ F₁ := r2l_fiber_def R b₁
  have h₃: r2l_fiber R b₂ =ₛₑₜ F₂ := r2l_fiber_def R b₂
  -- Unfold fiber set equalities to predicate level via eq_def
  have h₄: ∀ (S₂: Set U₁), (r2l_fiber R b₁) =ₛₑₜ S₂ ↔ ∀ (z: U₁.Particular), (r2l_fiber R b₁).pred z ↔ S₂.pred z := by forall_elim eq_def, (r2l_fiber R b₁)
  have h₅: (r2l_fiber R b₁) =ₛₑₜ F₁ ↔ ∀ (z: U₁.Particular), (r2l_fiber R b₁).pred z ↔ F₁.pred z := by forall_elim h₄, F₁
  have h₆: ∀ (z: U₁.Particular), (r2l_fiber R b₁).pred z ↔ F₁.pred z := PC₀.deductive_eq_l2r h₅ h₂
  have h₇: ∀ (S₂: Set U₁), (r2l_fiber R b₂) =ₛₑₜ S₂ ↔ ∀ (z: U₁.Particular), (r2l_fiber R b₂).pred z ↔ S₂.pred z := by forall_elim eq_def, (r2l_fiber R b₂)
  have h₈: (r2l_fiber R b₂) =ₛₑₜ F₂ ↔ ∀ (z: U₁.Particular), (r2l_fiber R b₂).pred z ↔ F₂.pred z := by forall_elim h₇, F₂
  have h₉: ∀ (z: U₁.Particular), (r2l_fiber R b₂).pred z ↔ F₂.pred z := PC₀.deductive_eq_l2r h₈ h₃
  -- Goal via eq_def
  have h₁₀: (r2l_fiber R b₁) =ₛₑₜ (r2l_fiber R b₂) ↔ ∀ (z: U₁.Particular), (r2l_fiber R b₁).pred z ↔ (r2l_fiber R b₂).pred z := by forall_elim h₄, (r2l_fiber R b₂)
  have h₁₁: ∀ (z: U₁.Particular), (r2l_fiber R b₁).pred z ↔ (r2l_fiber R b₂).pred z := by forall_intro
    variable(z: U₁.Particular)
    have h₁₁₁: (r2l_fiber R b₁).pred z ↔ F₁.pred z := by forall_elim h₆, z
    have h₁₁₂: (r2l_fiber R b₂).pred z ↔ F₂.pred z := by forall_elim h₉, z
    -- From b₁ =₍U₂₎ b₂, derive R.pred (z ⋈ b₁) ↔ R.pred (z ⋈ b₂) via dyad congruence
    have h₁₁₃: z =₍U₁₎ z := U₁.eq.refl z
    have h₁₁₄: z =₍U₁₎ z ∧ b₁ =₍U₂₎ b₂ := by and_intro h₁₁₃, h₁
    have h₁₁₅: ∀ (b₁': U₂.Particular), ∀ (a₂: U₁.Particular), ∀ (b₂': U₂.Particular),
      (z ⋈ b₁') =ₗₓₗ (a₂ ⋈ b₂') ↔ z =₍U₁₎ a₂ ∧ b₁' =₍U₂₎ b₂' := by forall_elim Dyads.eq_def, z
    have h₁₁₆: ∀ (a₂: U₁.Particular), ∀ (b₂': U₂.Particular),
      (z ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂') ↔ z =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₁₁₅, b₁
    have h₁₁₇: ∀ (b₂': U₂.Particular),
      (z ⋈ b₁) =ₗₓₗ (z ⋈ b₂') ↔ z =₍U₁₎ z ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₁₁₆, z
    have h₁₁₈: (z ⋈ b₁) =ₗₓₗ (z ⋈ b₂) ↔ z =₍U₁₎ z ∧ b₁ =₍U₂₎ b₂ := by forall_elim h₁₁₇, b₂
    have h₁₁₉: (z ⋈ b₁) =ₗₓₗ (z ⋈ b₂) := PC₀.deductive_eq_r2l h₁₁₈ h₁₁₄
    have h₁₁₁₀: ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂), d₁ =ₗₓₗ d₂ → (R.pred d₁ ↔ R.pred d₂) := R.cong
    have h₁₁₁₁: ∀ (d₂: U₁ ⋈ U₂), (z ⋈ b₁) =ₗₓₗ d₂ → (R.pred (z ⋈ b₁) ↔ R.pred d₂) := by forall_elim h₁₁₁₀, (z ⋈ b₁)
    have h₁₁₁₂: (z ⋈ b₁) =ₗₓₗ (z ⋈ b₂) → (R.pred (z ⋈ b₁) ↔ R.pred (z ⋈ b₂)) := by forall_elim h₁₁₁₁, (z ⋈ b₂)
    have h₁₁₁₃: R.pred (z ⋈ b₁) ↔ R.pred (z ⋈ b₂) := by modus_ponens h₁₁₁₂, h₁₁₉
    -- Chain: fiber₁.pred z → R.pred(z⋈b₁) → R.pred(z⋈b₂) → fiber₂.pred z
    have h₁₁₁₄: (r2l_fiber R b₁).pred z → (r2l_fiber R b₂).pred z := by
      assume(h₁₁₁₄₁: (r2l_fiber R b₁).pred z)
      have h₁₁₁₄₂: R.pred (z ⋈ b₁) := PC₀.deductive_eq_l2r h₁₁₁ h₁₁₁₄₁
      have h₁₁₁₄₃: R.pred (z ⋈ b₂) := PC₀.deductive_eq_l2r h₁₁₁₃ h₁₁₁₄₂
      have h₁₁₁₄₄: (r2l_fiber R b₂).pred z := PC₀.deductive_eq_r2l h₁₁₂ h₁₁₁₄₃
      iterate h₁₁₁₄₄
    have h₁₁₁₅: (r2l_fiber R b₂).pred z → (r2l_fiber R b₁).pred z := by
      assume(h₁₁₁₅₁: (r2l_fiber R b₂).pred z)
      have h₁₁₁₅₂: R.pred (z ⋈ b₂) := PC₀.deductive_eq_l2r h₁₁₂ h₁₁₁₅₁
      have h₁₁₁₅₃: R.pred (z ⋈ b₁) := PC₀.deductive_eq_r2l h₁₁₁₃ h₁₁₁₅₂
      have h₁₁₁₅₄: (r2l_fiber R b₁).pred z := PC₀.deductive_eq_r2l h₁₁₁ h₁₁₁₅₃
      iterate h₁₁₁₅₄
    have h₁₁₁₆: (r2l_fiber R b₁).pred z ↔ (r2l_fiber R b₂).pred z := by iff_intro h₁₁₁₄, h₁₁₁₅
    iterate h₁₁₁₆
  have h₁₂: r2l_fiber R b₁ =ₛₑₜ r2l_fiber R b₂ := PC₀.deductive_eq_r2l h₁₀ h₁₁
  iterate h₁₂

-- # r2l_fiber R as a CongruentUnaryOperation (for fixed R)
noncomputable def r2l_fiber_unary_operation (R: Rel U₁ U₂): CongruentUnaryOperation U₂ (𝐒𝐞𝐭 U₁) := {
  op := r2l_fiber R,
  cong := r2l_fiber_cong_arg R
}

-- # r2l_fiber as a CongruentBinaryOperation
noncomputable def r2l_fiber_operation: CongruentBinaryOperation (𝐑𝐞𝐥 U₁ U₂) U₂ (𝐒𝐞𝐭 U₁) := {
  op := r2l_fiber_unary_operation,
  cong := r2l_fiber_cong_rel
}

end Relations

end Universe
