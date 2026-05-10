import Universals.Relations.Universal
import Universals.Correspondences.Universal
import Universals.Sets
import Universals.Dyads

/-!
# Left-to-Right Fiber

-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets

axiom l2r_fiber: Rel U₁ U₂ → U₁.Particular → Set U₂

-- # Axiom definition
axiom l2r_fiber_def: ∀ (R: Rel U₁ U₂), ∀ (a: U₁.Particular),
  l2r_fiber R a =ₛₑₜ { y: U₂.Particular | R.pred (a ⋈ y) }

-- # Congruence in R: equal relations produce equal fibers
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem l2r_fiber_cong_rel: ∀ (R₁: Rel U₁ U₂), ∀ (R₂: Rel U₁ U₂), ∀ (a: U₁.Particular),
  R₁ =ᵣₑₗ R₂ → (l2r_fiber R₁ a =ₛₑₜ l2r_fiber R₂ a) := by forall_intro
  variable(R₁: Rel U₁ U₂)
  variable(R₂: Rel U₁ U₂)
  variable(a: U₁.Particular)
  assume(h₁: R₁ =ᵣₑₗ R₂)
  -- Unfold relation equality: ∀ d, R₁.pred d ↔ R₂.pred d
  have h₂: ∀ (S₂: Rel U₁ U₂), R₁ =ₛₑₜ S₂ ↔ ∀ (d: U₁ ⋈ U₂), R₁.pred d ↔ S₂.pred d := by forall_elim eq_def, R₁
  have h₃: R₁ =ₛₑₜ R₂ ↔ ∀ (d: U₁ ⋈ U₂), R₁.pred d ↔ R₂.pred d := by forall_elim h₂, R₂
  have h₄: ∀ (d: U₁ ⋈ U₂), R₁.pred d ↔ R₂.pred d := PC₀.deductive_eq_l2r h₃ h₁
  -- Name the fiber comprehension sets
  let F₁ : Set U₂ := {y: U₂.Particular | R₁.pred (a ⋈ y)}
  let F₂ : Set U₂ := {y: U₂.Particular | R₂.pred (a ⋈ y)}
  -- Fiber axiom: l2r_fiber Rᵢ a =ₛₑₜ Fᵢ (term-mode application of axiom)
  have h₅: l2r_fiber R₁ a =ₛₑₜ F₁ := l2r_fiber_def R₁ a
  have h₆: l2r_fiber R₂ a =ₛₑₜ F₂ := l2r_fiber_def R₂ a
  -- Unfold fiber set equalities to predicate level via eq_def
  have h₇: ∀ (S₂: Set U₂), (l2r_fiber R₁ a) =ₛₑₜ S₂ ↔ ∀ (z: U₂.Particular), (l2r_fiber R₁ a).pred z ↔ S₂.pred z := by forall_elim eq_def, (l2r_fiber R₁ a)
  have h₈: (l2r_fiber R₁ a) =ₛₑₜ F₁ ↔ ∀ (z: U₂.Particular), (l2r_fiber R₁ a).pred z ↔ F₁.pred z := by forall_elim h₇, F₁
  have h₉: ∀ (z: U₂.Particular), (l2r_fiber R₁ a).pred z ↔ F₁.pred z := PC₀.deductive_eq_l2r h₈ h₅
  have h₁₀: ∀ (S₂: Set U₂), (l2r_fiber R₂ a) =ₛₑₜ S₂ ↔ ∀ (z: U₂.Particular), (l2r_fiber R₂ a).pred z ↔ S₂.pred z := by forall_elim eq_def, (l2r_fiber R₂ a)
  have h₁₁: (l2r_fiber R₂ a) =ₛₑₜ F₂ ↔ ∀ (z: U₂.Particular), (l2r_fiber R₂ a).pred z ↔ F₂.pred z := by forall_elim h₁₀, F₂
  have h₁₂: ∀ (z: U₂.Particular), (l2r_fiber R₂ a).pred z ↔ F₂.pred z := PC₀.deductive_eq_l2r h₁₁ h₆
  -- Goal via eq_def: suffices to show ∀ z, (l2r_fiber R₁ a).pred z ↔ (l2r_fiber R₂ a).pred z
  have h₁₃: (l2r_fiber R₁ a) =ₛₑₜ (l2r_fiber R₂ a) ↔ ∀ (z: U₂.Particular), (l2r_fiber R₁ a).pred z ↔ (l2r_fiber R₂ a).pred z := by forall_elim h₇, (l2r_fiber R₂ a)
  have h₁₄: ∀ (z: U₂.Particular), (l2r_fiber R₁ a).pred z ↔ (l2r_fiber R₂ a).pred z := by forall_intro
    variable(z: U₂.Particular)
    -- Fᵢ.pred z reduces to Rᵢ.pred (a ⋈ z) by β-reduction
    have h₁₄₁: (l2r_fiber R₁ a).pred z ↔ F₁.pred z := by forall_elim h₉, z
    have h₁₄₂: (l2r_fiber R₂ a).pred z ↔ F₂.pred z := by forall_elim h₁₂, z
    have h₁₄₃: R₁.pred (a ⋈ z) ↔ R₂.pred (a ⋈ z) := by forall_elim h₄, (a ⋈ z)
    -- Chain: fiber₁.pred z → R₁.pred(a⋈z) → R₂.pred(a⋈z) → fiber₂.pred z
    have h₁₄₄: (l2r_fiber R₁ a).pred z → (l2r_fiber R₂ a).pred z := by
      assume(h₁₄₄₁: (l2r_fiber R₁ a).pred z)
      have h₁₄₄₂: R₁.pred (a ⋈ z) := PC₀.deductive_eq_l2r h₁₄₁ h₁₄₄₁
      have h₁₄₄₃: R₂.pred (a ⋈ z) := PC₀.deductive_eq_l2r h₁₄₃ h₁₄₄₂
      have h₁₄₄₄: (l2r_fiber R₂ a).pred z := PC₀.deductive_eq_r2l h₁₄₂ h₁₄₄₃
      iterate h₁₄₄₄
    have h₁₄₅: (l2r_fiber R₂ a).pred z → (l2r_fiber R₁ a).pred z := by
      assume(h₁₄₅₁: (l2r_fiber R₂ a).pred z)
      have h₁₄₅₂: R₂.pred (a ⋈ z) := PC₀.deductive_eq_l2r h₁₄₂ h₁₄₅₁
      have h₁₄₅₃: R₁.pred (a ⋈ z) := PC₀.deductive_eq_r2l h₁₄₃ h₁₄₅₂
      have h₁₄₅₄: (l2r_fiber R₁ a).pred z := PC₀.deductive_eq_r2l h₁₄₁ h₁₄₅₃
      iterate h₁₄₅₄
    have h₁₄₆: (l2r_fiber R₁ a).pred z ↔ (l2r_fiber R₂ a).pred z := by iff_intro h₁₄₄, h₁₄₅
    iterate h₁₄₆
  have h₁₅: l2r_fiber R₁ a =ₛₑₜ l2r_fiber R₂ a := PC₀.deductive_eq_r2l h₁₃ h₁₄
  iterate h₁₅

-- # Congruence in a: equal individuals produce equal fibers
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem l2r_fiber_cong_arg: ∀ (R: Rel U₁ U₂), ∀ (a₁: U₁.Particular), ∀ (a₂: U₁.Particular),
  a₁ =₍U₁₎ a₂ → (l2r_fiber R a₁ =ₛₑₜ l2r_fiber R a₂) := by forall_intro
  variable(R: Rel U₁ U₂)
  variable(a₁: U₁.Particular)
  variable(a₂: U₁.Particular)
  assume(h₁: a₁ =₍U₁₎ a₂)
  -- Name the fiber comprehension sets
  let F₁ : Set U₂ := {y: U₂.Particular | R.pred (a₁ ⋈ y)}
  let F₂ : Set U₂ := {y: U₂.Particular | R.pred (a₂ ⋈ y)}
  -- Fiber axiom: l2r_fiber R aᵢ =ₛₑₜ Fᵢ
  have h₂: l2r_fiber R a₁ =ₛₑₜ F₁ := l2r_fiber_def R a₁
  have h₃: l2r_fiber R a₂ =ₛₑₜ F₂ := l2r_fiber_def R a₂
  -- Unfold fiber set equalities to predicate level via eq_def
  have h₄: ∀ (S₂: Set U₂), (l2r_fiber R a₁) =ₛₑₜ S₂ ↔ ∀ (z: U₂.Particular), (l2r_fiber R a₁).pred z ↔ S₂.pred z := by forall_elim eq_def, (l2r_fiber R a₁)
  have h₅: (l2r_fiber R a₁) =ₛₑₜ F₁ ↔ ∀ (z: U₂.Particular), (l2r_fiber R a₁).pred z ↔ F₁.pred z := by forall_elim h₄, F₁
  have h₆: ∀ (z: U₂.Particular), (l2r_fiber R a₁).pred z ↔ F₁.pred z := PC₀.deductive_eq_l2r h₅ h₂
  have h₇: ∀ (S₂: Set U₂), (l2r_fiber R a₂) =ₛₑₜ S₂ ↔ ∀ (z: U₂.Particular), (l2r_fiber R a₂).pred z ↔ S₂.pred z := by forall_elim eq_def, (l2r_fiber R a₂)
  have h₈: (l2r_fiber R a₂) =ₛₑₜ F₂ ↔ ∀ (z: U₂.Particular), (l2r_fiber R a₂).pred z ↔ F₂.pred z := by forall_elim h₇, F₂
  have h₉: ∀ (z: U₂.Particular), (l2r_fiber R a₂).pred z ↔ F₂.pred z := PC₀.deductive_eq_l2r h₈ h₃
  -- Goal via eq_def
  have h₁₀: (l2r_fiber R a₁) =ₛₑₜ (l2r_fiber R a₂) ↔ ∀ (z: U₂.Particular), (l2r_fiber R a₁).pred z ↔ (l2r_fiber R a₂).pred z := by forall_elim h₄, (l2r_fiber R a₂)
  have h₁₁: ∀ (z: U₂.Particular), (l2r_fiber R a₁).pred z ↔ (l2r_fiber R a₂).pred z := by forall_intro
    variable(z: U₂.Particular)
    have h₁₁₁: (l2r_fiber R a₁).pred z ↔ F₁.pred z := by forall_elim h₆, z
    have h₁₁₂: (l2r_fiber R a₂).pred z ↔ F₂.pred z := by forall_elim h₉, z
    -- From a₁ =₍U₁₎ a₂, derive R.pred (a₁ ⋈ z) ↔ R.pred (a₂ ⋈ z) via dyad congruence
    have h₁₁₃: z =₍U₂₎ z := U₂.eq.refl z
    have h₁₁₄: a₁ =₍U₁₎ a₂ ∧ z =₍U₂₎ z := by and_intro h₁, h₁₁₃
    have h₁₁₅: ∀ (b₁: U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂: U₂.Particular),
      (a₁ ⋈ b₁) =ₗₓₗ (a₂' ⋈ b₂) ↔ a₁ =₍U₁₎ a₂' ∧ b₁ =₍U₂₎ b₂ := by forall_elim Dyads.eq_def, a₁
    have h₁₁₆: ∀ (a₂': U₁.Particular), ∀ (b₂: U₂.Particular),
      (a₁ ⋈ z) =ₗₓₗ (a₂' ⋈ b₂) ↔ a₁ =₍U₁₎ a₂' ∧ z =₍U₂₎ b₂ := by forall_elim h₁₁₅, z
    have h₁₁₇: ∀ (b₂: U₂.Particular),
      (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ z =₍U₂₎ b₂ := by forall_elim h₁₁₆, a₂
    have h₁₁₈: (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ z) ↔ a₁ =₍U₁₎ a₂ ∧ z =₍U₂₎ z := by forall_elim h₁₁₇, z
    have h₁₁₉: (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ z) := PC₀.deductive_eq_r2l h₁₁₈ h₁₁₄
    have h₁₁₁₀: ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂), d₁ =ₗₓₗ d₂ → (R.pred d₁ ↔ R.pred d₂) := R.cong
    have h₁₁₁₁: ∀ (d₂: U₁ ⋈ U₂), (a₁ ⋈ z) =ₗₓₗ d₂ → (R.pred (a₁ ⋈ z) ↔ R.pred d₂) := by forall_elim h₁₁₁₀, (a₁ ⋈ z)
    have h₁₁₁₂: (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ z) → (R.pred (a₁ ⋈ z) ↔ R.pred (a₂ ⋈ z)) := by forall_elim h₁₁₁₁, (a₂ ⋈ z)
    have h₁₁₁₃: R.pred (a₁ ⋈ z) ↔ R.pred (a₂ ⋈ z) := by modus_ponens h₁₁₁₂, h₁₁₉
    -- Chain: fiber₁.pred z → R.pred(a₁⋈z) → R.pred(a₂⋈z) → fiber₂.pred z
    have h₁₁₁₄: (l2r_fiber R a₁).pred z → (l2r_fiber R a₂).pred z := by
      assume(h₁₁₁₄₁: (l2r_fiber R a₁).pred z)
      have h₁₁₁₄₂: R.pred (a₁ ⋈ z) := PC₀.deductive_eq_l2r h₁₁₁ h₁₁₁₄₁
      have h₁₁₁₄₃: R.pred (a₂ ⋈ z) := PC₀.deductive_eq_l2r h₁₁₁₃ h₁₁₁₄₂
      have h₁₁₁₄₄: (l2r_fiber R a₂).pred z := PC₀.deductive_eq_r2l h₁₁₂ h₁₁₁₄₃
      iterate h₁₁₁₄₄
    have h₁₁₁₅: (l2r_fiber R a₂).pred z → (l2r_fiber R a₁).pred z := by
      assume(h₁₁₁₅₁: (l2r_fiber R a₂).pred z)
      have h₁₁₁₅₂: R.pred (a₂ ⋈ z) := PC₀.deductive_eq_l2r h₁₁₂ h₁₁₁₅₁
      have h₁₁₁₅₃: R.pred (a₁ ⋈ z) := PC₀.deductive_eq_r2l h₁₁₁₃ h₁₁₁₅₂
      have h₁₁₁₅₄: (l2r_fiber R a₁).pred z := PC₀.deductive_eq_r2l h₁₁₁ h₁₁₁₅₃
      iterate h₁₁₁₅₄
    have h₁₁₁₆: (l2r_fiber R a₁).pred z ↔ (l2r_fiber R a₂).pred z := by iff_intro h₁₁₁₄, h₁₁₁₅
    iterate h₁₁₁₆
  have h₁₂: l2r_fiber R a₁ =ₛₑₜ l2r_fiber R a₂ := PC₀.deductive_eq_r2l h₁₀ h₁₁
  iterate h₁₂

-- # l2r_fiber R as a CongruentUnaryOperation (for fixed R)
noncomputable def l2r_fiber_unary_operation (R: Rel U₁ U₂): CongruentUnaryOperation U₁ (𝐒𝐞𝐭 U₂) := {
  op := l2r_fiber R,
  cong := l2r_fiber_cong_arg R
}

-- # l2r_fiber as a CongruentBinaryOperation
noncomputable def l2r_fiber_operation: CongruentBinaryOperation (𝐑𝐞𝐥 U₁ U₂) U₁ (𝐒𝐞𝐭 U₂) := {
  op := l2r_fiber_unary_operation,
  cong := l2r_fiber_cong_rel
}

end Relations

end Universe
