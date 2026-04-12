import Universals.Relations.Universal
import Universals.Sets.Definitions.SetsAsUniversals.Definition
import Universals.Dyads

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads

axiom right_restrict: Rel U1 U2 → (S: Set U2) → Rel U1 (S: Universal)

axiom right_restrict_def {U: Universal}: ∀ (R: Rel U1 U2), ∀ (S: Set U2),
  ∀ (u₁: U1.Particular), ∀ (u₂: S.Particular),
  (right_restrict R S).pred (u₁ ⋈ u₂) ↔ R.pred (u₁ ⋈ ↑u₂)

-- axiom right_restrict_def2 {U: Universal}: ∀ (R: Rel U1 U2), ∀ (S: Set U2),
--  right_restrict R S =ₛₑₜ {x: U1 ⋈ S | R.pred (x.fst ⋈ ↑x.snd)} with sorry

--theorem right_restrict_cong_set2: ∀ (R: Rel U1 U2), ∀ (S₁: Set U2), ∀ (S₂: Set U2),
--  ∀ (u₁: U1.Particular), ∀ (S1: Set U2), ∀ (S2: Set U2),
--  S1 =ₛₑₜ S2 → right_restrict R S1 =ᵣₑₗ right_restrict R S2 := sorry

-- # Congruence in S (for fixed R)
-- When the underlying U2-elements are equal, the restricted predicates agree.
-- This is the pointwise form of congruence: since right_restrict R S₁ and
-- right_restrict R S₂ live in different Rel types (dependent on S), we cannot
-- state =ᵣₑₗ directly — instead we compare at the parent universal level.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-05
theorem right_restrict_cong_set: ∀ (R: Rel U1 U2), ∀ (S₁: Set U2), ∀ (S₂: Set U2),
  ∀ (u₁: U1.Particular), ∀ (v₁: S₁.Particular), ∀ (v₂: S₂.Particular),
  ↑v₁ =₍U2₎ ↑v₂ →
    ((right_restrict R S₁).pred (u₁ ⋈ v₁) ↔ (right_restrict R S₂).pred (u₁ ⋈ v₂)) := by forall_intro
  variable(R: Rel U1 U2)
  variable(S₁: Set U2)
  variable(S₂: Set U2)
  variable(u₁: U1.Particular)
  variable(v₁: S₁.Particular)
  variable(v₂: S₂.Particular)
  assume(h₁: ↑v₁ =₍U2₎ ↑v₂)
  -- Unfold right_restrict_def for both sides
  have h₂: ∀ (S: Set U2), ∀ (u: U1.Particular), ∀ (v: S.Particular),
    (right_restrict R S).pred (u ⋈ v) ↔ R.pred (u ⋈ ↑v) := by forall_elim (right_restrict_def (U := U2)), R
  have h₃: ∀ (u: U1.Particular), ∀ (v: S₁.Particular),
    (right_restrict R S₁).pred (u ⋈ v) ↔ R.pred (u ⋈ ↑v) := by forall_elim h₂, S₁
  have h₄: ∀ (v: S₁.Particular),
    (right_restrict R S₁).pred (u₁ ⋈ v) ↔ R.pred (u₁ ⋈ ↑v) := by forall_elim h₃, u₁
  have h₅: (right_restrict R S₁).pred (u₁ ⋈ v₁) ↔ R.pred (u₁ ⋈ ↑v₁) := by forall_elim h₄, v₁
  have h₆: ∀ (u: U1.Particular), ∀ (v: S₂.Particular),
    (right_restrict R S₂).pred (u ⋈ v) ↔ R.pred (u ⋈ ↑v) := by forall_elim h₂, S₂
  have h₇: ∀ (v: S₂.Particular),
    (right_restrict R S₂).pred (u₁ ⋈ v) ↔ R.pred (u₁ ⋈ ↑v) := by forall_elim h₆, u₁
  have h₈: (right_restrict R S₂).pred (u₁ ⋈ v₂) ↔ R.pred (u₁ ⋈ ↑v₂) := by forall_elim h₇, v₂
  -- Build dyad equality (u₁ ⋈ v₁.val) =ₗₓₗ (u₁ ⋈ v₂.val) via Dyads.eq_def
  have h₉: u₁ =₍U1₎ u₁ := U1.eq.refl u₁
  have h₁₀: u₁ =₍U1₎ u₁ ∧ ↑v₁ =₍U2₎ ↑v₂ := by and_intro h₉, h₁
  have h₁₁: ∀ (b₁: U2.Particular), ∀ (a₂: U1.Particular), ∀ (b₂: U2.Particular),
    (u₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ u₁ =₍U1₎ a₂ ∧ b₁ =₍U2₎ b₂ := by forall_elim Dyads.eq_def, u₁
  have h₁₂: ∀ (a₂: U1.Particular), ∀ (b₂: U2.Particular),
    (u₁ ⋈ v₁.val) =ₗₓₗ (a₂ ⋈ b₂) ↔ u₁ =₍U1₎ a₂ ∧ v₁.val =₍U2₎ b₂ := by forall_elim h₁₁, v₁.val
  have h₁₃: ∀ (b₂: U2.Particular),
    (u₁ ⋈ v₁.val) =ₗₓₗ (u₁ ⋈ b₂) ↔ u₁ =₍U1₎ u₁ ∧ v₁.val =₍U2₎ b₂ := by forall_elim h₁₂, u₁
  have h₁₄: (u₁ ⋈ v₁.val) =ₗₓₗ (u₁ ⋈ v₂.val) ↔ u₁ =₍U1₎ u₁ ∧ v₁.val =₍U2₎ v₂.val := by forall_elim h₁₃, v₂.val
  have h₁₅: (u₁ ⋈ v₁.val) =ₗₓₗ (u₁ ⋈ v₂.val) := PC₀.deductive_eq_r2l h₁₄ h₁₀
  -- Apply R.cong to get R.pred (u₁ ⋈ v₁.val) ↔ R.pred (u₁ ⋈ v₂.val)
  have h₁₆: ∀ (d₁: U1 ⋈ U2), ∀ (d₂: U1 ⋈ U2), d₁ =ₗₓₗ d₂ → (R.pred d₁ ↔ R.pred d₂) := R.cong
  have h₁₇: ∀ (d₂: U1 ⋈ U2), (u₁ ⋈ v₁.val) =ₗₓₗ d₂ → (R.pred (u₁ ⋈ v₁.val) ↔ R.pred d₂) := by forall_elim h₁₆, (u₁ ⋈ v₁.val)
  have h₁₈: (u₁ ⋈ v₁.val) =ₗₓₗ (u₁ ⋈ v₂.val) → (R.pred (u₁ ⋈ v₁.val) ↔ R.pred (u₁ ⋈ v₂.val)) := by forall_elim h₁₇, (u₁ ⋈ v₂.val)
  have h₁₉: R.pred (u₁ ⋈ v₁.val) ↔ R.pred (u₁ ⋈ v₂.val) := by modus_ponens h₁₈, h₁₅
  -- Chain: restrict₁ ↔ R.pred(u₁ ⋈ ↑v₁) ↔ R.pred(u₁ ⋈ ↑v₂) ↔ restrict₂
  have h₂₀: (right_restrict R S₁).pred (u₁ ⋈ v₁) → (right_restrict R S₂).pred (u₁ ⋈ v₂) := by
    assume(h₂₀₁: (right_restrict R S₁).pred (u₁ ⋈ v₁))
    have h₂₀₂: R.pred (u₁ ⋈ ↑v₁) := PC₀.deductive_eq_l2r h₅ h₂₀₁
    have h₂₀₃: R.pred (u₁ ⋈ ↑v₂) := PC₀.deductive_eq_l2r h₁₉ h₂₀₂
    have h₂₀₄: (right_restrict R S₂).pred (u₁ ⋈ v₂) := PC₀.deductive_eq_r2l h₈ h₂₀₃
    iterate h₂₀₄
  have h₂₁: (right_restrict R S₂).pred (u₁ ⋈ v₂) → (right_restrict R S₁).pred (u₁ ⋈ v₁) := by
    assume(h₂₁₁: (right_restrict R S₂).pred (u₁ ⋈ v₂))
    have h₂₁₂: R.pred (u₁ ⋈ ↑v₂) := PC₀.deductive_eq_l2r h₈ h₂₁₁
    have h₂₁₃: R.pred (u₁ ⋈ ↑v₁) := PC₀.deductive_eq_r2l h₁₉ h₂₁₂
    have h₂₁₄: (right_restrict R S₁).pred (u₁ ⋈ v₁) := PC₀.deductive_eq_r2l h₅ h₂₁₃
    iterate h₂₁₄
  have h₂₂: (right_restrict R S₁).pred (u₁ ⋈ v₁) ↔ (right_restrict R S₂).pred (u₁ ⋈ v₂) := by iff_intro h₂₀, h₂₁
  iterate h₂₂

end Relations

end Universe
