import Universals.Relations.Universal
import Universals.Correspondences
import Universals.Sets
import Universals.Relations.Operations.Unary.R2LFiber.Operation

/-!
# Right-to-Left Correspondence

The dual of l2r_correspondence. Given a relation R: Rel U₁ U₂ (a set of
dyads), produces the correspondence whose arrows pair each individual b of
U₂ with its fiber set {a | a ⋈ b ∈ R}.
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Arrows
open Correspondences

-- # r2l_correspondence: Relation → Correspondence (reversed)
axiom r2l_correspondence: Rel U₁ U₂ → Corr U₂ U₁
postfix:max "←" => r2l_correspondence

-- # Axiom definition
-- An arrow b ⭢ S belongs to the correspondence iff S is the fiber of R at b:
-- S contains exactly those a for which the dyad a ⋈ b belongs to R.
axiom r2l_correspondence_def: ∀ (R: Rel U₁ U₂), ∀ (b: U₂.Particular), ∀ (S: Set U₁),
  (b ⭢ᵃ S) ∈ₛₑₜ R← ↔ (S =ₛₑₜ r2l_fiber R b)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem r2l_correspondence_cong: ∀ (R₁: Rel U₁ U₂), ∀ (R₂: Rel U₁ U₂),
  (R₁ =ᵣₑₗ R₂) → (R₁← =→ᶜ R₂←) := by forall_intro
  variable(R₁: Rel U₁ U₂)
  variable(R₂: Rel U₁ U₂)
  assume(h₁: R₁ =ᵣₑₗ R₂)
  -- Fiber congruence: equal relations have equal fibers
  have h₂: ∀ (b: U₂.Particular), (r2l_fiber R₁ b) =ₛₑₜ (r2l_fiber R₂ b) := by forall_intro
    variable(b: U₂.Particular)
    have h₂₁ := r2l_fiber_cong_rel R₁ R₂ b
    have h₂₂: (r2l_fiber R₁ b) =ₛₑₜ (r2l_fiber R₂ b) := by modus_ponens h₂₁, h₁
    iterate h₂₂
  -- Correspondence equality via eq_def: ∀ arr, C₁.pred arr ↔ C₂.pred arr
  have h₃: ∀ (S₂: Corr U₂ U₁), (R₁←) =ₛₑₜ S₂ ↔ ∀ (arr: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (R₁←).pred arr ↔ S₂.pred arr := by forall_elim eq_def, (R₁←)
  have h₄: (R₁←) =ₛₑₜ (R₂←) ↔ ∀ (arr: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (R₁←).pred arr ↔ (R₂←).pred arr := by forall_elim h₃, (R₂←)
  have h₅: ∀ (arr: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (R₁←).pred arr ↔ (R₂←).pred arr := by forall_intro
    variable(arr: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular)
    -- Arrow exhaustiveness: arr = b ⭢ᵃ S
    have h₅₁: ∃ (b: U₂.Particular), ∃ (S: (𝐒𝐞𝐭 U₁).Particular), arr 🟰 (b ⭢ᵃ S) := by forall_elim Arrows.exhaustiveness, arr
    have ⟨(b: U₂.Particular), (h₅₂: ∃ (S: (𝐒𝐞𝐭 U₁).Particular), arr 🟰 (b ⭢ᵃ S))⟩ := exists_elim h₅₁
    have ⟨(S: (𝐒𝐞𝐭 U₁).Particular), (h₅₃: arr 🟰 (b ⭢ᵃ S))⟩ := exists_elim h₅₂
    -- Leibniz: transfer C₁.pred arr ↔ C₁.pred (b ⭢ᵃ S)
    let p₁: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular → Prop := (x: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular ↦ (R₁←).pred x)
    have h₅₄: ∀ (x: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), ∀ (y: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (x 🟰 y) → (p₁ x ↔ p₁ y) := by forall_elim leibniz_eq_subs, p₁
    have h₅₅: ∀ (y: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (arr 🟰 y) → (p₁ arr ↔ p₁ y) := by forall_elim h₅₄, arr
    have h₅₆: (arr 🟰 (b ⭢ᵃ S)) → ((R₁←).pred arr ↔ (R₁←).pred (b ⭢ᵃ S)) := by forall_elim h₅₅, (b ⭢ᵃ S)
    have h₅₇: (R₁←).pred arr ↔ (R₁←).pred (b ⭢ᵃ S) := by modus_ponens h₅₆, h₅₃
    -- Leibniz: transfer C₂.pred arr ↔ C₂.pred (b ⭢ᵃ S)
    let p₂: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular → Prop := (x: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular ↦ (R₂←).pred x)
    have h₅₈: ∀ (x: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), ∀ (y: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (x 🟰 y) → (p₂ x ↔ p₂ y) := by forall_elim leibniz_eq_subs, p₂
    have h₅₉: ∀ (y: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), (arr 🟰 y) → (p₂ arr ↔ p₂ y) := by forall_elim h₅₈, arr
    have h₅₁₀: (arr 🟰 (b ⭢ᵃ S)) → ((R₂←).pred arr ↔ (R₂←).pred (b ⭢ᵃ S)) := by forall_elim h₅₉, (b ⭢ᵃ S)
    have h₅₁₁: (R₂←).pred arr ↔ (R₂←).pred (b ⭢ᵃ S) := by modus_ponens h₅₁₀, h₅₃
    -- r2l_correspondence_def at constructor form
    have h₅₁₂: ∀ (b': U₂.Particular), ∀ (S': Set U₁), (b' ⭢ᵃ S') ∈ₛₑₜ (R₁←) ↔ (S' =ₛₑₜ r2l_fiber R₁ b') := by forall_elim r2l_correspondence_def, R₁
    have h₅₁₃: ∀ (S': Set U₁), (b ⭢ᵃ S') ∈ₛₑₜ (R₁←) ↔ (S' =ₛₑₜ r2l_fiber R₁ b) := by forall_elim h₅₁₂, b
    have h₅₁₄: (b ⭢ᵃ S) ∈ₛₑₜ (R₁←) ↔ (S =ₛₑₜ r2l_fiber R₁ b) := by forall_elim h₅₁₃, S
    have h₅₁₅: ∀ (b': U₂.Particular), ∀ (S': Set U₁), (b' ⭢ᵃ S') ∈ₛₑₜ (R₂←) ↔ (S' =ₛₑₜ r2l_fiber R₂ b') := by forall_elim r2l_correspondence_def, R₂
    have h₅₁₆: ∀ (S': Set U₁), (b ⭢ᵃ S') ∈ₛₑₜ (R₂←) ↔ (S' =ₛₑₜ r2l_fiber R₂ b) := by forall_elim h₅₁₅, b
    have h₅₁₇: (b ⭢ᵃ S) ∈ₛₑₜ (R₂←) ↔ (S =ₛₑₜ r2l_fiber R₂ b) := by forall_elim h₅₁₆, S
    -- mem_def: ∈ₛₑₜ ↔ .pred
    have h₅₁₈: ∀ (x: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), x ∈ₛₑₜ (R₁←) ↔ (R₁←).pred x := by forall_elim mem_def, (R₁←)
    have h₅₁₉: (b ⭢ᵃ S) ∈ₛₑₜ (R₁←) ↔ (R₁←).pred (b ⭢ᵃ S) := by forall_elim h₅₁₈, (b ⭢ᵃ S)
    have h₅₂₀: ∀ (x: (U₂ ➞ᵃ (𝐒𝐞𝐭 U₁)).Particular), x ∈ₛₑₜ (R₂←) ↔ (R₂←).pred x := by forall_elim mem_def, (R₂←)
    have h₅₂₁: (b ⭢ᵃ S) ∈ₛₑₜ (R₂←) ↔ (R₂←).pred (b ⭢ᵃ S) := by forall_elim h₅₂₀, (b ⭢ᵃ S)
    -- Fiber equality for b
    have h₅₂₂: (r2l_fiber R₁ b) =ₛₑₜ (r2l_fiber R₂ b) := by forall_elim h₂, b
    -- Forward: (R₁←).pred arr → (R₂←).pred arr
    have h₅₂₃: ((R₁←).pred arr) → ((R₂←).pred arr) := by
      assume(h: (R₁←).pred arr)
      have h_a: (R₁←).pred (b ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₇ h
      have h_b: (b ⭢ᵃ S) ∈ₛₑₜ (R₁←) := PC₀.deductive_eq_r2l h₅₁₉ h_a
      have h_c: S =ₛₑₜ r2l_fiber R₁ b := PC₀.deductive_eq_l2r h₅₁₄ h_b
      have h_d: (S =ₛₑₜ r2l_fiber R₁ b) ∧ ((r2l_fiber R₁ b) =ₛₑₜ (r2l_fiber R₂ b)) := by and_intro h_c, h₅₂₂
      have h_e: S =ₛₑₜ r2l_fiber R₂ b := (𝐒𝐞𝐭 U₁).eq.trans S (r2l_fiber R₁ b) (r2l_fiber R₂ b) h_d
      have h_f: (b ⭢ᵃ S) ∈ₛₑₜ (R₂←) := PC₀.deductive_eq_r2l h₅₁₇ h_e
      have h_g: (R₂←).pred (b ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₂₁ h_f
      have h_h: (R₂←).pred arr := PC₀.deductive_eq_r2l h₅₁₁ h_g
      iterate h_h
    -- Backward: (R₂←).pred arr → (R₁←).pred arr
    have h₅₂₄: ((R₂←).pred arr) → ((R₁←).pred arr) := by
      assume(h: (R₂←).pred arr)
      have h_a: (R₂←).pred (b ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₁₁ h
      have h_b: (b ⭢ᵃ S) ∈ₛₑₜ (R₂←) := PC₀.deductive_eq_r2l h₅₂₁ h_a
      have h_c: S =ₛₑₜ r2l_fiber R₂ b := PC₀.deductive_eq_l2r h₅₁₇ h_b
      have h_d: (r2l_fiber R₂ b) =ₛₑₜ (r2l_fiber R₁ b) := (𝐒𝐞𝐭 U₁).eq.sym (r2l_fiber R₁ b) (r2l_fiber R₂ b) h₅₂₂
      have h_e: (S =ₛₑₜ r2l_fiber R₂ b) ∧ ((r2l_fiber R₂ b) =ₛₑₜ (r2l_fiber R₁ b)) := by and_intro h_c, h_d
      have h_f: S =ₛₑₜ r2l_fiber R₁ b := (𝐒𝐞𝐭 U₁).eq.trans S (r2l_fiber R₂ b) (r2l_fiber R₁ b) h_e
      have h_g: (b ⭢ᵃ S) ∈ₛₑₜ (R₁←) := PC₀.deductive_eq_r2l h₅₁₄ h_f
      have h_h: (R₁←).pred (b ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₁₉ h_g
      have h_i: (R₁←).pred arr := PC₀.deductive_eq_r2l h₅₇ h_h
      iterate h_i
    have h₅₂₅: (R₁←).pred arr ↔ (R₂←).pred arr := by iff_intro h₅₂₃, h₅₂₄
    iterate h₅₂₅
  have h₆: R₁← =→ᶜ R₂← := PC₀.deductive_eq_r2l h₄ h₅
  iterate h₆

-- # r2l_correspondence as a CongruentUnaryOperation
noncomputable def r2l_correspondence_operation: CongruentUnaryOperation (𝐑𝐞𝐥 U₁ U₂) (U₂ ➞ᶜ U₁) := {
  op := r2l_correspondence,
  cong := r2l_correspondence_cong
}

end Relations

end Universe
