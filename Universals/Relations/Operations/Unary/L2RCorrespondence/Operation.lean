import Universals.Relations.Universal
import Universals.Correspondences
import Universals.Sets
import Universals.Relations.Operations.Unary.L2RFiber.Operation

/-!
# Left-to-Right Correspondence

The induction from a relation to a correspondence. Given a relation
R: Rel U₁ U₂ (a set of dyads), produces the correspondence whose arrows
pair each individual a with its fiber set {b | a ⋈ b ∈ R}.

This is the bridge from the undirected world (relations/dyads) to the
directed world (correspondences/arrows).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Arrows
open Correspondences

-- # l2r_correspondence: Relation → Correspondence
axiom l2r_correspondence: Rel U₁ U₂ → U₁ ⭢ᶜ U₂
postfix:max "→" => l2r_correspondence

-- # Axiom definition
-- An arrow a ⭢ S belongs to the correspondence iff S is the fiber of R at a:
-- S contains exactly those b for which the dyad a ⋈ b belongs to R.
axiom l2r_correspondence_def: ∀ (R: Rel U₁ U₂), ∀ (a: U₁.Particular), ∀ (S: Set U₂),
  (a ⭢ᵃ S) ∈ₛₑₜ R→ ↔ (S =ₛₑₜ l2r_fiber R a)

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem l2r_correspondence_cong: ∀ (R₁: Rel U₁ U₂), ∀ (R₂: Rel U₁ U₂),
  (R₁ =ᵣₑₗ R₂) → (R₁→ =→ᶜ R₂→) := by forall_intro
  variable(R₁: Rel U₁ U₂)
  variable(R₂: Rel U₁ U₂)
  assume(h₁: R₁ =ᵣₑₗ R₂)
  -- Fiber congruence: equal relations have equal fibers
  have h₂: ∀ (a: U₁.Particular), (l2r_fiber R₁ a) =ₛₑₜ (l2r_fiber R₂ a) := by forall_intro
    variable(a: U₁.Particular)
    have h₂₁ := l2r_fiber_cong_rel R₁ R₂ a
    have h₂₂: (l2r_fiber R₁ a) =ₛₑₜ (l2r_fiber R₂ a) := by modus_ponens h₂₁, h₁
    iterate h₂₂
  -- Correspondence equality via eq_def: ∀ arr, C₁.pred arr ↔ C₂.pred arr
  have h₃: ∀ (S₂: U₁ ⭢ᶜ U₂), (R₁→) =ₛₑₜ S₂ ↔ ∀ (arr: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (R₁→).pred arr ↔ S₂.pred arr := by forall_elim eq_def, (R₁→)
  have h₄: (R₁→) =ₛₑₜ (R₂→) ↔ ∀ (arr: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (R₁→).pred arr ↔ (R₂→).pred arr := by forall_elim h₃, (R₂→)
  have h₅: ∀ (arr: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (R₁→).pred arr ↔ (R₂→).pred arr := by forall_intro
    variable(arr: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular)
    -- Arrow exhaustiveness: arr = a ⭢ᵃ S
    have h₅₁: ∃ (a: U₁.Particular), ∃ (S: (𝐒𝐞𝐭 U₂).Particular), arr 🟰 (a ⭢ᵃ S) := by forall_elim Arrows.exhaustiveness, arr
    have ⟨(a: U₁.Particular), (h₅₂: ∃ (S: (𝐒𝐞𝐭 U₂).Particular), arr 🟰 (a ⭢ᵃ S))⟩ := exists_elim h₅₁
    have ⟨(S: (𝐒𝐞𝐭 U₂).Particular), (h₅₃: arr 🟰 (a ⭢ᵃ S))⟩ := exists_elim h₅₂
    -- Leibniz: transfer C₁.pred arr ↔ C₁.pred (a ⭢ᵃ S)
    let p₁: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular → Prop := (x: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular ↦ (R₁→).pred x)
    have h₅₄: ∀ (x: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), ∀ (y: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (x 🟰 y) → (p₁ x ↔ p₁ y) := by forall_elim leibniz_eq_subs, p₁
    have h₅₅: ∀ (y: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (arr 🟰 y) → (p₁ arr ↔ p₁ y) := by forall_elim h₅₄, arr
    have h₅₆: (arr 🟰 (a ⭢ᵃ S)) → ((R₁→).pred arr ↔ (R₁→).pred (a ⭢ᵃ S)) := by forall_elim h₅₅, (a ⭢ᵃ S)
    have h₅₇: (R₁→).pred arr ↔ (R₁→).pred (a ⭢ᵃ S) := by modus_ponens h₅₆, h₅₃
    -- Leibniz: transfer C₂.pred arr ↔ C₂.pred (a ⭢ᵃ S)
    let p₂: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular → Prop := (x: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular ↦ (R₂→).pred x)
    have h₅₈: ∀ (x: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), ∀ (y: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (x 🟰 y) → (p₂ x ↔ p₂ y) := by forall_elim leibniz_eq_subs, p₂
    have h₅₉: ∀ (y: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), (arr 🟰 y) → (p₂ arr ↔ p₂ y) := by forall_elim h₅₈, arr
    have h₅₁₀: (arr 🟰 (a ⭢ᵃ S)) → ((R₂→).pred arr ↔ (R₂→).pred (a ⭢ᵃ S)) := by forall_elim h₅₉, (a ⭢ᵃ S)
    have h₅₁₁: (R₂→).pred arr ↔ (R₂→).pred (a ⭢ᵃ S) := by modus_ponens h₅₁₀, h₅₃
    -- l2r_correspondence_def at constructor form
    have h₅₁₂: ∀ (a': U₁.Particular), ∀ (S': Set U₂), (a' ⭢ᵃ S') ∈ₛₑₜ (R₁→) ↔ (S' =ₛₑₜ l2r_fiber R₁ a') := by forall_elim l2r_correspondence_def, R₁
    have h₅₁₃: ∀ (S': Set U₂), (a ⭢ᵃ S') ∈ₛₑₜ (R₁→) ↔ (S' =ₛₑₜ l2r_fiber R₁ a) := by forall_elim h₅₁₂, a
    have h₅₁₄: (a ⭢ᵃ S) ∈ₛₑₜ (R₁→) ↔ (S =ₛₑₜ l2r_fiber R₁ a) := by forall_elim h₅₁₃, S
    have h₅₁₅: ∀ (a': U₁.Particular), ∀ (S': Set U₂), (a' ⭢ᵃ S') ∈ₛₑₜ (R₂→) ↔ (S' =ₛₑₜ l2r_fiber R₂ a') := by forall_elim l2r_correspondence_def, R₂
    have h₅₁₆: ∀ (S': Set U₂), (a ⭢ᵃ S') ∈ₛₑₜ (R₂→) ↔ (S' =ₛₑₜ l2r_fiber R₂ a) := by forall_elim h₅₁₅, a
    have h₅₁₇: (a ⭢ᵃ S) ∈ₛₑₜ (R₂→) ↔ (S =ₛₑₜ l2r_fiber R₂ a) := by forall_elim h₅₁₆, S
    -- mem_def: ∈ₛₑₜ ↔ .pred
    have h₅₁₈: ∀ (x: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), x ∈ₛₑₜ (R₁→) ↔ (R₁→).pred x := by forall_elim mem_def, (R₁→)
    have h₅₁₉: (a ⭢ᵃ S) ∈ₛₑₜ (R₁→) ↔ (R₁→).pred (a ⭢ᵃ S) := by forall_elim h₅₁₈, (a ⭢ᵃ S)
    have h₅₂₀: ∀ (x: (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂)).Particular), x ∈ₛₑₜ (R₂→) ↔ (R₂→).pred x := by forall_elim mem_def, (R₂→)
    have h₅₂₁: (a ⭢ᵃ S) ∈ₛₑₜ (R₂→) ↔ (R₂→).pred (a ⭢ᵃ S) := by forall_elim h₅₂₀, (a ⭢ᵃ S)
    -- Fiber equality for a
    have h₅₂₂: (l2r_fiber R₁ a) =ₛₑₜ (l2r_fiber R₂ a) := by forall_elim h₂, a
    -- Forward: (R₁→).pred arr → (R₂→).pred arr
    have h₅₂₃: ((R₁→).pred arr) → ((R₂→).pred arr) := by
      assume(h: (R₁→).pred arr)
      have h_a: (R₁→).pred (a ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₇ h
      have h_b: (a ⭢ᵃ S) ∈ₛₑₜ (R₁→) := PC₀.deductive_eq_r2l h₅₁₉ h_a
      have h_c: S =ₛₑₜ l2r_fiber R₁ a := PC₀.deductive_eq_l2r h₅₁₄ h_b
      have h_d: (S =ₛₑₜ l2r_fiber R₁ a) ∧ ((l2r_fiber R₁ a) =ₛₑₜ (l2r_fiber R₂ a)) := by and_intro h_c, h₅₂₂
      have h_e: S =ₛₑₜ l2r_fiber R₂ a := (𝐒𝐞𝐭 U₂).eq.trans S (l2r_fiber R₁ a) (l2r_fiber R₂ a) h_d
      have h_f: (a ⭢ᵃ S) ∈ₛₑₜ (R₂→) := PC₀.deductive_eq_r2l h₅₁₇ h_e
      have h_g: (R₂→).pred (a ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₂₁ h_f
      have h_h: (R₂→).pred arr := PC₀.deductive_eq_r2l h₅₁₁ h_g
      iterate h_h
    -- Backward: (R₂→).pred arr → (R₁→).pred arr
    have h₅₂₄: ((R₂→).pred arr) → ((R₁→).pred arr) := by
      assume(h: (R₂→).pred arr)
      have h_a: (R₂→).pred (a ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₁₁ h
      have h_b: (a ⭢ᵃ S) ∈ₛₑₜ (R₂→) := PC₀.deductive_eq_r2l h₅₂₁ h_a
      have h_c: S =ₛₑₜ l2r_fiber R₂ a := PC₀.deductive_eq_l2r h₅₁₇ h_b
      have h_d: (l2r_fiber R₂ a) =ₛₑₜ (l2r_fiber R₁ a) := (𝐒𝐞𝐭 U₂).eq.sym (l2r_fiber R₁ a) (l2r_fiber R₂ a) h₅₂₂
      have h_e: (S =ₛₑₜ l2r_fiber R₂ a) ∧ ((l2r_fiber R₂ a) =ₛₑₜ (l2r_fiber R₁ a)) := by and_intro h_c, h_d
      have h_f: S =ₛₑₜ l2r_fiber R₁ a := (𝐒𝐞𝐭 U₂).eq.trans S (l2r_fiber R₂ a) (l2r_fiber R₁ a) h_e
      have h_g: (a ⭢ᵃ S) ∈ₛₑₜ (R₁→) := PC₀.deductive_eq_r2l h₅₁₄ h_f
      have h_h: (R₁→).pred (a ⭢ᵃ S) := PC₀.deductive_eq_l2r h₅₁₉ h_g
      have h_i: (R₁→).pred arr := PC₀.deductive_eq_r2l h₅₇ h_h
      iterate h_i
    have h₅₂₅: (R₁→).pred arr ↔ (R₂→).pred arr := by iff_intro h₅₂₃, h₅₂₄
    iterate h₅₂₅
  have h₆: R₁→ =→ᶜ R₂→ := PC₀.deductive_eq_r2l h₄ h₅
  iterate h₆

-- # l2r_correspondence as a CongruentUnaryOperation
noncomputable def l2r_correspondence_operation: CongruentUnaryOperation (𝐑𝐞𝐥 U₁ U₂) (U₁ ➞ᶜ U₂) := {
  op := l2r_correspondence,
  cong := l2r_correspondence_cong
}

end Relations

end Universe
