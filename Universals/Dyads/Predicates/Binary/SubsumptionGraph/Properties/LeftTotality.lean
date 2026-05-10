import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsume graph — left-totality

-- Proof by Claude Opus 4.7 Max, 2026-05-03
theorem subsume_left_totality {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    ∀ (d': U₁' ⋈ U₂'), ∃ (d: U₁ ⋈ U₂), ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by forall_intro
  variable(d': U₁' ⋈ U₂')
  -- Decompose d' via exhaustiveness
  have h₁: ∃ (a: U₁'.Particular), ∃ (b: U₂'.Particular), d' 🟰 (a ⋈ b) := by forall_elim exhaustiveness, d'
  have ⟨(a: U₁'.Particular), (h₂: ∃ (b: U₂'.Particular), d' 🟰 (a ⋈ b))⟩ := exists_elim h₁
  have ⟨(b: U₂'.Particular), (h₃: d' 🟰 (a ⋈ b))⟩ := exists_elim h₂
  -- Transfer d' 🟰 (a ⋈ b) to d' =ₗₓₗ (a ⋈ b) via Leibniz
  let pred₁: U₁' ⋈ U₂' → Prop := (x: U₁' ⋈ U₂' ↦ d' =ₗₓₗ x)
  have h₄: d' 🟰 (a ⋈ b) → (pred₁ d' ↔ pred₁ (a ⋈ b)) := by forall_elim leibniz_eq_subs, pred₁, d', (a ⋈ b)
  have h₅: pred₁ d' ↔ pred₁ (a ⋈ b) := by modus_ponens h₄, h₃
  have h₆: d' =ₗₓₗ d' := by forall_elim eq_refl, d'
  have h₇: d' =ₗₓₗ (a ⋈ b) := PC₀.deductive_eq_l2r h₅ h₆
  -- Image side — refl
  have h₈: (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by forall_elim eq_refl, (e₁.embedding a ⋈ e₂.embedding b)
  have h₉: d' =ₗₓₗ (a ⋈ b) ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by and_intro h₇, h₈
  have h₁₀: ∃ (b': U₂'.Particular), d' =ₗₓₗ (a ⋈ b') ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b') := by exists_intro h₉, b
  have h₁₁: ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by exists_intro h₁₀, a
  have h₁₂: ∃ (d: U₁ ⋈ U₂), ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by exists_intro h₁₁, (e₁.embedding a ⋈ e₂.embedding b)
  iterate h₁₂

end Dyads
end Universe
