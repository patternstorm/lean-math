import Universe
import Logic
import Universals.Dyads.Operations.Unary.Subsume.Operation

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Equation of subsume on dyad constructor
-- From subsume_def + reflexivity of the extension at the matching witnesses:
--   subsume e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b).
-- The extension graph holds because (a ⋈ b) =ₗₓₗ (a ⋈ b) (refl) and
-- (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) (refl), so a = a, b = b witness the ∃.

-- Proof by Claude Opus 4.7, 2026-04-19
theorem subsume_dyad {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): ∀ (a: U₁'.Particular), ∀ (b: U₂'.Particular), subsume e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by forall_intro
  variable(a: U₁'.Particular)
  variable(b: U₂'.Particular)
  -- Witness the extension graph at (a ⋈ b) for the image (e₁ a ⋈ e₂ b)
  have h₁: (a ⋈ b) =ₗₓₗ (a ⋈ b) := by forall_elim eq_refl, (a ⋈ b)
  have h₂: (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by forall_elim eq_refl, (e₁.embedding a ⋈ e₂.embedding b)
  have h₃: (a ⋈ b) =ₗₓₗ (a ⋈ b) ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := by and_intro h₁, h₂
  have h₄: ∃ (b': U₂'.Particular), (a ⋈ b) =ₗₓₗ (a ⋈ b') ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b') := by exists_intro h₃, b
  have h₅: ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), (a ⋈ b) =ₗₓₗ (a' ⋈ b') ∧ (e₁.embedding a ⋈ e₂.embedding b) =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by exists_intro h₄, a
  -- h₅ is ((subsume_ext e₁ e₂).pred (a ⋈ b)).pred (e₁ a ⋈ e₂ b) unfolded
  -- Use subsume_def to conclude
  have h₆: ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: U₁ ⋈ U₂), (subsume e₁ e₂ x =ₗₓₗ y) ↔ ((subsume_graph e₁ e₂).pred x).pred y := subsume_def e₁ e₂
  have h₇: ∀ (y: U₁ ⋈ U₂), (subsume e₁ e₂ (a ⋈ b) =ₗₓₗ y) ↔ ((subsume_graph e₁ e₂).pred (a ⋈ b)).pred y := by forall_elim h₆, (a ⋈ b)
  have h₈: (subsume e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b)) ↔ ((subsume_graph e₁ e₂).pred (a ⋈ b)).pred (e₁.embedding a ⋈ e₂.embedding b) := by forall_elim h₇, (e₁.embedding a ⋈ e₂.embedding b)
  have h₉: subsume e₁ e₂ (a ⋈ b) =ₗₓₗ (e₁.embedding a ⋈ e₂.embedding b) := PC₀.deductive_eq_r2l h₈ h₅
  iterate h₉

end Dyads
end Universe
