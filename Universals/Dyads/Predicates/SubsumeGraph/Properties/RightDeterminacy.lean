import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsume graph — right-determinacy
-- If `d₁` and `d₂` are both subsume-images of the same domain dyad `d'`,
-- they are equal in `U₁ ⧓ U₂`.

-- Proof by Claude Opus 4.7 Max, 2026-05-03
theorem subsume_right_determinacy {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
    ∀ (d': U₁' ⋈ U₂'), ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂),
      (∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular),
         d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))
      ∧ (∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular),
         d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))
      → d₁ =ₗₓₗ d₂ := by forall_intro
  variable(d': U₁' ⋈ U₂')
  variable(d₁: U₁ ⋈ U₂)
  variable(d₂: U₁ ⋈ U₂)
  assume(h₀:
    (∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular),
       d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))
    ∧ (∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular),
       d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b')))
  -- Witnesses for d₁
  have h₁: ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₀
  have ⟨(a₁: U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d' =ₗₓₗ (a₁ ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b'))⟩ := exists_elim h₁
  have ⟨(b₁: U₂'.Particular), (h₃: d' =ₗₓₗ (a₁ ⋈ b₁) ∧ d₁ =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁))⟩ := exists_elim h₂
  have h₄: d' =ₗₓₗ (a₁ ⋈ b₁) := by and_elim h₃
  have h₅: d₁ =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) := by and_elim h₃
  -- Witnesses for d₂
  have h₆: ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₀
  have ⟨(a₂: U₁'.Particular), (h₇: ∃ (b': U₂'.Particular), d' =ₗₓₗ (a₂ ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b'))⟩ := exists_elim h₆
  have ⟨(b₂: U₂'.Particular), (h₈: d' =ₗₓₗ (a₂ ⋈ b₂) ∧ d₂ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂))⟩ := exists_elim h₇
  have h₉: d' =ₗₓₗ (a₂ ⋈ b₂) := by and_elim h₈
  have h₁₀: d₂ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by and_elim h₈
  -- Chain (a₁ ⋈ b₁) =ₗₓₗ d' =ₗₓₗ (a₂ ⋈ b₂) via sym + trans
  have h₁₁: d' =ₗₓₗ (a₁ ⋈ b₁) → (a₁ ⋈ b₁) =ₗₓₗ d' := by forall_elim eq_sym, d', (a₁ ⋈ b₁)
  have h₁₂: (a₁ ⋈ b₁) =ₗₓₗ d' := by modus_ponens h₁₁, h₄
  have h₁₃: (a₁ ⋈ b₁) =ₗₓₗ d' ∧ d' =ₗₓₗ (a₂ ⋈ b₂) := by and_intro h₁₂, h₉
  have h₁₄: (a₁ ⋈ b₁) =ₗₓₗ d' ∧ d' =ₗₓₗ (a₂ ⋈ b₂) → (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := by forall_elim eq_trans, (a₁ ⋈ b₁), d', (a₂ ⋈ b₂)
  have h₁₅: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := by modus_ponens h₁₄, h₁₃
  -- Lift to component equalities via eq_def forward
  have h₁₆: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂ := by forall_elim eq_def, a₁, b₁, a₂, b₂
  have h₁₇: a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂ := PC₀.deductive_eq_l2r h₁₆ h₁₅
  have h₁₈: a₁ =₍U₁'₎ a₂ := by and_elim h₁₇
  have h₁₉: b₁ =₍U₂'₎ b₂ := by and_elim h₁₇
  -- Transport via e_i.preserves_eq forward
  have h₂₀: a₁ =₍U₁'₎ a₂ ↔ (e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂) := by forall_elim e₁.preserves_eq, a₁, a₂
  have h₂₁: e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ := PC₀.deductive_eq_l2r h₂₀ h₁₈
  have h₂₂: b₁ =₍U₂'₎ b₂ ↔ (e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂) := by forall_elim e₂.preserves_eq, b₁, b₂
  have h₂₃: e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := PC₀.deductive_eq_l2r h₂₂ h₁₉
  -- Rebuild via eq_def backward
  have h₂₄: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) ↔ e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := by forall_elim eq_def, (e₁.embedding a₁), (e₂.embedding b₁), (e₁.embedding a₂), (e₂.embedding b₂)
  have h₂₅: e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := by and_intro h₂₁, h₂₃
  have h₂₆: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := PC₀.deductive_eq_r2l h₂₄ h₂₅
  -- Chain d₁ =ₗₓₗ (e₁ a₁ ⋈ e₂ b₁) =ₗₓₗ (e₁ a₂ ⋈ e₂ b₂)
  have h₂₇: d₁ =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) ∧ (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by and_intro h₅, h₂₆
  have h₂₈: d₁ =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) ∧ (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) → d₁ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by forall_elim eq_trans, d₁, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (e₁.embedding a₂ ⋈ e₂.embedding b₂)
  have h₂₉: d₁ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by modus_ponens h₂₈, h₂₇
  -- Sym on h₁₀ and final trans
  have h₃₀: d₂ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) → (e₁.embedding a₂ ⋈ e₂.embedding b₂) =ₗₓₗ d₂ := by forall_elim eq_sym, d₂, (e₁.embedding a₂ ⋈ e₂.embedding b₂)
  have h₃₁: (e₁.embedding a₂ ⋈ e₂.embedding b₂) =ₗₓₗ d₂ := by modus_ponens h₃₀, h₁₀
  have h₃₂: d₁ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) ∧ (e₁.embedding a₂ ⋈ e₂.embedding b₂) =ₗₓₗ d₂ := by and_intro h₂₉, h₃₁
  have h₃₃: d₁ =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) ∧ (e₁.embedding a₂ ⋈ e₂.embedding b₂) =ₗₓₗ d₂ → d₁ =ₗₓₗ d₂ := by forall_elim eq_trans, d₁, (e₁.embedding a₂ ⋈ e₂.embedding b₂), d₂
  have h₃₄: d₁ =ₗₓₗ d₂ := by modus_ponens h₃₃, h₃₂
  iterate h₃₄

end Dyads
end Universe
