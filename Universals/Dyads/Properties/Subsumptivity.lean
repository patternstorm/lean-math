import Universe
import Logic
import Universals.Dyads.Operations.Unary.Subsumption.Operation
import Universals.Dyads.Operations.Unary.Subsumption.Properties.Equations

/-!
# Dyad Subsumptivity

`subsumptivity` is a `SubUniversal` instance: given `e₁: U₁' <: U₁` and `e₂: U₂' <: U₂`,
the dyad universal `U₁' ⧓ U₂'` is a sub-universal of `U₁ ⧓ U₂`, via `subsume`.
Lean Type Class resolution composes this instance with `subuniversal_refl` and the refined-universal
instance to cover all coercion paths automatically.
-/

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsumptivity — U₁' ⧓ U₂' <: U₁ ⧓ U₂ via subsume

-- Proof by Claude Opus 4.7, 2026-04-19
noncomputable instance subsumptivity {U₁' U₁ U₂' U₂: Universal}
    [e₁: U₁' <: U₁] [e₂: U₂' <: U₂]: (U₁' ⧓ U₂') <: (U₁ ⧓ U₂) :=
  let subsume: (U₁' ⧓ U₂') ⟴ (U₁ ⧓ U₂) := subsume e₁ e₂
  let preserves_eq: ∀ (d₁': U₁' ⋈ U₂'), ∀ (d₂': U₁' ⋈ U₂'), d₁' =ₗₓₗ d₂' ↔ (subsume d₁' =ₗₓₗ subsume d₂') := by forall_intro
    variable(d₁': U₁' ⋈ U₂')
    variable(d₂': U₁' ⋈ U₂')
    -- Forward: congruence of the UnaryOperation.
    have h₁: d₁' =ₗₓₗ d₂' → subsume d₁' =ₗₓₗ subsume d₂' := by
      have h₁₁: d₁' =ₗₓₗ d₂' → (subsume d₁' =ₗₓₗ subsume d₂') := by forall_elim subsume.cong, d₁', d₂'
      iterate h₁₁
    -- Backward: injectivity via exhaustiveness + subsume_dyad + component preserves_eq.
    have h₂: subsume d₁' =ₗₓₗ subsume d₂' → d₁' =ₗₓₗ d₂' := by
      assume(h₂₁: subsume d₁' =ₗₓₗ subsume d₂')
      -- Decompose d₁' and d₂' via exhaustiveness
      have h₂₂: ∃ (a: U₁'.Particular), ∃ (b: U₂'.Particular), d₁' 🟰 (a ⋈ b) := by forall_elim exhaustiveness, d₁'
      have ⟨(a₁: U₁'.Particular), (h₂₃: ∃ (b: U₂'.Particular), d₁' 🟰 (a₁ ⋈ b))⟩ := exists_elim h₂₂
      have ⟨(b₁: U₂'.Particular), (h₂₄: d₁' 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₂₃
      have h₂₅: ∃ (a: U₁'.Particular), ∃ (b: U₂'.Particular), d₂' 🟰 (a ⋈ b) := by forall_elim exhaustiveness, d₂'
      have ⟨(a₂: U₁'.Particular), (h₂₆: ∃ (b: U₂'.Particular), d₂' 🟰 (a₂ ⋈ b))⟩ := exists_elim h₂₅
      have ⟨(b₂: U₂'.Particular), (h₂₇: d₂' 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₂₆
      -- subsume_dyad at (a₁, b₁) and (a₂, b₂)
      have h₂₈: subsume (a₁ ⋈ b₁) =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) := by forall_elim subsume_dyad e₁ e₂, a₁, b₁
      have h₂₉: subsume (a₂ ⋈ b₂) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by forall_elim subsume_dyad e₁ e₂, a₂, b₂
      -- Transfer d_i 🟰 (a_i ⋈ b_i) into subsume d_i =ₗₓₗ subsume (a_i ⋈ b_i) via Leibniz
      let pred₁: U₁' ⋈ U₂' → Prop := (x: U₁' ⋈ U₂' ↦ subsume d₁' =ₗₓₗ subsume x)
      have h₂₁₀: d₁' 🟰 (a₁ ⋈ b₁) → (pred₁ d₁' ↔ pred₁ (a₁ ⋈ b₁)) := by forall_elim leibniz_eq_subs, pred₁, d₁', (a₁ ⋈ b₁)
      have h₂₁₁: pred₁ d₁' ↔ pred₁ (a₁ ⋈ b₁) := by modus_ponens h₂₁₀, h₂₄
      -- pred₁ d₁' = (s d₁' =ₗₓₗ s d₁') which holds by refl on s d₁'
      have h₂₁₂: subsume d₁' =ₗₓₗ subsume d₁' := by forall_elim eq_refl, (subsume d₁')
      have h₂₁₃: subsume d₁' =ₗₓₗ subsume (a₁ ⋈ b₁) := PC₀.deductive_eq_l2r h₂₁₁ h₂₁₂
      let pred₂: U₁' ⋈ U₂' → Prop := (x: U₁' ⋈ U₂' ↦ subsume d₂' =ₗₓₗ subsume x)
      have h₂₁₄: d₂' 🟰 (a₂ ⋈ b₂) → (pred₂ d₂' ↔ pred₂ (a₂ ⋈ b₂)) := by forall_elim leibniz_eq_subs, pred₂, d₂', (a₂ ⋈ b₂)
      have h₂₁₅: pred₂ d₂' ↔ pred₂ (a₂ ⋈ b₂) := by modus_ponens h₂₁₄, h₂₇
      have h₂₁₆: subsume d₂' =ₗₓₗ subsume d₂' := by forall_elim eq_refl, (subsume d₂')
      have h₂₁₇: subsume d₂' =ₗₓₗ subsume (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₂₁₅ h₂₁₆
      -- Chain: (e₁ a₁ ⋈ e₂ b₁) =ₗₓₗ s (a₁ ⋈ b₁) =ₗₓₗ s d₁' =ₗₓₗ s d₂' =ₗₓₗ s (a₂ ⋈ b₂) =ₗₓₗ (e₁ a₂ ⋈ e₂ b₂)
      have h₂₁₈: subsume (a₁ ⋈ b₁) =ₗₓₗ (e₁.embedding a₁ ⋈ e₂.embedding b₁) → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) := by forall_elim eq_sym, (subsume (a₁ ⋈ b₁)), (e₁.embedding a₁ ⋈ e₂.embedding b₁)
      have h₂₁₉: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) := by modus_ponens h₂₁₈, h₂₈
      have h₂₂₀: subsume d₁' =ₗₓₗ subsume (a₁ ⋈ b₁) → subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' := by forall_elim eq_sym, (subsume d₁'), (subsume (a₁ ⋈ b₁))
      have h₂₂₁: subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' := by modus_ponens h₂₂₀, h₂₁₃
      have h₂₂₂: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) ∧ subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' := by and_intro h₂₁₉, h₂₂₁
      have h₂₂₃: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₁ ⋈ b₁) ∧ subsume (a₁ ⋈ b₁) =ₗₓₗ subsume d₁' → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume (a₁ ⋈ b₁)), (subsume d₁')
      have h₂₂₄: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' := by modus_ponens h₂₂₃, h₂₂₂
      have h₂₂₅: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' ∧ subsume d₁' =ₗₓₗ subsume d₂' := by and_intro h₂₂₄, h₂₁
      have h₂₂₆: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₁' ∧ subsume d₁' =ₗₓₗ subsume d₂' → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume d₁'), (subsume d₂')
      have h₂₂₇: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' := by modus_ponens h₂₂₆, h₂₂₅
      have h₂₂₈: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' ∧ subsume d₂' =ₗₓₗ subsume (a₂ ⋈ b₂) := by and_intro h₂₂₇, h₂₁₇
      have h₂₂₉: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume d₂' ∧ subsume d₂' =ₗₓₗ subsume (a₂ ⋈ b₂) → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume d₂'), (subsume (a₂ ⋈ b₂))
      have h₂₃₀: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) := by modus_ponens h₂₂₉, h₂₂₈
      have h₂₃₁: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) ∧ subsume (a₂ ⋈ b₂) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by and_intro h₂₃₀, h₂₉
      have h₂₃₂: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ subsume (a₂ ⋈ b₂) ∧ subsume (a₂ ⋈ b₂) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) → (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by forall_elim eq_trans, (e₁.embedding a₁ ⋈ e₂.embedding b₁), (subsume (a₂ ⋈ b₂)), (e₁.embedding a₂ ⋈ e₂.embedding b₂)
      have h₂₃₃: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) := by modus_ponens h₂₃₂, h₂₃₁
      -- Apply eq_def (forward) to extract component equalities
      have h₂₃₄: (e₁.embedding a₁ ⋈ e₂.embedding b₁) =ₗₓₗ (e₁.embedding a₂ ⋈ e₂.embedding b₂) ↔ e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := by forall_elim eq_def, (e₁.embedding a₁), (e₂.embedding b₁), (e₁.embedding a₂), (e₂.embedding b₂)
      have h₂₃₅: e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ ∧ e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := PC₀.deductive_eq_l2r h₂₃₄ h₂₃₃
      have h₂₃₆: e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂ := by and_elim h₂₃₅
      have h₂₃₇: e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂ := by and_elim h₂₃₅
      -- Apply e_i.preserves_eq (backward) to recover component equalities
      have h₂₃₈: a₁ =₍U₁'₎ a₂ ↔ (e₁.embedding a₁ =₍U₁₎ e₁.embedding a₂) := by forall_elim e₁.preserves_eq, a₁, a₂
      have h₂₃₉: a₁ =₍U₁'₎ a₂ := PC₀.deductive_eq_r2l h₂₃₈ h₂₃₆
      have h₂₄₀: b₁ =₍U₂'₎ b₂ ↔ (e₂.embedding b₁ =₍U₂₎ e₂.embedding b₂) := by forall_elim e₂.preserves_eq, b₁, b₂
      have h₂₄₁: b₁ =₍U₂'₎ b₂ := PC₀.deductive_eq_r2l h₂₄₀ h₂₃₇
      -- Apply eq_def (backward) to get (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂)
      have h₂₄₂: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂ := by forall_elim eq_def, a₁, b₁, a₂, b₂
      have h₂₄₃: a₁ =₍U₁'₎ a₂ ∧ b₁ =₍U₂'₎ b₂ := by and_intro h₂₃₉, h₂₄₁
      have h₂₄₄: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_r2l h₂₄₂ h₂₄₃
      -- Transfer back to d₁' =ₗₓₗ d₂' via Leibniz
      let pred₃: U₁' ⋈ U₂' → Prop := (x: U₁' ⋈ U₂' ↦ x =ₗₓₗ (a₂ ⋈ b₂))
      have h₂₄₅: d₁' 🟰 (a₁ ⋈ b₁) → (pred₃ d₁' ↔ pred₃ (a₁ ⋈ b₁)) := by forall_elim leibniz_eq_subs, pred₃, d₁', (a₁ ⋈ b₁)
      have h₂₄₆: pred₃ d₁' ↔ pred₃ (a₁ ⋈ b₁) := by modus_ponens h₂₄₅, h₂₄
      have h₂₄₇: d₁' =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_r2l h₂₄₆ h₂₄₄
      let pred₄: U₁' ⋈ U₂' → Prop := (x: U₁' ⋈ U₂' ↦ d₁' =ₗₓₗ x)
      have h₂₄₈: d₂' 🟰 (a₂ ⋈ b₂) → (pred₄ d₂' ↔ pred₄ (a₂ ⋈ b₂)) := by forall_elim leibniz_eq_subs, pred₄, d₂', (a₂ ⋈ b₂)
      have h₂₄₉: pred₄ d₂' ↔ pred₄ (a₂ ⋈ b₂) := by modus_ponens h₂₄₈, h₂₇
      have h₂₅₀: d₁' =ₗₓₗ d₂' := PC₀.deductive_eq_r2l h₂₄₉ h₂₄₇
      iterate h₂₅₀
    have h₃: d₁' =ₗₓₗ d₂' ↔ (subsume d₁' =ₗₓₗ subsume d₂') := by iff_intro h₁, h₂
    iterate h₃
  { embedding := subsume, preserves_eq := preserves_eq }

end Dyads
end Universe
