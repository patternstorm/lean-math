import Universe
import Logic
import Universals.Arrows.Particular

/-!
# Arrow Universal

Arrows over U₁ and U₂ form their own Universal, 𝐀𝐫𝐫𝐨𝐰 U₁ U₂, with
componentwise equality. This makes arrows first-class: they can be quantified
over, collected into sets, and subjected to the same predicate/set machinery
as any other particulars.
-/

namespace Universe
namespace Arrows

open Logic
open Logic.PC₁
open Logic.ND

-- # =→ᵃ is an equivalence relation

-- ## =→ᵃ is reflexive
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-08
theorem eq_refl: ∀ (f: Arrows.Particular U₁ U₂), f =→ᵃ f := by forall_intro
  variable(f: Arrows.Particular U₁ U₂)
  -- Decompose f via exhaustiveness
  have h₁: ∃ (a: U₁.Particular), ∃ (b: U₂.Particular), f 🟰 (a ⭢ᵃ b) := by forall_elim exhaustiveness, f
  have ⟨(a: U₁.Particular), (h₂: ∃ (b: U₂.Particular), f 🟰 (a ⭢ᵃ b))⟩ := exists_elim h₁
  have ⟨(b: U₂.Particular), (h₃: f 🟰 (a ⭢ᵃ b))⟩ := exists_elim h₂
  -- Use Leibniz substitution to reduce f =→ᵃ f to (a ⭢ᵃ b) =→ᵃ (a ⭢ᵃ b)
  let pred: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ x =→ᵃ x)
  have h₄: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
  have h₅: ∀ (y: Arrows.Particular U₁ U₂), f 🟰 y → (pred f ↔ pred y) := by forall_elim h₄, f
  have h₆: f 🟰 (a ⭢ᵃ b) → (pred f ↔ pred (a ⭢ᵃ b)) := by forall_elim h₅, (a ⭢ᵃ b)
  have h₇: pred f ↔ pred (a ⭢ᵃ b) := by modus_ponens h₆, h₃
  -- Prove (a ⭢ b) =→ (a ⭢ b) via eq_def + component reflexivity
  have h₈: ∀ (b₁: U₂.Particular), ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (a ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim eq_def, a
  have h₉: ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (a ⭢ᵃ b) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a =₍U₁₎ a₂ ∧ b =₍U₂₎ b₂ := by forall_elim h₈, b
  have h₁₀: ∀ (b₂: U₂.Particular),
    (a ⭢ᵃ b) =→ᵃ (a ⭢ᵃ b₂) ↔ a =₍U₁₎ a ∧ b =₍U₂₎ b₂ := by forall_elim h₉, a
  have h₁₁: (a ⭢ᵃ b) =→ᵃ (a ⭢ᵃ b) ↔ a =₍U₁₎ a ∧ b =₍U₂₎ b := by forall_elim h₁₀, b
  have h₁₂: a =₍U₁₎ a := U₁.eq.refl a
  have h₁₃: b =₍U₂₎ b := U₂.eq.refl b
  have h₁₄: a =₍U₁₎ a ∧ b =₍U₂₎ b := by and_intro h₁₂, h₁₃
  have h₁₅: (a ⭢ᵃ b) =→ᵃ (a ⭢ᵃ b) := PC₀.deductive_eq_r2l h₁₁ h₁₄
  have h₁₆: pred f := PC₀.deductive_eq_r2l h₇ h₁₅
  iterate h₁₆

-- ## =→ᵃ is symmetric
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-08
theorem eq_sym: ∀ (f₁: Arrows.Particular U₁ U₂), ∀ (f₂: Arrows.Particular U₁ U₂), f₁ =→ᵃ f₂ → f₂ =→ᵃ f₁ := by forall_intro
  variable(f₁: Arrows.Particular U₁ U₂)
  variable(f₂: Arrows.Particular U₁ U₂)
  assume(h₁: f₁ =→ᵃ f₂)
  -- Decompose f₁
  have h₂: ∃ (a₁: U₁.Particular), ∃ (b₁: U₂.Particular), f₁ 🟰 (a₁ ⭢ᵃ b₁) := by forall_elim exhaustiveness, f₁
  have ⟨(a₁: U₁.Particular), (h₃: ∃ (b₁: U₂.Particular), f₁ 🟰 (a₁ ⭢ᵃ b₁))⟩ := exists_elim h₂
  have ⟨(b₁: U₂.Particular), (h₄: f₁ 🟰 (a₁ ⭢ᵃ b₁))⟩ := exists_elim h₃
  -- Decompose f₂
  have h₅: ∃ (a₂: U₁.Particular), ∃ (b₂: U₂.Particular), f₂ 🟰 (a₂ ⭢ᵃ b₂) := by forall_elim exhaustiveness, f₂
  have ⟨(a₂: U₁.Particular), (h₆: ∃ (b₂: U₂.Particular), f₂ 🟰 (a₂ ⭢ᵃ b₂))⟩ := exists_elim h₅
  have ⟨(b₂: U₂.Particular), (h₇: f₂ 🟰 (a₂ ⭢ᵃ b₂))⟩ := exists_elim h₆
  -- Transfer f₁ =→ᵃ f₂ to (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) via Leibniz substitution
  -- First substitute f₁ → (a₁ ⭢ᵃ b₁)
  let pred₁: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ x =→ᵃ f₂)
  have h₈: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₁ x ↔ pred₁ y) := by forall_elim leibniz_eq_subs, pred₁
  have h₉: ∀ (y: Arrows.Particular U₁ U₂), f₁ 🟰 y → (pred₁ f₁ ↔ pred₁ y) := by forall_elim h₈, f₁
  have h₁₀: f₁ 🟰 (a₁ ⭢ᵃ b₁) → (pred₁ f₁ ↔ pred₁ (a₁ ⭢ᵃ b₁)) := by forall_elim h₉, (a₁ ⭢ᵃ b₁)
  have h₁₁: pred₁ f₁ ↔ pred₁ (a₁ ⭢ᵃ b₁) := by modus_ponens h₁₀, h₄
  have h₁₂: (a₁ ⭢ᵃ b₁) =→ᵃ f₂ := PC₀.deductive_eq_l2r h₁₁ h₁
  -- Then substitute f₂ → (a₂ ⭢ᵃ b₂)
  let pred₂: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ (a₁ ⭢ᵃ b₁) =→ᵃ x)
  have h₁₃: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
  have h₁₄: ∀ (y: Arrows.Particular U₁ U₂), f₂ 🟰 y → (pred₂ f₂ ↔ pred₂ y) := by forall_elim h₁₃, f₂
  have h₁₅: f₂ 🟰 (a₂ ⭢ᵃ b₂) → (pred₂ f₂ ↔ pred₂ (a₂ ⭢ᵃ b₂)) := by forall_elim h₁₄, (a₂ ⭢ᵃ b₂)
  have h₁₆: pred₂ f₂ ↔ pred₂ (a₂ ⭢ᵃ b₂) := by modus_ponens h₁₅, h₇
  have h₁₇: (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) := PC₀.deductive_eq_l2r h₁₆ h₁₂
  -- Extract components via eq_def
  have h₁₈: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁') =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₁
  have h₁₉: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁) =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₁₈, b₁
  have h₂₀: ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₁₉, a₂
  have h₂₁: (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim h₂₀, b₂
  have h₂₂: a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := PC₀.deductive_eq_l2r h₂₁ h₁₇
  have h₂₃: a₁ =₍U₁₎ a₂ := by and_elim h₂₂
  have h₂₄: b₁ =₍U₂₎ b₂ := by and_elim h₂₂
  -- Reverse components
  have h₂₅: a₂ =₍U₁₎ a₁ := U₁.eq.sym a₁ a₂ h₂₃
  have h₂₆: b₂ =₍U₂₎ b₁ := U₂.eq.sym b₁ b₂ h₂₄
  -- Build (a₂ ⭢ᵃ b₂) =→ᵃ (a₁ ⭢ᵃ b₁) via eq_def
  have h₂₇: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⭢ᵃ b₁') =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₂
  have h₂₈: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⭢ᵃ b₂) =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₂₇, b₂
  have h₂₉: ∀ (b₂': U₂.Particular),
    (a₂ ⭢ᵃ b₂) =→ᵃ (a₁ ⭢ᵃ b₂') ↔ a₂ =₍U₁₎ a₁ ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₂₈, a₁
  have h₃₀: (a₂ ⭢ᵃ b₂) =→ᵃ (a₁ ⭢ᵃ b₁) ↔ a₂ =₍U₁₎ a₁ ∧ b₂ =₍U₂₎ b₁ := by forall_elim h₂₉, b₁
  have h₃₁: a₂ =₍U₁₎ a₁ ∧ b₂ =₍U₂₎ b₁ := by and_intro h₂₅, h₂₆
  have h₃₂: (a₂ ⭢ᵃ b₂) =→ᵃ (a₁ ⭢ᵃ b₁) := PC₀.deductive_eq_r2l h₃₀ h₃₁
  -- Transfer back to f₂ =→ᵃ f₁ via Leibniz substitution
  -- First: (a₂ ⭢ᵃ b₂) =→ᵃ (a₁ ⭢ᵃ b₁) → f₂ =→ᵃ (a₁ ⭢ᵃ b₁)
  let pred₃: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ x =→ᵃ (a₁ ⭢ᵃ b₁))
  have h₃₃: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₃ x ↔ pred₃ y) := by forall_elim leibniz_eq_subs, pred₃
  have h₃₄: ∀ (y: Arrows.Particular U₁ U₂), f₂ 🟰 y → (pred₃ f₂ ↔ pred₃ y) := by forall_elim h₃₃, f₂
  have h₃₅: f₂ 🟰 (a₂ ⭢ᵃ b₂) → (pred₃ f₂ ↔ pred₃ (a₂ ⭢ᵃ b₂)) := by forall_elim h₃₄, (a₂ ⭢ᵃ b₂)
  have h₃₆: pred₃ f₂ ↔ pred₃ (a₂ ⭢ᵃ b₂) := by modus_ponens h₃₅, h₇
  have h₃₇: f₂ =→ᵃ (a₁ ⭢ᵃ b₁) := PC₀.deductive_eq_r2l h₃₆ h₃₂
  -- Then: f₂ =→ᵃ (a₁ ⭢ᵃ b₁) → f₂ =→ᵃ f₁
  let pred₄: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ f₂ =→ᵃ x)
  have h₃₈: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₄ x ↔ pred₄ y) := by forall_elim leibniz_eq_subs, pred₄
  have h₃₉: ∀ (y: Arrows.Particular U₁ U₂), f₁ 🟰 y → (pred₄ f₁ ↔ pred₄ y) := by forall_elim h₃₈, f₁
  have h₄₀: f₁ 🟰 (a₁ ⭢ᵃ b₁) → (pred₄ f₁ ↔ pred₄ (a₁ ⭢ᵃ b₁)) := by forall_elim h₃₉, (a₁ ⭢ᵃ b₁)
  have h₄₁: pred₄ f₁ ↔ pred₄ (a₁ ⭢ᵃ b₁) := by modus_ponens h₄₀, h₄
  have h₄₂: f₂ =→ᵃ f₁ := PC₀.deductive_eq_r2l h₄₁ h₃₇
  iterate h₄₂

-- ## =→ᵃ is transitive
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-08
theorem eq_trans: ∀ (f₁: Arrows.Particular U₁ U₂), ∀ (f₂: Arrows.Particular U₁ U₂), ∀ (f₃: Arrows.Particular U₁ U₂),
    f₁ =→ᵃ f₂ ∧ f₂ =→ᵃ f₃ → f₁ =→ᵃ f₃ := by forall_intro
  variable(f₁: Arrows.Particular U₁ U₂)
  variable(f₂: Arrows.Particular U₁ U₂)
  variable(f₃: Arrows.Particular U₁ U₂)
  assume(h₁: f₁ =→ᵃ f₂ ∧ f₂ =→ᵃ f₃)
  have h₂: f₁ =→ᵃ f₂ := by and_elim h₁
  have h₃: f₂ =→ᵃ f₃ := by and_elim h₁
  -- Decompose all three arrows
  have h₄: ∃ (a₁: U₁.Particular), ∃ (b₁: U₂.Particular), f₁ 🟰 (a₁ ⭢ᵃ b₁) := by forall_elim exhaustiveness, f₁
  have ⟨(a₁: U₁.Particular), (h₅: ∃ (b₁: U₂.Particular), f₁ 🟰 (a₁ ⭢ᵃ b₁))⟩ := exists_elim h₄
  have ⟨(b₁: U₂.Particular), (h₆: f₁ 🟰 (a₁ ⭢ᵃ b₁))⟩ := exists_elim h₅
  have h₇: ∃ (a₂: U₁.Particular), ∃ (b₂: U₂.Particular), f₂ 🟰 (a₂ ⭢ᵃ b₂) := by forall_elim exhaustiveness, f₂
  have ⟨(a₂: U₁.Particular), (h₈: ∃ (b₂: U₂.Particular), f₂ 🟰 (a₂ ⭢ᵃ b₂))⟩ := exists_elim h₇
  have ⟨(b₂: U₂.Particular), (h₉: f₂ 🟰 (a₂ ⭢ᵃ b₂))⟩ := exists_elim h₈
  have h₁₀: ∃ (a₃: U₁.Particular), ∃ (b₃: U₂.Particular), f₃ 🟰 (a₃ ⭢ᵃ b₃) := by forall_elim exhaustiveness, f₃
  have ⟨(a₃: U₁.Particular), (h₁₁: ∃ (b₃: U₂.Particular), f₃ 🟰 (a₃ ⭢ᵃ b₃))⟩ := exists_elim h₁₀
  have ⟨(b₃: U₂.Particular), (h₁₂: f₃ 🟰 (a₃ ⭢ᵃ b₃))⟩ := exists_elim h₁₁
  -- Transfer f₁ =→ᵃ f₂ to (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂)
  let pred₁: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ x =→ᵃ f₂)
  have h₁₃: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₁ x ↔ pred₁ y) := by forall_elim leibniz_eq_subs, pred₁
  have h₁₄: ∀ (y: Arrows.Particular U₁ U₂), f₁ 🟰 y → (pred₁ f₁ ↔ pred₁ y) := by forall_elim h₁₃, f₁
  have h₁₅: f₁ 🟰 (a₁ ⭢ᵃ b₁) → (pred₁ f₁ ↔ pred₁ (a₁ ⭢ᵃ b₁)) := by forall_elim h₁₄, (a₁ ⭢ᵃ b₁)
  have h₁₆: pred₁ f₁ ↔ pred₁ (a₁ ⭢ᵃ b₁) := by modus_ponens h₁₅, h₆
  have h₁₇: (a₁ ⭢ᵃ b₁) =→ᵃ f₂ := PC₀.deductive_eq_l2r h₁₆ h₂
  let pred₂: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ (a₁ ⭢ᵃ b₁) =→ᵃ x)
  have h₁₈: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
  have h₁₉: ∀ (y: Arrows.Particular U₁ U₂), f₂ 🟰 y → (pred₂ f₂ ↔ pred₂ y) := by forall_elim h₁₈, f₂
  have h₂₀: f₂ 🟰 (a₂ ⭢ᵃ b₂) → (pred₂ f₂ ↔ pred₂ (a₂ ⭢ᵃ b₂)) := by forall_elim h₁₉, (a₂ ⭢ᵃ b₂)
  have h₂₁: pred₂ f₂ ↔ pred₂ (a₂ ⭢ᵃ b₂) := by modus_ponens h₂₀, h₉
  have h₂₂: (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) := PC₀.deductive_eq_l2r h₂₁ h₁₇
  -- Transfer f₂ =→ᵃ f₃ to (a₂ ⭢ᵃ b₂) =→ᵃ (a₃ ⭢ᵃ b₃)
  let pred₃: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ x =→ᵃ f₃)
  have h₂₃: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₃ x ↔ pred₃ y) := by forall_elim leibniz_eq_subs, pred₃
  have h₂₄: ∀ (y: Arrows.Particular U₁ U₂), f₂ 🟰 y → (pred₃ f₂ ↔ pred₃ y) := by forall_elim h₂₃, f₂
  have h₂₅: f₂ 🟰 (a₂ ⭢ᵃ b₂) → (pred₃ f₂ ↔ pred₃ (a₂ ⭢ᵃ b₂)) := by forall_elim h₂₄, (a₂ ⭢ᵃ b₂)
  have h₂₆: pred₃ f₂ ↔ pred₃ (a₂ ⭢ᵃ b₂) := by modus_ponens h₂₅, h₉
  have h₂₇: (a₂ ⭢ᵃ b₂) =→ᵃ f₃ := PC₀.deductive_eq_l2r h₂₆ h₃
  let pred₄: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ (a₂ ⭢ᵃ b₂) =→ᵃ x)
  have h₂₈: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₄ x ↔ pred₄ y) := by forall_elim leibniz_eq_subs, pred₄
  have h₂₉: ∀ (y: Arrows.Particular U₁ U₂), f₃ 🟰 y → (pred₄ f₃ ↔ pred₄ y) := by forall_elim h₂₈, f₃
  have h₃₀: f₃ 🟰 (a₃ ⭢ᵃ b₃) → (pred₄ f₃ ↔ pred₄ (a₃ ⭢ᵃ b₃)) := by forall_elim h₂₉, (a₃ ⭢ᵃ b₃)
  have h₃₁: pred₄ f₃ ↔ pred₄ (a₃ ⭢ᵃ b₃) := by modus_ponens h₃₀, h₁₂
  have h₃₂: (a₂ ⭢ᵃ b₂) =→ᵃ (a₃ ⭢ᵃ b₃) := PC₀.deductive_eq_l2r h₃₁ h₂₇
  -- Extract components from both equalities
  have h₃₃: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁') =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₁
  have h₃₄: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁) =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₃₃, b₁
  have h₃₅: ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₃₄, a₂
  have h₃₆: (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim h₃₅, b₂
  have h₃₇: a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := PC₀.deductive_eq_l2r h₃₆ h₂₂
  have h₃₈: a₁ =₍U₁₎ a₂ := by and_elim h₃₇
  have h₃₉: b₁ =₍U₂₎ b₂ := by and_elim h₃₇
  have h₄₀: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⭢ᵃ b₁') =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₂
  have h₄₁: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⭢ᵃ b₂) =→ᵃ (a₂' ⭢ᵃ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₄₀, b₂
  have h₄₂: ∀ (b₂': U₂.Particular),
    (a₂ ⭢ᵃ b₂) =→ᵃ (a₃ ⭢ᵃ b₂') ↔ a₂ =₍U₁₎ a₃ ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₄₁, a₃
  have h₄₃: (a₂ ⭢ᵃ b₂) =→ᵃ (a₃ ⭢ᵃ b₃) ↔ a₂ =₍U₁₎ a₃ ∧ b₂ =₍U₂₎ b₃ := by forall_elim h₄₂, b₃
  have h₄₄: a₂ =₍U₁₎ a₃ ∧ b₂ =₍U₂₎ b₃ := PC₀.deductive_eq_l2r h₄₃ h₃₂
  have h₄₅: a₂ =₍U₁₎ a₃ := by and_elim h₄₄
  have h₄₆: b₂ =₍U₂₎ b₃ := by and_elim h₄₄
  -- Transitivity on components
  have h₄₇: a₁ =₍U₁₎ a₂ ∧ a₂ =₍U₁₎ a₃ := by and_intro h₃₈, h₄₅
  have h₄₈: a₁ =₍U₁₎ a₃ := U₁.eq.trans a₁ a₂ a₃ h₄₇
  have h₄₉: b₁ =₍U₂₎ b₂ ∧ b₂ =₍U₂₎ b₃ := by and_intro h₃₉, h₄₆
  have h₅₀: b₁ =₍U₂₎ b₃ := U₂.eq.trans b₁ b₂ b₃ h₄₉
  -- Build (a₁ ⭢ᵃ b₁) =→ᵃ (a₃ ⭢ᵃ b₃) via eq_def
  have h₅₁: ∀ (b₂': U₂.Particular),
    (a₁ ⭢ᵃ b₁) =→ᵃ (a₃ ⭢ᵃ b₂') ↔ a₁ =₍U₁₎ a₃ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₃₄, a₃
  have h₅₂: (a₁ ⭢ᵃ b₁) =→ᵃ (a₃ ⭢ᵃ b₃) ↔ a₁ =₍U₁₎ a₃ ∧ b₁ =₍U₂₎ b₃ := by forall_elim h₅₁, b₃
  have h₅₃: a₁ =₍U₁₎ a₃ ∧ b₁ =₍U₂₎ b₃ := by and_intro h₄₈, h₅₀
  have h₅₄: (a₁ ⭢ᵃ b₁) =→ᵃ (a₃ ⭢ᵃ b₃) := PC₀.deductive_eq_r2l h₅₂ h₅₃
  -- Transfer back to f₁ =→ᵃ f₃ via Leibniz substitution
  let pred₅: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ x =→ᵃ (a₃ ⭢ᵃ b₃))
  have h₅₅: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₅ x ↔ pred₅ y) := by forall_elim leibniz_eq_subs, pred₅
  have h₅₆: ∀ (y: Arrows.Particular U₁ U₂), f₁ 🟰 y → (pred₅ f₁ ↔ pred₅ y) := by forall_elim h₅₅, f₁
  have h₅₇: f₁ 🟰 (a₁ ⭢ᵃ b₁) → (pred₅ f₁ ↔ pred₅ (a₁ ⭢ᵃ b₁)) := by forall_elim h₅₆, (a₁ ⭢ᵃ b₁)
  have h₅₈: pred₅ f₁ ↔ pred₅ (a₁ ⭢ᵃ b₁) := by modus_ponens h₅₇, h₆
  have h₅₉: f₁ =→ᵃ (a₃ ⭢ᵃ b₃) := PC₀.deductive_eq_r2l h₅₈ h₅₄
  let pred₆: (Arrows.Particular U₁ U₂) → Prop := (x: Arrows.Particular U₁ U₂ ↦ f₁ =→ᵃ x)
  have h₆₀: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), x 🟰 y → (pred₆ x ↔ pred₆ y) := by forall_elim leibniz_eq_subs, pred₆
  have h₆₁: ∀ (y: Arrows.Particular U₁ U₂), f₃ 🟰 y → (pred₆ f₃ ↔ pred₆ y) := by forall_elim h₆₀, f₃
  have h₆₂: f₃ 🟰 (a₃ ⭢ᵃ b₃) → (pred₆ f₃ ↔ pred₆ (a₃ ⭢ᵃ b₃)) := by forall_elim h₆₁, (a₃ ⭢ᵃ b₃)
  have h₆₃: pred₆ f₃ ↔ pred₆ (a₃ ⭢ᵃ b₃) := by modus_ponens h₆₂, h₁₂
  have h₆₄: f₁ =→ᵃ f₃ := PC₀.deductive_eq_r2l h₆₃ h₅₉
  iterate h₆₄

-- # =→ᵃ Equality
def equality (U₁: Universal) (U₂: Universal): Equality (Arrows.Particular U₁ U₂) :=
  let pred: (Arrows.Particular U₁ U₂) → (Arrows.Particular U₁ U₂) → Prop := eq
  let refl: ∀ (x: Arrows.Particular U₁ U₂), pred x x := eq_refl
  let sym: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), pred x y → pred y x := eq_sym
  let trans: ∀ (x: Arrows.Particular U₁ U₂), ∀ (y: Arrows.Particular U₁ U₂), ∀ (z: Arrows.Particular U₁ U₂), pred x y ∧ pred y z → pred x z := eq_trans
  { pred := pred, refl := refl, sym := sym, trans := trans }

-- # Arrow Universal
def ArrowUniversal (U₁: Universal) (U₂: Universal): Universal := {
  Particular := Arrows.Particular U₁ U₂
  eq := equality U₁ U₂
}
notation "𝐀𝐫𝐫𝐨𝐰" => ArrowUniversal
notation:35 U₁:36 " ➞ᵃ " U₂:36 => ArrowUniversal U₁ U₂
abbrev Arrow U₁ U₂ := (ArrowUniversal U₁ U₂).Particular
notation:35 U₁:36 " ⭢ᵃ " U₂:36 => Arrow U₁ U₂

end Arrows
end Universe
