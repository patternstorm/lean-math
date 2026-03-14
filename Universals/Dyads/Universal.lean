import Universe
import Logic
import Universals.Dyads.Particular

/-!
# Dyad Universal

Dyads over U₁ and U₂ form their own Universal, U₁ ⋈ U₂, with relatum-wise
equality. This makes dyads first-class: they can be quantified over, collected
into sets, and subjected to the same predicate/set machinery as any other
particulars — which is exactly the point. Binary predicates become unary
predicates on this Universal, and sets of dyads become relations.
-/

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # =ₗₓₗ is an equivalence relation

-- ## =ₗₓₗ is reflexive
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-28
theorem eq_refl: ∀ (d: Dyads.Particular U₁ U₂), d =ₗₓₗ d := by forall_intro
  variable(d: Dyads.Particular U₁ U₂)
  -- Decompose d via exhaustiveness
  have h₁: ∃ (a: U₁.Particular), ∃ (b: U₂.Particular), d 🟰 (a ⋈ b) := by forall_elim exhaustiveness, d
  have ⟨(a: U₁.Particular), (h₂: ∃ (b: U₂.Particular), d 🟰 (a ⋈ b))⟩ := exists_elim h₁
  have ⟨(b: U₂.Particular), (h₃: d 🟰 (a ⋈ b))⟩ := exists_elim h₂
  -- Use Leibniz substitution to reduce d =ₗₓₗ d to (a ⋈ b) =ₗₓₗ (a ⋈ b)
  let pred: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ x =ₗₓₗ x)
  have h₄: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
  have h₅: ∀ (y: Dyads.Particular U₁ U₂), d 🟰 y → (pred d ↔ pred y) := by forall_elim h₄, d
  have h₆: d 🟰 (a ⋈ b) → (pred d ↔ pred (a ⋈ b)) := by forall_elim h₅, (a ⋈ b)
  have h₇: pred d ↔ pred (a ⋈ b) := by modus_ponens h₆, h₃
  -- Prove (a ⋈ b) =ₗₓₗ (a ⋈ b) via eq_def + relatum reflexivity
  have h₈: ∀ (b₁: U₂.Particular), ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (a ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim eq_def, a
  have h₉: ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
    (a ⋈ b) =ₗₓₗ (a₂ ⋈ b₂) ↔ a =₍U₁₎ a₂ ∧ b =₍U₂₎ b₂ := by forall_elim h₈, b
  have h₁₀: ∀ (b₂: U₂.Particular),
    (a ⋈ b) =ₗₓₗ (a ⋈ b₂) ↔ a =₍U₁₎ a ∧ b =₍U₂₎ b₂ := by forall_elim h₉, a
  have h₁₁: (a ⋈ b) =ₗₓₗ (a ⋈ b) ↔ a =₍U₁₎ a ∧ b =₍U₂₎ b := by forall_elim h₁₀, b
  have h₁₂: a =₍U₁₎ a := U₁.eq.refl a
  have h₁₃: b =₍U₂₎ b := U₂.eq.refl b
  have h₁₄: a =₍U₁₎ a ∧ b =₍U₂₎ b := by and_intro h₁₂, h₁₃
  have h₁₅: (a ⋈ b) =ₗₓₗ (a ⋈ b) := PC₀.deductive_eq_r2l h₁₁ h₁₄
  have h₁₆: pred d := PC₀.deductive_eq_r2l h₇ h₁₅
  iterate h₁₆

-- ## =ₗₓₗ is symmetric
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-28
theorem eq_sym: ∀ (d₁: Dyads.Particular U₁ U₂), ∀ (d₂: Dyads.Particular U₁ U₂), d₁ =ₗₓₗ d₂ → d₂ =ₗₓₗ d₁ := by forall_intro
  variable(d₁: Dyads.Particular U₁ U₂)
  variable(d₂: Dyads.Particular U₁ U₂)
  assume(h₁: d₁ =ₗₓₗ d₂)
  -- Decompose d₁
  have h₂: ∃ (a₁: U₁.Particular), ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁) := by forall_elim exhaustiveness, d₁
  have ⟨(a₁: U₁.Particular), (h₃: ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₂
  have ⟨(b₁: U₂.Particular), (h₄: d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₃
  -- Decompose d₂
  have h₅: ∃ (a₂: U₁.Particular), ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂) := by forall_elim exhaustiveness, d₂
  have ⟨(a₂: U₁.Particular), (h₆: ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₅
  have ⟨(b₂: U₂.Particular), (h₇: d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₆
  -- Transfer d₁ =ₗₓₗ d₂ to (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) via Leibniz substitution
  -- First substitute d₁ → (a₁ ⋈ b₁)
  let pred₁: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ x =ₗₓₗ d₂)
  have h₈: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₁ x ↔ pred₁ y) := by forall_elim leibniz_eq_subs, pred₁
  have h₉: ∀ (y: Dyads.Particular U₁ U₂), d₁ 🟰 y → (pred₁ d₁ ↔ pred₁ y) := by forall_elim h₈, d₁
  have h₁₀: d₁ 🟰 (a₁ ⋈ b₁) → (pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁)) := by forall_elim h₉, (a₁ ⋈ b₁)
  have h₁₁: pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁) := by modus_ponens h₁₀, h₄
  have h₁₂: (a₁ ⋈ b₁) =ₗₓₗ d₂ := PC₀.deductive_eq_l2r h₁₁ h₁
  -- Then substitute d₂ → (a₂ ⋈ b₂)
  let pred₂: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ (a₁ ⋈ b₁) =ₗₓₗ x)
  have h₁₃: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
  have h₁₄: ∀ (y: Dyads.Particular U₁ U₂), d₂ 🟰 y → (pred₂ d₂ ↔ pred₂ y) := by forall_elim h₁₃, d₂
  have h₁₅: d₂ 🟰 (a₂ ⋈ b₂) → (pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂)) := by forall_elim h₁₄, (a₂ ⋈ b₂)
  have h₁₆: pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂) := by modus_ponens h₁₅, h₇
  have h₁₇: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₁₆ h₁₂
  -- Extract relata via eq_def
  have h₁₈: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁') =ₗₓₗ (a₂' ⋈ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₁
  have h₁₉: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁) =ₗₓₗ (a₂' ⋈ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₁₈, b₁
  have h₂₀: ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂') ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₁₉, a₂
  have h₂₁: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim h₂₀, b₂
  have h₂₂: a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := PC₀.deductive_eq_l2r h₂₁ h₁₇
  have h₂₃: a₁ =₍U₁₎ a₂ := by and_elim h₂₂
  have h₂₄: b₁ =₍U₂₎ b₂ := by and_elim h₂₂
  -- Reverse relata
  have h₂₅: a₂ =₍U₁₎ a₁ := U₁.eq.sym a₁ a₂ h₂₃
  have h₂₆: b₂ =₍U₂₎ b₁ := U₂.eq.sym b₁ b₂ h₂₄
  -- Build (a₂ ⋈ b₂) =ₗₓₗ (a₁ ⋈ b₁) via eq_def
  have h₂₇: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⋈ b₁') =ₗₓₗ (a₂' ⋈ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₂
  have h₂₈: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⋈ b₂) =ₗₓₗ (a₂' ⋈ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₂₇, b₂
  have h₂₉: ∀ (b₂': U₂.Particular),
    (a₂ ⋈ b₂) =ₗₓₗ (a₁ ⋈ b₂') ↔ a₂ =₍U₁₎ a₁ ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₂₈, a₁
  have h₃₀: (a₂ ⋈ b₂) =ₗₓₗ (a₁ ⋈ b₁) ↔ a₂ =₍U₁₎ a₁ ∧ b₂ =₍U₂₎ b₁ := by forall_elim h₂₉, b₁
  have h₃₁: a₂ =₍U₁₎ a₁ ∧ b₂ =₍U₂₎ b₁ := by and_intro h₂₅, h₂₆
  have h₃₂: (a₂ ⋈ b₂) =ₗₓₗ (a₁ ⋈ b₁) := PC₀.deductive_eq_r2l h₃₀ h₃₁
  -- Transfer back to d₂ =ₗₓₗ d₁ via Leibniz substitution
  -- First: (a₂ ⋈ b₂) =ₗₓₗ (a₁ ⋈ b₁) → d₂ =ₗₓₗ (a₁ ⋈ b₁)
  let pred₃: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ x =ₗₓₗ (a₁ ⋈ b₁))
  have h₃₃: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₃ x ↔ pred₃ y) := by forall_elim leibniz_eq_subs, pred₃
  have h₃₄: ∀ (y: Dyads.Particular U₁ U₂), d₂ 🟰 y → (pred₃ d₂ ↔ pred₃ y) := by forall_elim h₃₃, d₂
  have h₃₅: d₂ 🟰 (a₂ ⋈ b₂) → (pred₃ d₂ ↔ pred₃ (a₂ ⋈ b₂)) := by forall_elim h₃₄, (a₂ ⋈ b₂)
  have h₃₆: pred₃ d₂ ↔ pred₃ (a₂ ⋈ b₂) := by modus_ponens h₃₅, h₇
  have h₃₇: d₂ =ₗₓₗ (a₁ ⋈ b₁) := PC₀.deductive_eq_r2l h₃₆ h₃₂
  -- Then: d₂ =ₗₓₗ (a₁ ⋈ b₁) → d₂ =ₗₓₗ d₁
  let pred₄: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ d₂ =ₗₓₗ x)
  have h₃₈: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₄ x ↔ pred₄ y) := by forall_elim leibniz_eq_subs, pred₄
  have h₃₉: ∀ (y: Dyads.Particular U₁ U₂), d₁ 🟰 y → (pred₄ d₁ ↔ pred₄ y) := by forall_elim h₃₈, d₁
  have h₄₀: d₁ 🟰 (a₁ ⋈ b₁) → (pred₄ d₁ ↔ pred₄ (a₁ ⋈ b₁)) := by forall_elim h₃₉, (a₁ ⋈ b₁)
  have h₄₁: pred₄ d₁ ↔ pred₄ (a₁ ⋈ b₁) := by modus_ponens h₄₀, h₄
  have h₄₂: d₂ =ₗₓₗ d₁ := PC₀.deductive_eq_r2l h₄₁ h₃₇
  iterate h₄₂

-- ## =ₗₓₗ is transitive
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-28
theorem eq_trans: ∀ (d₁: Dyads.Particular U₁ U₂), ∀ (d₂: Dyads.Particular U₁ U₂), ∀ (d₃: Dyads.Particular U₁ U₂),
    d₁ =ₗₓₗ d₂ ∧ d₂ =ₗₓₗ d₃ → d₁ =ₗₓₗ d₃ := by forall_intro
  variable(d₁: Dyads.Particular U₁ U₂)
  variable(d₂: Dyads.Particular U₁ U₂)
  variable(d₃: Dyads.Particular U₁ U₂)
  assume(h₁: d₁ =ₗₓₗ d₂ ∧ d₂ =ₗₓₗ d₃)
  have h₂: d₁ =ₗₓₗ d₂ := by and_elim h₁
  have h₃: d₂ =ₗₓₗ d₃ := by and_elim h₁
  -- Decompose all three dyads
  have h₄: ∃ (a₁: U₁.Particular), ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁) := by forall_elim exhaustiveness, d₁
  have ⟨(a₁: U₁.Particular), (h₅: ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₄
  have ⟨(b₁: U₂.Particular), (h₆: d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₅
  have h₇: ∃ (a₂: U₁.Particular), ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂) := by forall_elim exhaustiveness, d₂
  have ⟨(a₂: U₁.Particular), (h₈: ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₇
  have ⟨(b₂: U₂.Particular), (h₉: d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₈
  have h₁₀: ∃ (a₃: U₁.Particular), ∃ (b₃: U₂.Particular), d₃ 🟰 (a₃ ⋈ b₃) := by forall_elim exhaustiveness, d₃
  have ⟨(a₃: U₁.Particular), (h₁₁: ∃ (b₃: U₂.Particular), d₃ 🟰 (a₃ ⋈ b₃))⟩ := exists_elim h₁₀
  have ⟨(b₃: U₂.Particular), (h₁₂: d₃ 🟰 (a₃ ⋈ b₃))⟩ := exists_elim h₁₁
  -- Transfer d₁ =ₗₓₗ d₂ to (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂)
  let pred₁: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ x =ₗₓₗ d₂)
  have h₁₃: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₁ x ↔ pred₁ y) := by forall_elim leibniz_eq_subs, pred₁
  have h₁₄: ∀ (y: Dyads.Particular U₁ U₂), d₁ 🟰 y → (pred₁ d₁ ↔ pred₁ y) := by forall_elim h₁₃, d₁
  have h₁₅: d₁ 🟰 (a₁ ⋈ b₁) → (pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁)) := by forall_elim h₁₄, (a₁ ⋈ b₁)
  have h₁₆: pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁) := by modus_ponens h₁₅, h₆
  have h₁₇: (a₁ ⋈ b₁) =ₗₓₗ d₂ := PC₀.deductive_eq_l2r h₁₆ h₂
  let pred₂: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ (a₁ ⋈ b₁) =ₗₓₗ x)
  have h₁₈: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
  have h₁₉: ∀ (y: Dyads.Particular U₁ U₂), d₂ 🟰 y → (pred₂ d₂ ↔ pred₂ y) := by forall_elim h₁₈, d₂
  have h₂₀: d₂ 🟰 (a₂ ⋈ b₂) → (pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂)) := by forall_elim h₁₉, (a₂ ⋈ b₂)
  have h₂₁: pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂) := by modus_ponens h₂₀, h₉
  have h₂₂: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₂₁ h₁₇
  -- Transfer d₂ =ₗₓₗ d₃ to (a₂ ⋈ b₂) =ₗₓₗ (a₃ ⋈ b₃)
  let pred₃: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ x =ₗₓₗ d₃)
  have h₂₃: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₃ x ↔ pred₃ y) := by forall_elim leibniz_eq_subs, pred₃
  have h₂₄: ∀ (y: Dyads.Particular U₁ U₂), d₂ 🟰 y → (pred₃ d₂ ↔ pred₃ y) := by forall_elim h₂₃, d₂
  have h₂₅: d₂ 🟰 (a₂ ⋈ b₂) → (pred₃ d₂ ↔ pred₃ (a₂ ⋈ b₂)) := by forall_elim h₂₄, (a₂ ⋈ b₂)
  have h₂₆: pred₃ d₂ ↔ pred₃ (a₂ ⋈ b₂) := by modus_ponens h₂₅, h₉
  have h₂₇: (a₂ ⋈ b₂) =ₗₓₗ d₃ := PC₀.deductive_eq_l2r h₂₆ h₃
  let pred₄: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ (a₂ ⋈ b₂) =ₗₓₗ x)
  have h₂₈: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₄ x ↔ pred₄ y) := by forall_elim leibniz_eq_subs, pred₄
  have h₂₉: ∀ (y: Dyads.Particular U₁ U₂), d₃ 🟰 y → (pred₄ d₃ ↔ pred₄ y) := by forall_elim h₂₈, d₃
  have h₃₀: d₃ 🟰 (a₃ ⋈ b₃) → (pred₄ d₃ ↔ pred₄ (a₃ ⋈ b₃)) := by forall_elim h₂₉, (a₃ ⋈ b₃)
  have h₃₁: pred₄ d₃ ↔ pred₄ (a₃ ⋈ b₃) := by modus_ponens h₃₀, h₁₂
  have h₃₂: (a₂ ⋈ b₂) =ₗₓₗ (a₃ ⋈ b₃) := PC₀.deductive_eq_l2r h₃₁ h₂₇
  -- Extract relata from both equalities
  have h₃₃: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁') =ₗₓₗ (a₂' ⋈ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₁
  have h₃₄: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁) =ₗₓₗ (a₂' ⋈ b₂') ↔ a₁ =₍U₁₎ a₂' ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₃₃, b₁
  have h₃₅: ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂') ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₃₄, a₂
  have h₃₆: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim h₃₅, b₂
  have h₃₇: a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := PC₀.deductive_eq_l2r h₃₆ h₂₂
  have h₃₈: a₁ =₍U₁₎ a₂ := by and_elim h₃₇
  have h₃₉: b₁ =₍U₂₎ b₂ := by and_elim h₃₇
  have h₄₀: ∀ (b₁': U₂.Particular), ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⋈ b₁') =ₗₓₗ (a₂' ⋈ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₁' =₍U₂₎ b₂' := by forall_elim eq_def, a₂
  have h₄₁: ∀ (a₂': U₁.Particular), ∀ (b₂': U₂.Particular),
    (a₂ ⋈ b₂) =ₗₓₗ (a₂' ⋈ b₂') ↔ a₂ =₍U₁₎ a₂' ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₄₀, b₂
  have h₄₂: ∀ (b₂': U₂.Particular),
    (a₂ ⋈ b₂) =ₗₓₗ (a₃ ⋈ b₂') ↔ a₂ =₍U₁₎ a₃ ∧ b₂ =₍U₂₎ b₂' := by forall_elim h₄₁, a₃
  have h₄₃: (a₂ ⋈ b₂) =ₗₓₗ (a₃ ⋈ b₃) ↔ a₂ =₍U₁₎ a₃ ∧ b₂ =₍U₂₎ b₃ := by forall_elim h₄₂, b₃
  have h₄₄: a₂ =₍U₁₎ a₃ ∧ b₂ =₍U₂₎ b₃ := PC₀.deductive_eq_l2r h₄₃ h₃₂
  have h₄₅: a₂ =₍U₁₎ a₃ := by and_elim h₄₄
  have h₄₆: b₂ =₍U₂₎ b₃ := by and_elim h₄₄
  -- Transitivity on relata
  have h₄₇: a₁ =₍U₁₎ a₂ ∧ a₂ =₍U₁₎ a₃ := by and_intro h₃₈, h₄₅
  have h₄₈: a₁ =₍U₁₎ a₃ := U₁.eq.trans a₁ a₂ a₃ h₄₇
  have h₄₉: b₁ =₍U₂₎ b₂ ∧ b₂ =₍U₂₎ b₃ := by and_intro h₃₉, h₄₆
  have h₅₀: b₁ =₍U₂₎ b₃ := U₂.eq.trans b₁ b₂ b₃ h₄₉
  -- Build (a₁ ⋈ b₁) =ₗₓₗ (a₃ ⋈ b₃) via eq_def
  have h₅₁: ∀ (b₂': U₂.Particular),
    (a₁ ⋈ b₁) =ₗₓₗ (a₃ ⋈ b₂') ↔ a₁ =₍U₁₎ a₃ ∧ b₁ =₍U₂₎ b₂' := by forall_elim h₃₄, a₃
  have h₅₂: (a₁ ⋈ b₁) =ₗₓₗ (a₃ ⋈ b₃) ↔ a₁ =₍U₁₎ a₃ ∧ b₁ =₍U₂₎ b₃ := by forall_elim h₅₁, b₃
  have h₅₃: a₁ =₍U₁₎ a₃ ∧ b₁ =₍U₂₎ b₃ := by and_intro h₄₈, h₅₀
  have h₅₄: (a₁ ⋈ b₁) =ₗₓₗ (a₃ ⋈ b₃) := PC₀.deductive_eq_r2l h₅₂ h₅₃
  -- Transfer back to d₁ =ₗₓₗ d₃ via Leibniz substitution
  let pred₅: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ x =ₗₓₗ (a₃ ⋈ b₃))
  have h₅₅: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₅ x ↔ pred₅ y) := by forall_elim leibniz_eq_subs, pred₅
  have h₅₆: ∀ (y: Dyads.Particular U₁ U₂), d₁ 🟰 y → (pred₅ d₁ ↔ pred₅ y) := by forall_elim h₅₅, d₁
  have h₅₇: d₁ 🟰 (a₁ ⋈ b₁) → (pred₅ d₁ ↔ pred₅ (a₁ ⋈ b₁)) := by forall_elim h₅₆, (a₁ ⋈ b₁)
  have h₅₈: pred₅ d₁ ↔ pred₅ (a₁ ⋈ b₁) := by modus_ponens h₅₇, h₆
  have h₅₉: d₁ =ₗₓₗ (a₃ ⋈ b₃) := PC₀.deductive_eq_r2l h₅₈ h₅₄
  let pred₆: (Dyads.Particular U₁ U₂) → Prop := (x: Dyads.Particular U₁ U₂ ↦ d₁ =ₗₓₗ x)
  have h₆₀: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), x 🟰 y → (pred₆ x ↔ pred₆ y) := by forall_elim leibniz_eq_subs, pred₆
  have h₆₁: ∀ (y: Dyads.Particular U₁ U₂), d₃ 🟰 y → (pred₆ d₃ ↔ pred₆ y) := by forall_elim h₆₀, d₃
  have h₆₂: d₃ 🟰 (a₃ ⋈ b₃) → (pred₆ d₃ ↔ pred₆ (a₃ ⋈ b₃)) := by forall_elim h₆₁, (a₃ ⋈ b₃)
  have h₆₃: pred₆ d₃ ↔ pred₆ (a₃ ⋈ b₃) := by modus_ponens h₆₂, h₁₂
  have h₆₄: d₁ =ₗₓₗ d₃ := PC₀.deductive_eq_r2l h₆₃ h₅₉
  iterate h₆₄

-- # =ₗₓₗ Equality
def equality (U₁: Universal) (U₂: Universal): Equality (Dyads.Particular U₁ U₂) :=
  let pred: (Dyads.Particular U₁ U₂) → (Dyads.Particular U₁ U₂) → Prop := eq
  let refl: ∀ (x: Dyads.Particular U₁ U₂), pred x x := eq_refl
  let sym: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), pred x y → pred y x := eq_sym
  let trans: ∀ (x: Dyads.Particular U₁ U₂), ∀ (y: Dyads.Particular U₁ U₂), ∀ (z: Dyads.Particular U₁ U₂), pred x y ∧ pred y z → pred x z := eq_trans
  { pred := pred, refl := refl, sym := sym, trans := trans }

-- # Dyad Universal
def DyadUniversal (U₁: Universal) (U₂: Universal): Universal := {
  Particular := Dyads.Particular U₁ U₂
  eq := equality U₁ U₂
}

notation "𝐃𝐲𝐚𝐝" => DyadUniversal
notation:35 U₁:36 " ⧓ " U₂:36 => DyadUniversal U₁ U₂
abbrev Dyad U₁ U₂ := (DyadUniversal U₁ U₂).Particular
notation:35 U₁:36 " ⋈ " U₂:36 => Dyad U₁ U₂

end Dyads
end Universe
