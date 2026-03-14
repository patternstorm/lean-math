import Universe
import Logic
import Universals.Sets
import Universals.Dyads

/-!
# Relations — Particular

A relation between U₁ and U₂ is a set of dyads. This is a type alias,
not a new type — relations inherit all set operations for free.

The `relation_from` constructor builds a relation from a congruent binary
predicate using uncurry: the curried predicate P a b becomes the unary
predicate (uncurry P) on dyads a ⋈ b.
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads

-- # Relations are sets of dyads
protected def Particular (U₁: Universal) (U₂: Universal): Type := Set (U₁ ⧓ U₂)

-- # Relation constructor
-- Builds a relation from a congruent binary predicate.
-- The curried predicate P a b is converted to a unary predicate on dyads
-- via uncurry, and congruence is derived from P's congruence in both
-- arguments and the relatum-wise definition of dyad equality.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-07
noncomputable def relation_from {U₁: Universal} {U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂): Relations.Particular U₁ U₂ :=
  let R: U₁.Particular → U₂.Particular → Prop := (a: U₁.Particular, b: U₂.Particular ↦ (P.pred a).pred b)
  let pred: U₁ ⋈ U₂ → Prop := uncurry R
  let cong: ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂), d₁ =ₗₓₗ d₂ → (pred d₁ ↔ pred d₂) := by forall_intro
    variable(d₁: U₁ ⋈ U₂)
    variable(d₂: U₁ ⋈ U₂)
    assume(h₁: d₁ =ₗₓₗ d₂)
    -- Decompose d₁ via exhaustiveness
    have h₂: ∃ (a₁: U₁.Particular), ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁) := by forall_elim exhaustiveness, d₁
    have ⟨(a₁: U₁.Particular), (h₃: ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₂
    have ⟨(b₁: U₂.Particular), (h₄: d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₃
    -- Decompose d₂ via exhaustiveness
    have h₅: ∃ (a₂: U₁.Particular), ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂) := by forall_elim exhaustiveness, d₂
    have ⟨(a₂: U₁.Particular), (h₆: ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₅
    have ⟨(b₂: U₂.Particular), (h₇: d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₆
    -- Transfer d₁ =ₗₓₗ d₂ to (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) via Leibniz substitution
    let pred₁: U₁ ⋈ U₂ → Prop := (x: U₁ ⋈ U₂ ↦ x =ₗₓₗ d₂)
    have h₈: ∀ (x: U₁ ⋈ U₂), ∀ (y: U₁ ⋈ U₂), x 🟰 y → (pred₁ x ↔ pred₁ y) := by forall_elim leibniz_eq_subs, pred₁
    have h₉: ∀ (y: U₁ ⋈ U₂), d₁ 🟰 y → (pred₁ d₁ ↔ pred₁ y) := by forall_elim h₈, d₁
    have h₁₀: d₁ 🟰 (a₁ ⋈ b₁) → (pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁)) := by forall_elim h₉, (a₁ ⋈ b₁)
    have h₁₁: pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁) := by modus_ponens h₁₀, h₄
    have h₁₂: (a₁ ⋈ b₁) =ₗₓₗ d₂ := PC₀.deductive_eq_l2r h₁₁ h₁
    let pred₂: U₁ ⋈ U₂ → Prop := (x: U₁ ⋈ U₂ ↦ (a₁ ⋈ b₁) =ₗₓₗ x)
    have h₁₃: ∀ (x: U₁ ⋈ U₂), ∀ (y: U₁ ⋈ U₂), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
    have h₁₄: ∀ (y: U₁ ⋈ U₂), d₂ 🟰 y → (pred₂ d₂ ↔ pred₂ y) := by forall_elim h₁₃, d₂
    have h₁₅: d₂ 🟰 (a₂ ⋈ b₂) → (pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂)) := by forall_elim h₁₄, (a₂ ⋈ b₂)
    have h₁₆: pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂) := by modus_ponens h₁₅, h₇
    have h₁₇: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₁₆ h₁₂
    -- Extract relata equalities via eq_def
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
    -- Transfer pred to constructor form via Leibniz substitution
    let lpred: U₁ ⋈ U₂ → Prop := (x: U₁ ⋈ U₂ ↦ pred x)
    have h₂₅: ∀ (x: U₁ ⋈ U₂), ∀ (y: U₁ ⋈ U₂), x 🟰 y → (lpred x ↔ lpred y) := by forall_elim leibniz_eq_subs, lpred
    have h₂₆: ∀ (y: U₁ ⋈ U₂), d₁ 🟰 y → (lpred d₁ ↔ lpred y) := by forall_elim h₂₅, d₁
    have h₂₇: d₁ 🟰 (a₁ ⋈ b₁) → (pred d₁ ↔ pred (a₁ ⋈ b₁)) := by forall_elim h₂₆, (a₁ ⋈ b₁)
    have h₂₈: pred d₁ ↔ pred (a₁ ⋈ b₁) := by modus_ponens h₂₇, h₄
    have h₂₉: ∀ (y: U₁ ⋈ U₂), d₂ 🟰 y → (lpred d₂ ↔ lpred y) := by forall_elim h₂₅, d₂
    have h₃₀: d₂ 🟰 (a₂ ⋈ b₂) → (pred d₂ ↔ pred (a₂ ⋈ b₂)) := by forall_elim h₂₉, (a₂ ⋈ b₂)
    have h₃₁: pred d₂ ↔ pred (a₂ ⋈ b₂) := by modus_ponens h₃₀, h₇
    -- Unfold pred at constructor form via uncurry_def
    have h₃₂: ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), (uncurry R) (a ⋈ b) ↔ R a b := uncurry_def R
    have h₃₃: ∀ (b: U₂.Particular), (uncurry R) (a₁ ⋈ b) ↔ R a₁ b := by forall_elim h₃₂, a₁
    have h₃₄: (uncurry R) (a₁ ⋈ b₁) ↔ R a₁ b₁ := by forall_elim h₃₃, b₁
    have h₃₅: ∀ (b: U₂.Particular), (uncurry R) (a₂ ⋈ b) ↔ R a₂ b := by forall_elim h₃₂, a₂
    have h₃₆: (uncurry R) (a₂ ⋈ b₂) ↔ R a₂ b₂ := by forall_elim h₃₅, b₂
    -- Binary congruence: first argument (a₁ =₍U₁₎ a₂)
    have h₃₇: ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), a₁ =₍U₁₎ y → ((P.pred a₁).pred z ↔ (P.pred y).pred z) := by forall_elim P.cong, a₁
    have h₃₈: ∀ (z: U₂.Particular), a₁ =₍U₁₎ a₂ → ((P.pred a₁).pred z ↔ (P.pred a₂).pred z) := by forall_elim h₃₇, a₂
    have h₃₉: a₁ =₍U₁₎ a₂ → ((P.pred a₁).pred b₁ ↔ (P.pred a₂).pred b₁) := by forall_elim h₃₈, b₁
    have h₄₀: (P.pred a₁).pred b₁ ↔ (P.pred a₂).pred b₁ := by modus_ponens h₃₉, h₂₃
    -- Binary congruence: second argument (b₁ =₍U₂₎ b₂)
    have h₄₁: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((P.pred a₂).pred b₁ ↔ (P.pred a₂).pred y) := by forall_elim (P.pred a₂).cong, b₁
    have h₄₂: b₁ =₍U₂₎ b₂ → ((P.pred a₂).pred b₁ ↔ (P.pred a₂).pred b₂) := by forall_elim h₄₁, b₂
    have h₄₃: (P.pred a₂).pred b₁ ↔ (P.pred a₂).pred b₂ := by modus_ponens h₄₂, h₂₄
    -- Chain: pred d₁ → pred d₂
    have h₄₄: pred d₁ → pred d₂ := by
      assume(h₄₄₁: pred d₁)
      have h₄₄₂: pred (a₁ ⋈ b₁) := PC₀.deductive_eq_l2r h₂₈ h₄₄₁
      have h₄₄₃: (P.pred a₁).pred b₁ := PC₀.deductive_eq_l2r h₃₄ h₄₄₂
      have h₄₄₄: (P.pred a₂).pred b₁ := PC₀.deductive_eq_l2r h₄₀ h₄₄₃
      have h₄₄₅: (P.pred a₂).pred b₂ := PC₀.deductive_eq_l2r h₄₃ h₄₄₄
      have h₄₄₆: pred (a₂ ⋈ b₂) := PC₀.deductive_eq_r2l h₃₆ h₄₄₅
      have h₄₄₇: pred d₂ := PC₀.deductive_eq_r2l h₃₁ h₄₄₆
      iterate h₄₄₇
    -- Chain: pred d₂ → pred d₁
    have h₄₅: pred d₂ → pred d₁ := by
      assume(h₄₅₁: pred d₂)
      have h₄₅₂: pred (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₃₁ h₄₅₁
      have h₄₅₃: (P.pred a₂).pred b₂ := PC₀.deductive_eq_l2r h₃₆ h₄₅₂
      have h₄₅₄: (P.pred a₂).pred b₁ := PC₀.deductive_eq_r2l h₄₃ h₄₅₃
      have h₄₅₅: (P.pred a₁).pred b₁ := PC₀.deductive_eq_r2l h₄₀ h₄₅₄
      have h₄₅₆: pred (a₁ ⋈ b₁) := PC₀.deductive_eq_r2l h₃₄ h₄₅₅
      have h₄₅₇: pred d₁ := PC₀.deductive_eq_r2l h₂₈ h₄₅₆
      iterate h₄₅₇
    have h₄₆: pred d₁ ↔ pred d₂ := by iff_intro h₄₄, h₄₅
    iterate h₄₆
  { pred := pred,
    cong := cong }

end Relations

end Universe
