import Logic.PredicateCalculus.Schemas.SubUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Operations.Unary.Subsume.Operation
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Operations.Unary.Subsume.Properties.Equations
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- # Subsumptivity — a refined universal U ↾ P is a sub-universal of U.
--
-- The proof derives `preserves_eq` from the defining axiom of the `subsume`
--
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-12
noncomputable instance subsumptivity {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P) <: U :=
  let Uₚ: Universal := U ↾ P
  let subsume: (U ↾ P) ⟴ U := subsume P
  -- preserves_eq: x =₍Uₚ₎ y ↔ e x =₍U₎ e y
  -- Forward: x =₍Uₚ₎ y is ↑x =₍U₎ ↑y. Chain e x =₍U₎ ↑x =₍U₎ ↑y =₍U₎ e y.
  -- Backward: from e x =₍U₎ e y, chain ↑x =₍U₎ e x =₍U₎ e y =₍U₎ ↑y.
  let preserves_eq: ∀ (x: Uₚ.Particular), ∀ (y: Uₚ.Particular),
      x =₍Uₚ₎ y ↔ (subsume x =₍U₎ subsume y) := by forall_intro
    variable(x: Uₚ.Particular)
    variable(y: Uₚ.Particular)
    have h₁: subsume x =₍U₎ ↑x := by forall_elim subsume_particular P, x
    have h₂: subsume y =₍U₎ ↑y := by forall_elim subsume_particular P, y
    have h₃: x =₍Uₚ₎ y → (subsume x =₍U₎ subsume y) := by
      assume(h₄: x =₍Uₚ₎ y)
      -- h₄ is definitionally ↑x =₍U₎ ↑y
      -- e x =₍U₎ ↑x ∧ ↑x =₍U₎ ↑y → e x =₍U₎ ↑y
      have h₅: subsume x =₍U₎ ↑x ∧ ↑x =₍U₎ ↑y := by and_intro h₁, h₄
      have h₆: subsume x =₍U₎ ↑x ∧ ↑x =₍U₎ ↑y → subsume x =₍U₎ ↑y := by forall_elim U.eq.trans, subsume x, ↑x, ↑y
      have h₇: subsume x =₍U₎ ↑y := by modus_ponens h₆, h₅
      -- ↑y =₍U₎ e y (sym of h₂)
      have h₈: subsume y =₍U₎ ↑y → ↑y =₍U₎ subsume y := by forall_elim U.eq.sym, subsume y, ↑y
      have h₉: ↑y =₍U₎ subsume y := by modus_ponens h₈, h₂
      -- e x =₍U₎ ↑y ∧ ↑y =₍U₎ e y → e x =₍U₎ e y
      have h₁₀: subsume x =₍U₎ ↑y ∧ ↑y =₍U₎ subsume y := by and_intro h₇, h₉
      have h₁₁: subsume x =₍U₎ ↑y ∧ ↑y =₍U₎ subsume y → subsume x =₍U₎ subsume y := by forall_elim U.eq.trans, subsume x, ↑y, subsume y
      have h₁₂: subsume x =₍U₎ subsume y := by modus_ponens h₁₁, h₁₀
      iterate h₁₂
    have h₁₃: (subsume x =₍U₎ subsume y) → x =₍Uₚ₎ y := by
      assume(h₁₄: subsume x =₍U₎ subsume y)
      -- ↑x =₍U₎ e x (sym of h₁)
      have h₁₅: subsume x =₍U₎ ↑x → ↑x =₍U₎ subsume x := by forall_elim U.eq.sym, subsume x, ↑x
      have h₁₆: ↑x =₍U₎ subsume x := by modus_ponens h₁₅, h₁
      -- ↑x =₍U₎ e x ∧ e x =₍U₎ e y → ↑x =₍U₎ e y
      have h₁₇: ↑x =₍U₎ subsume x ∧ subsume x =₍U₎ subsume y := by and_intro h₁₆, h₁₄
      have h₁₈: ↑x =₍U₎ subsume x ∧ subsume x =₍U₎ subsume y → ↑x =₍U₎ subsume y := by forall_elim U.eq.trans, ↑x, subsume x, subsume y
      have h₁₉: ↑x =₍U₎ subsume y := by modus_ponens h₁₈, h₁₇
      -- ↑x =₍U₎ e y ∧ e y =₍U₎ ↑y → ↑x =₍U₎ ↑y
      have h₂₀: ↑x =₍U₎ subsume y ∧ subsume y =₍U₎ ↑y := by and_intro h₁₉, h₂
      have h₂₁: ↑x =₍U₎ subsume y ∧ subsume y =₍U₎ ↑y → ↑x =₍U₎ ↑y := by forall_elim U.eq.trans, ↑x, subsume y, ↑y
      have h₂₂: ↑x =₍U₎ ↑y := by modus_ponens h₂₁, h₂₀
      iterate h₂₂
    have h₂₃: x =₍Uₚ₎ y ↔ (subsume x =₍U₎ subsume y) := by iff_intro h₃, h₁₃
    iterate h₂₃
  { embedding := subsume, preserves_eq := preserves_eq }

end PC₁

end Logic
