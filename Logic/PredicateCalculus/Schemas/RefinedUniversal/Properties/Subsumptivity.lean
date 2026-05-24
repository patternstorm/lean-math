import Logic.PredicateCalculus.Schemas.SubUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Operations.Unary.Subsumption.Operation
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Operations.Unary.Subsumption.Properties.Equations
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
  -- Forward: x =₍Uₚ₎ y is x.val =₍U₎ y.val. Chain e x =₍U₎ x.val =₍U₎ y.val =₍U₎ e y.
  -- Backward: from e x =₍U₎ e y, chain x.val =₍U₎ e x =₍U₎ e y =₍U₎ y.val.
  let preserves_eq: ∀ (x: Uₚ.Particular), ∀ (y: Uₚ.Particular),
      x =₍Uₚ₎ y ↔ (subsume x =₍U₎ subsume y) := by forall_intro
    variable(x: Uₚ.Particular)
    variable(y: Uₚ.Particular)
    have h₁: subsume x =₍U₎ x.val := by forall_elim subsume_particular P, x
    have h₂: subsume y =₍U₎ y.val := by forall_elim subsume_particular P, y
    have h₃: x =₍Uₚ₎ y → (subsume x =₍U₎ subsume y) := by
      assume(h₄: x =₍Uₚ₎ y)
      -- h₄ is definitionally x.val =₍U₎ y.val
      -- e x =₍U₎ x.val ∧ x.val =₍U₎ y.val → e x =₍U₎ y.val
      have h₅: subsume x =₍U₎ x.val ∧ x.val =₍U₎ y.val := by and_intro h₁, h₄
      have h₆: subsume x =₍U₎ x.val ∧ x.val =₍U₎ y.val → subsume x =₍U₎ y.val := by forall_elim U.eq.trans, subsume x, x.val, y.val
      have h₇: subsume x =₍U₎ y.val := by modus_ponens h₆, h₅
      -- y.val =₍U₎ e y (sym of h₂)
      have h₈: subsume y =₍U₎ y.val → y.val =₍U₎ subsume y := by forall_elim U.eq.sym, subsume y, y.val
      have h₉: y.val =₍U₎ subsume y := by modus_ponens h₈, h₂
      -- e x =₍U₎ y.val ∧ y.val =₍U₎ e y → e x =₍U₎ e y
      have h₁₀: subsume x =₍U₎ y.val ∧ y.val =₍U₎ subsume y := by and_intro h₇, h₉
      have h₁₁: subsume x =₍U₎ y.val ∧ y.val =₍U₎ subsume y → subsume x =₍U₎ subsume y := by forall_elim U.eq.trans, subsume x, y.val, subsume y
      have h₁₂: subsume x =₍U₎ subsume y := by modus_ponens h₁₁, h₁₀
      iterate h₁₂
    have h₁₃: (subsume x =₍U₎ subsume y) → x =₍Uₚ₎ y := by
      assume(h₁₄: subsume x =₍U₎ subsume y)
      -- x.val =₍U₎ e x (sym of h₁)
      have h₁₅: subsume x =₍U₎ x.val → x.val =₍U₎ subsume x := by forall_elim U.eq.sym, subsume x, x.val
      have h₁₆: x.val =₍U₎ subsume x := by modus_ponens h₁₅, h₁
      -- x.val =₍U₎ e x ∧ e x =₍U₎ e y → x.val =₍U₎ e y
      have h₁₇: x.val =₍U₎ subsume x ∧ subsume x =₍U₎ subsume y := by and_intro h₁₆, h₁₄
      have h₁₈: x.val =₍U₎ subsume x ∧ subsume x =₍U₎ subsume y → x.val =₍U₎ subsume y := by forall_elim U.eq.trans, x.val, subsume x, subsume y
      have h₁₉: x.val =₍U₎ subsume y := by modus_ponens h₁₈, h₁₇
      -- x.val =₍U₎ e y ∧ e y =₍U₎ y.val → x.val =₍U₎ y.val
      have h₂₀: x.val =₍U₎ subsume y ∧ subsume y =₍U₎ y.val := by and_intro h₁₉, h₂
      have h₂₁: x.val =₍U₎ subsume y ∧ subsume y =₍U₎ y.val → x.val =₍U₎ y.val := by forall_elim U.eq.trans, x.val, subsume y, y.val
      have h₂₂: x.val =₍U₎ y.val := by modus_ponens h₂₁, h₂₀
      iterate h₂₂
    have h₂₃: x =₍Uₚ₎ y ↔ (subsume x =₍U₎ subsume y) := by iff_intro h₃, h₁₃
    iterate h₂₃
  { embedding := subsume, preserves_eq := preserves_eq }

end PC₁

end Logic
