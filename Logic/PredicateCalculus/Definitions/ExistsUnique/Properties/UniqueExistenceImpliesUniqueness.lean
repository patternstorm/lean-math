import Logic.PredicateCalculus.Definitions.ExistsUnique.Definition
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND


-- # Unique existence implies uniqueness
--
-- The "uniqueness" face of unique existence: any two particulars satisfying
-- `P` must be equal in `U`. Useful when a proof needs to collapse two
-- witnesses to the same value without separately handling the existence
-- part (e.g., right-determinacy of an operation graph whose codomain has
-- a uniqueness property baked in).
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem unique_existence_implies_uniqueness {U: Universal} {P: U.Particular → Prop}:
    (∃!₍U₎ (x: U.Particular), P x) → ∀ (b: U.Particular), ∀ (c: U.Particular), P b ∧ P c → b =₍U₎ c := by
  assume(h₁: ∃!₍U₎ (x: U.Particular), P x)
  have h₂: (∃!₍U₎ (x: U.Particular), P x) ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x)) := by forall_elim exists_unique_def, U, (x: U.Particular ↦ P x)
  have h₃: ∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x) := PC₀.deductive_eq_l2r h₂ h₁
  have ⟨(a: U.Particular), (h₄: P a ∧ (∀ (y: U.Particular), P y → y =₍U₎ a))⟩ := exists_elim h₃
  have h₅: ∀ (y: U.Particular), P y → y =₍U₎ a := by and_elim h₄
  have h₆: ∀ (b: U.Particular), ∀ (c: U.Particular), P b ∧ P c → b =₍U₎ c := by forall_intro
    variable(b: U.Particular)
    variable(c: U.Particular)
    assume(h₆₁: P b ∧ P c)
    have h₆₂: P b := by and_elim h₆₁
    have h₆₃: P c := by and_elim h₆₁
    have h₆₄: P b → b =₍U₎ a := by forall_elim h₅, b
    have h₆₅: b =₍U₎ a := by modus_ponens h₆₄, h₆₂
    have h₆₆: P c → c =₍U₎ a := by forall_elim h₅, c
    have h₆₇: c =₍U₎ a := by modus_ponens h₆₆, h₆₃
    have h₆₈: c =₍U₎ a → a =₍U₎ c := by forall_elim U.eq.sym, c, a
    have h₆₉: a =₍U₎ c := by modus_ponens h₆₈, h₆₇
    have h₆₁₀: b =₍U₎ a ∧ a =₍U₎ c := by and_intro h₆₅, h₆₉
    have h₆₁₁: b =₍U₎ a ∧ a =₍U₎ c → b =₍U₎ c := by forall_elim U.eq.trans, b, a, c
    have h₆₁₂: b =₍U₎ c := by modus_ponens h₆₁₁, h₆₁₀
    iterate h₆₁₂
  iterate h₆


end PC₁

end Logic
