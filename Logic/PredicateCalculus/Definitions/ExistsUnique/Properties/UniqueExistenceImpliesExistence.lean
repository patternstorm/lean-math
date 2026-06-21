import Logic.PredicateCalculus.Definitions.ExistsUnique.Definition
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND


-- # Unique existence implies existence
--
-- The "only if" direction of unique existence: dropping the uniqueness
-- conjunct yields plain existence. Useful when a proof needs a witness but
-- not the uniqueness clause that came with it (e.g., extracting the member
-- of a singleton set without separately tracking that it's the unique one).
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem unique_existence_implies_existence {U: Universal} {P: U.Particular → Prop}: (∃!₍U₎ (x: U.Particular), P x) → ∃ (x: U.Particular), P x := by
  assume(h₀: ∃!₍U₎ (x: U.Particular), P x)
  have h₁: (∃!₍U₎ (x: U.Particular), P x) ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x)) := by forall_elim exists_unique_def, U, (x: U.Particular ↦ P x)
  have h₂: ∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x) := PC₀.deductive_eq_l2r h₁ h₀
  have ⟨(a: U.Particular), (h₃: P a ∧ (∀ (y: U.Particular), P y → y =₍U₎ a))⟩ := exists_elim h₂
  have h₄: P a := by and_elim h₃
  have h₅: ∃ (x: U.Particular), P x := by exists_intro h₄, a
  iterate h₅


end PC₁

end Logic
