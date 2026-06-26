import Logic.PredicateCalculus.Definitions.ExistsUnique.Definition
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND


-- # Unique existence intro
--
-- The "introduction" direction of unique existence: from a witness `w`, a
-- proof that `w` satisfies `P`, and a proof that any `P`-satisfier equals
-- `w`, build `∃!₍U₎ x, P x`. Inverse of `unique_existence_implies_existence`
-- and `unique_existence_implies_uniqueness` combined.
--
-- The witness-relative uniqueness form `∀ y, P y → y =₍U₎ w` is what
-- `exists_unique_def` natively unfolds to — consumers that proved uniqueness
-- against a specific candidate (the typical pattern when constructing a
-- singleton from an explicit element) can pack the result in one step.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-26
theorem unique_existence_intro {U: Universal} {P: U.Particular → Prop} (a: U.Particular) (h₁: P a) (h₂: ∀ (y: U.Particular), P y → y =₍U₎ a):
  ∃!₍U₎ (x: U.Particular), P x := by
    have h₃: P a ∧ (∀ (y: U.Particular), P y → y =₍U₎ a) := by and_intro h₁, h₂
    have h₄: ∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x) := by exists_intro h₃, a
    have h₅: (∃!₍U₎ (x: U.Particular), P x) ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x)) := by forall_elim exists_unique_def, U, (x: U.Particular ↦ P x)
    have h₆: ∃!₍U₎ (x: U.Particular), P x := PC₀.deductive_eq_r2l h₅ h₄
    iterate h₆


end PC₁

end Logic
