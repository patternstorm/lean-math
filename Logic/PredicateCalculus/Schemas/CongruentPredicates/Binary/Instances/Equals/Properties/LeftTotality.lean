import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals.Instance
import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

-- # universal equality left totality — every particular is at least equal to another particular, i.e. itself

-- Proof by Claude Opus 4.7 Max, 2026-05-02
theorem equals_left_totality {U: Universal}: ∀ (x: U.Particular), ∃ (y: U.Particular), x =₍U₎ y := by forall_intro
  variable(a: U.Particular)
  have h₁: a =₍U₎ a := by forall_elim U.eq.refl, a
  have h₂: ∃ (y: U.Particular), a =₍U₎ y := by exists_intro h₁, a
  iterate h₂

end PC₁

end Logic
