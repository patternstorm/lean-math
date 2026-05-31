import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity.Operation
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- # Invariance of identity
--
-- Every element of U is fixed by the identity operation: `identity z =₍U₎ z`.
-- Derived from `identity_def` at (z, z), which reduces to
--   `identity z =₍U₎ z ↔ z =₍U₎ z`,
-- whose right-hand side holds by reflexivity of =₍U₎.
--
-- Proof by Claude Opus 4.7, 2026-04-19
theorem identity_invariance: ∀ (z: U.Particular), identity z =₍U₎ z := by forall_intro
  variable(z: U.Particular)
  have h₁: ∀ (w: U.Particular), (identity z =₍U₎ w) ↔ identity.graph.pred z w := by forall_elim identity.«def», z
  have h₂: (identity z =₍U₎ z) ↔ identity.graph.pred z z := by forall_elim h₁, z
  have h₃: z =₍U₎ z := by forall_elim U.eq.refl, z
  have h₄: identity z =₍U₎ z := PC₀.deductive_eq_r2l h₂ h₃
  iterate h₄

end PC₁

end Logic
