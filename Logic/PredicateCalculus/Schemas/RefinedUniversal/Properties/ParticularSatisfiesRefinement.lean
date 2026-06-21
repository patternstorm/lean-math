import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁


-- # Particulars of a refined universal satisfy the refinement predicate
--
-- By construction, a particular of `U ↾ P` is an element of `U` together
-- with a proof that it satisfies `P`. This theorem exposes that proof as
-- a named ND-accessible fact, so consumers reason via `forall_elim` instead
-- of reaching into the underlying `Subtype.property` projection.
--
-- The proof itself uses `a.property` once, at the framework level — the
-- same boundary at which `refined_universal` uses Lean's `fun`/Subtype
-- machinery (justified as logic infrastructure, not mathematics; see
-- `RefinedUniversal/Schema.lean`). Consumers never touch `.property`.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
theorem particular_satisfies_refinement {U: Universal} {P: CongruentUnaryPredicate U}: ∀ (x: (U ↾ P).Particular), P.pred x.val := by forall_intro
  variable(a: (U ↾ P).Particular)
  have h₁: P.pred a.val := a.property
  iterate h₁


end PC₁

end Logic
