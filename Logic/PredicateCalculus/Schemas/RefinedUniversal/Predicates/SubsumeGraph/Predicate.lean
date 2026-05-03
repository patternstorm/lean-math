import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph
import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity.Operation
import Logic.PredicateCalculus.Definitions
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Predicates.SubsumeGraph.Properties

namespace Logic

namespace PC₁

-- # Subsume — the embedding operation from a refined universal into its parent

private def subsume_graph_pred{U: Universal} (P: CongruentUnaryPredicate U)
  (a: (U ↾ P).Particular) (b: U.Particular): Prop := b =₍U₎ ↑a


-- Because `x₁ =₍Uₚ₎ x₂` is definitionally `↑x₁ =₍U₎ ↑x₂`, each graph
-- obligation (`cong`, `ltot`, `rdet`) reduces to a single instantiation of the
-- corresponding `identity_graph` field at `↑x` (and `↑x₁, ↑x₂` for `cong`):
--
-- - `cong`  ← `identity_graph.cong`  applied to `↑x₁, ↑x₂, z`
-- - `ltot`  ← `identity_graph.ltot`  applied to `↑x`
-- - `rdet`  ← `identity_graph.rdet`  applied to `↑x, y₁, y₂`
--
-- Proof by Claude Opus 4.7 Max, 2026-05-02
noncomputable def subsume_graph {U: Universal} (P: CongruentUnaryPredicate U): UnaryOperationGraph (U ↾ P) U :=
  let Uₚ: Universal := U ↾ P
  let pred: Uₚ.Particular → CongruentUnaryPredicate U := (x: Uₚ.Particular ↦ equal_to ↑x)
  -- Outer congruence: reuse identity_graph.cong at (↑x₁, ↑x₂, z)
  -- the antecedent `x₁ =₍Uₚ₎ x₂` is definitionally `↑x₁ =₍U₎ ↑x₂`.
  let cong: ∀ (x₁: Uₚ.Particular), ∀ (x₂: Uₚ.Particular), ∀ (z: U.Particular), x₁ =₍Uₚ₎ x₂ → (↑x₁ =₍U₎ z ↔ ↑x₂ =₍U₎ z) := by forall_intro
    variable(x₁: Uₚ.Particular)
    variable(x₂: Uₚ.Particular)
    variable(z: U.Particular)
    assume(h₁: x₁ =₍Uₚ₎ x₂)
    have h₂: ↑x₁ =₍U₎ ↑x₂ → (↑x₁ =₍U₎ z ↔ ↑x₂ =₍U₎ z) := by forall_elim identity_graph.cong, (↑x₁: U.Particular), ↑x₂, z
    have h₃: ↑x₁ =₍U₎ z ↔ ↑x₂ =₍U₎ z := by modus_ponens h₂, h₁
    iterate h₃
  let ltot: ∀ (x: Uₚ.Particular), ∃ (y: U.Particular), ↑x =₍U₎ y := subsume_left_totality P
  let rdet: ∀ (x: Uₚ.Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), ↑x =₍U₎ y₁ ∧ ↑x =₍U₎ y₂ → y₁ =₍U₎ y₂ := subsume_right_determinacy P
  { pred := pred, cong := cong, ltot := ltot, rdet := rdet }


end PC₁

end Logic
