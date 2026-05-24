import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph
import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity.Operation
import Logic.PredicateCalculus.Definitions
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Predicates.SubsumptionGraph.Properties

namespace Logic

namespace PC₁

-- # Subsume — the embedding operation from a refined universal into its parent

private def subsumption_graph_pred{U: Universal} (P: CongruentUnaryPredicate U)
  (a: (U ↾ P).Particular) (b: U.Particular): Prop := b =₍U₎ a.val


-- Because `x₁ =₍Uₚ₎ x₂` is definitionally `x₁.val =₍U₎ x₂.val`, each graph
-- obligation (`cong`, `ltot`, `rdet`) reduces to a single instantiation of the
-- corresponding `identity_graph` field at `x.val` (and `x₁.val, x₂.val` for `cong`):
--
-- - `cong`  ← `identity_graph.cong`  applied to `x₁.val, x₂.val, z`
-- - `ltot`  ← `identity_graph.ltot`  applied to `x.val`
-- - `rdet`  ← `identity_graph.rdet`  applied to `x.val, y₁, y₂`
--
-- Proof by Claude Opus 4.7 Max, 2026-05-02
noncomputable def subsumption_graph {U: Universal} (P: CongruentUnaryPredicate U): UnaryOperationGraph (U ↾ P) U :=
  let Uₚ: Universal := U ↾ P
  let pred: Uₚ.Particular → CongruentUnaryPredicate U := (x: Uₚ.Particular ↦ equal_to x.val)
  -- Outer congruence: reuse identity_graph.cong at (x₁.val, x₂.val, z)
  -- the antecedent `x₁ =₍Uₚ₎ x₂` is definitionally `x₁.val =₍U₎ x₂.val`.
  let cong: ∀ (x₁: Uₚ.Particular), ∀ (x₂: Uₚ.Particular), ∀ (z: U.Particular), x₁ =₍Uₚ₎ x₂ → (x₁.val =₍U₎ z ↔ x₂.val =₍U₎ z) := by forall_intro
    variable(x₁: Uₚ.Particular)
    variable(x₂: Uₚ.Particular)
    variable(z: U.Particular)
    assume(h₁: x₁ =₍Uₚ₎ x₂)
    have h₂: x₁.val =₍U₎ x₂.val → (x₁.val =₍U₎ z ↔ x₂.val =₍U₎ z) := by forall_elim identity_graph.cong, (x₁.val: U.Particular), x₂.val, z
    have h₃: x₁.val =₍U₎ z ↔ x₂.val =₍U₎ z := by modus_ponens h₂, h₁
    iterate h₃
  let ltot: ∀ (x: Uₚ.Particular), ∃ (y: U.Particular), x.val =₍U₎ y := subsume_left_totality P
  let rdet: ∀ (x: Uₚ.Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), x.val =₍U₎ y₁ ∧ x.val =₍U₎ y₂ → y₁ =₍U₎ y₂ := subsume_right_determinacy P
  { pred := pred, cong := cong, ltot := ltot, rdet := rdet }


end PC₁

end Logic
