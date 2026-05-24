import Universe
import Logic
import Universals.Dyads.Universal
import Universals.Dyads.Predicates.Binary.SubsumptionGraph.Properties

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsumption predicate
-- A dyad d in U₁ ⧓ U₂ is a subsume-image of d' in U₁' ⧓ U₂' iff
-- d' decomposes as (a' ⋈ b') and d equals the embedded pair (e₁ a' ⋈ e₂ b').
@[reducible] private def subsumption_graph_pred {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): U₁' ⋈ U₂' → U₁ ⋈ U₂ → Prop :=
  (d': U₁' ⋈ U₂', d: U₁ ⋈ U₂ ↦ ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =₍(U₁' ⧓ U₂')₎ (a' ⋈ b') ∧ d =₍(U₁ ⧓ U₂)₎ (e₁.embedding a' ⋈ e₂.embedding b'))

-- # Subsume graph — binary operation graph

noncomputable def subsumption_graph {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): UnaryOperationGraph (U₁' ⧓ U₂') (U₁ ⧓ U₂) :=
  let graph: CongruentBinaryPredicate (U₁' ⧓ U₂') (U₁ ⧓ U₂) := subsumption_graph_pred e₁ e₂
  let ltot := subsume_left_totality e₁ e₂
  let rdet := subsume_right_determinacy e₁ e₂
  { pred := graph.pred, cong := graph.cong, ltot := ltot, rdet := rdet }

end Dyads
end Universe
