import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Predicates.SubsumptionGraph

namespace Logic

namespace PC₁


-- The subsume operation symbol: the canonical injection (U ↾ P) → U.
-- Defining axiom: subsume_sym P x =₍U₎ y ↔ ↑x =₍U₎ y.
axiom subsume_sym {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P).Particular → U.Particular
axiom subsume_def {U: Universal} (P: CongruentUnaryPredicate U): ∀ (x: (U ↾ P).Particular), ∀ (y: U.Particular),
    (subsume_sym P x =₍U₎ y) ↔ ((subsumption_graph P).pred x).pred y

noncomputable def subsume {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P) ⟴ U :=
  { graph := subsumption_graph P, op := subsume_sym P, «def» := subsume_def P }

end PC₁

end Logic
