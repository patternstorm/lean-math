import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity.Operation

namespace Logic

namespace PC₁

theorem subsume_left_totality {U: Universal} (P: CongruentUnaryPredicate U): ∀ (x: (U ↾ P).Particular), ∃ (y: U.Particular), ↑x =₍U₎ y := by forall_intro
    variable(x: (U ↾ P).Particular)
    have h₁: ∃ (y: U.Particular), ↑x =₍U₎ y := by forall_elim identity_graph.ltot, (↑x: U.Particular)
    iterate h₁

end PC₁

end Logic
