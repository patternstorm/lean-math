import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity.Operation

namespace Logic

namespace PC₁

theorem subsume_right_determinacy {U: Universal} (P: CongruentUnaryPredicate U): ∀ (x: (U ↾ P).Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), x.val =₍U₎ y₁ ∧ x.val =₍U₎ y₂ → y₁ =₍U₎ y₂ := by forall_intro
    variable(x: (U ↾ P).Particular)
    variable(y₁: U.Particular)
    variable(y₂: U.Particular)
    have h₁: x.val =₍U₎ y₁ ∧ x.val =₍U₎ y₂ → y₁ =₍U₎ y₂ := by forall_elim identity_graph.rdet, (x.val: U.Particular), y₁, y₂
    iterate h₁


end PC₁

end Logic
