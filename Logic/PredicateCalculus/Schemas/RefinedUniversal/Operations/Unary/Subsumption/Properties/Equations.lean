import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Operations.Unary.Subsumption.Operation

namespace Logic

namespace PC₁

theorem subsume_particular {U: Universal} (P: CongruentUnaryPredicate U): ∀ (z: (U ↾ P).Particular), subsume P z =₍U₎ z.val := by forall_intro
  let Uₚ: Universal := U ↾ P
  let subsume: (U ↾ P) ⟴ U := subsume P
  variable(z: Uₚ.Particular)
  have h₁: ∀ (w: U.Particular), (subsume z =₍U₎ w) ↔ subsume.graph.pred z w := by forall_elim subsume.«def», z
  have h₂: (subsume z =₍U₎ z.val) ↔ subsume.graph.pred z z.val := by forall_elim h₁, z.val
  have h₃: z.val =₍U₎ z.val := by forall_elim U.eq.refl, z.val
  have h₄: subsume z =₍U₎ z.val := PC₀.deductive_eq_r2l h₂ h₃
  iterate h₄

end PC₁
end Logic
