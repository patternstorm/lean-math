import Logic.PredicateCalculus.Schemas.RefinedUniversal.Properties.Subsumptivity

namespace Logic

namespace PC₁

-- Test: coercion from (U ↾ P).Particular to U.Particular via the subsume operation.

variable {U: Universal} {P: CongruentUnaryPredicate U}
variable (x: (U ↾ P).Particular)

-- Explicit use of the subsume operation.
noncomputable def via_subsume: U.Particular := subsume P x

-- Implicit coercion: Lean should insert (is_subuniversal P).embedding x automatically.
noncomputable def via_coe: U.Particular := x

-- Both should yield the same result propositionally.
theorem coe_eq_subsume: via_coe x =₍U₎ via_subsume x := by
  iterate (by forall_elim U.eq.refl, (subsume P x))

end PC₁

end Logic
