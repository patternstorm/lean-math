import Logic.PredicateCalculus.Schemas.Universal.Schema

namespace Logic

namespace PC₁

structure CongruentUnaryPredicate (U: Universal): Type where
  pred: U.Particular → Prop
  cong: ∀ (x: U.Particular), ∀ (y: U.Particular), U.eq x y → (pred x ↔ pred y)

class CongruentUnary (U: Universal) (P: U.Particular → Prop) where
  cong: ∀ (x: U.Particular), ∀ (y: U.Particular), U.eq x y → (P x ↔ P y)

-- Coercion: when Lean expects a CongruentUnaryPredicate U and finds a predicate P,
-- it coerces automatically if CongruentUnary U P is synthesizable.
-- Key invariant: coe.pred = P definitionally.
instance congruent_coercion {U: Universal} {P: U.Particular → Prop}
    [c: CongruentUnary U P]: CoeDep (U.Particular → Prop) P (CongruentUnaryPredicate U) where
  coe := { pred := P, cong := c.cong }

-- Bridge: a CongruentUnaryPredicate's .pred field is itself congruent.
-- Low priority so structural instances (conjunction, existential, etc.) take precedence.
instance (priority := 50) congruent_pred {U: Universal} {R: CongruentUnaryPredicate U}:
    CongruentUnary U R.pred where
  cong := R.cong

-- # `CoeFun`: lets us write `P x` instead of `P.pred x`.
-- A `CongruentUnaryPredicate U` is callable as a 1-argument function returning
-- the proposition "x satisfies P". The `.pred` projection becomes implicit.
instance {U: Universal}: CoeFun (CongruentUnaryPredicate U) (fun _ => U.Particular → Prop) where
  coe P := P.pred

end PC₁

end Logic
