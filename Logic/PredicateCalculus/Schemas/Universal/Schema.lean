import Logic.PredicateCalculus.Schemas.Equality.Schema

namespace Logic

namespace PC₁

structure Universal where
  Particular: Type
  eq: Equality Particular

def universal_eq (U : Universal) : U.Particular → U.Particular → Prop := U.eq.pred
notation:50 a:51 " =₍" U:51 "₎ " b:51 => universal_eq U a b

end PC₁

end Logic
