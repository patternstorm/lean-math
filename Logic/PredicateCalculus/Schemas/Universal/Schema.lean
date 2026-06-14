import Logic.PredicateCalculus.Schemas.Equality.Schema

namespace Logic

namespace PC₁

structure Universal where
  Particular: Type
  eq: Equality Particular

end PC₁

end Logic
