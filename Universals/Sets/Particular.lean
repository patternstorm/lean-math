import Universe

import Logic

/-!
# Sets — Particular

Sets are congruent unary predicates over a Universal.
Two sets are equal iff their predicates are logically equivalent.
-/

namespace Universe

open Logic
open Logic.PC₁


namespace Sets

-- # `Sets`are "created" by `Unary Predicates`
protected abbrev Particular (U: Universal): Type := CongruentUnaryPredicate U

-- # `Set` equality predicate
axiom eq: Sets.Particular U → Sets.Particular U → Prop

-- ## Two `Sets` are equal if their predicates are logically equivalent.
axiom eq_def: ∀ (S₁: Sets.Particular U), ∀ (S₂: Sets.Particular U), eq S₁ S₂ ↔ ∀ (x: U.Particular), S₁.pred x ↔ S₂.pred x

end Sets

end Universe
