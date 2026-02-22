import Universe

import Logic

/-!
# Sets — Particular

The abstract data type specification for sets.
Sets are congruent unary predicates over a Universal. The equality of sets is extensional:
two sets are equal iff their predicates are logically equivalent.
-/

namespace Universe

open Logic
open Logic.PC₁


namespace Sets

-- # `Sets`are "represented" by `Unary Predicates`
def Particular (U: Universal): Type := CongruentUnaryPredicate U
def Set (U: Universal): Type := Particular U

-- # `Set` equality predicate
axiom eq: Set U → Set U → Prop
notation:50 A:51 " =ₛₑₜ " B:51 => eq A B

-- ## Two `Sets` are equal if their predicates are logically equivalent.
axiom eq_def: ∀ (S₁: Set U), ∀ (S₂: Set U), S₁ =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), S₁.pred x ↔ S₂.pred x

end Sets

end Universe
