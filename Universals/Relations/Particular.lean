import Universe
import Logic
import Universals.Sets
import Universals.Dyads

/-!
# Relations — Particular

Relations are congruent binary predicates over two Universals.
Two relations are equal iff their predicates are logically equivalent.-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁

-- # Relations are "created" by binary predicates
protected abbrev Particular (U₁: Universal) (U₂: Universal): Type := CongruentBinaryPredicate U₁ U₂

-- # `Relation` equality predicate
axiom eq: Relations.Particular U₁ U₂ → Relations.Particular U₁ U₂ → Prop

-- ## Two `Relations` are equal if their predicates are logically equivalent.
axiom eq_def: ∀ (R₁: Relations.Particular U₁ U₂), ∀ (R₂: Relations.Particular U₁ U₂), eq R₁ R₂ ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), R₁ x y ↔ R₂ x y

end Relations

end Universe
