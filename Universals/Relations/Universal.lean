import Universe
import Logic
import Universals.Relations.Particular

/-!
# Relation Universal

Relations over U₁ and U₂ form their own Universal, with set equality
inherited from the underlying dyad sets. This makes relations first-class:
they can be quantified over, collected into sets, and subjected to the same
predicate/set machinery as any other particulars.
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets

-- # Relation equality is set equality over dyad sets
def equality (U₁: Universal) (U₂: Universal): Equality (Relations.Particular U₁ U₂) := Sets.equality
notation:50 A:51 " =ᵣₑₗ " B:51 => eq A B

-- # Relation Universal
def RelationUniversal (U₁: Universal) (U₂: Universal): Universal := {
  Particular := Relations.Particular U₁ U₂
  eq := equality U₁ U₂
}
notation "𝐑𝐞𝐥" => RelationUniversal
abbrev Rel U₁ U₂ := (RelationUniversal U₁ U₂).Particular

end Relations

end Universe
