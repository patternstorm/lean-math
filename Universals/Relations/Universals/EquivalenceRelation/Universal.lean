import Universe
import Logic
import Universals.Relations.Universal
import Universals.Relations.Predicates.Unary.EquivalenceRelation.Predicate

namespace Universe

namespace Relations

open Logic
open Logic.PC₁

-- # Equivalence Relation Universal
-- The sub-universal of Rel U U whose particulars are equivalence relations.
-- A particular of this universal is a relation R bundled with a proof that
-- is_reflexive R ∧ is_symmetric R ∧ is_transitive R.
def EqRelUniversal (U: Universal): Universal := sub_universal (𝐑𝐞𝐥 U U) (equivalence_relation_predicate U)
notation "𝐄𝐪𝐑𝐞𝐥" => EqRelUniversal

def EqRel (U: Universal): Type := (𝐄𝐪𝐑𝐞𝐥 U).Particular

end Relations

end Universe
