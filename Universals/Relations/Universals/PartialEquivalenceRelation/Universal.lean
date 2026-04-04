import Universe
import Logic
import Universals.Relations.Universal
import Universals.Relations.Predicates.Unary.PartialEquivalenceRelation.Predicate

namespace Universe

namespace Relations

open Logic
open Logic.PC₁

-- # Partial Equivalence Relation Universal
-- The sub-universal of Rel U U whose particulars are partial equivalence relations.
-- A particular of this universal is a relation R bundled with a proof that
-- is_symmetric R ∧ is_transitive R.
def PEqRelUniversal (U: Universal): Universal := sub_universal (𝐑𝐞𝐥 U U) (partial_equivalence_relation_predicate U)
notation "𝐏𝐄𝐪𝐑𝐞𝐥" => PEqRelUniversal

def PEqRel (U: Universal): Type := (𝐏𝐄𝐪𝐑𝐞𝐥 U).Particular

end Relations

end Universe
