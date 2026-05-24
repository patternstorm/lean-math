import Universe
import Logic
import Universals.Sets.Universal
import Universals.Arrows.Universal

/-!
# Correspondences — Particular

A correspondence between U₁ and U₂ is a classification mapping: it maps
classifications (sets) in one universal to classifications in another.
Internally, it is a set of arrows from individuals to sets — arrows of type
`U₁ ⭢ᵃ 𝐒𝐞𝐭 U₂`, where each particular of U₁ is associated with the particulars
of U₂ according to the relation that gives place to the correspondence. This is
in fact the co-classification basis of the correspondence, i.e. which particulars
of the target universal each particular of the source universal co-classifies,
which determines how the correspondence maps classifications between the two universals.

## Relationship to Relations

Relations and correspondences are parallel concepts at different levels of the
induction hierarchy:

- Relation `Rel U₁ U₂`: a set of dyads — selects which dyads satisfy the relation
- Correspondence `Corr U₁ U₂`: a set of arrows — maps each particular
  to a class (set) in the target universal

A relation naturally induces a correspondence, and vice versa.

## Role in the Framework

A correspondence has a basis: the mapping of the singletons of its domain
particulars to their corresponding classes in the target universal. We say
the singleton co-classifies the particulars in the target universal. This basis
determines how the correspondence maps classifications between the two universals.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets
open Arrows

-- # Correspondences are sets of arrows from individuals to sets
protected abbrev Particular (U₁: Universal) (U₂: Universal): Type := Set (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂))


end Correspondences

end Universe
