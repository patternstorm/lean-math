import Universe
import Logic
import Universals.Sets.Universal
import Universals.Arrows.Universal

/-!
# Correspondences — Particular

A correspondence between U₁ and U₂ is a set of arrows from individuals to
sets: arrows of type `U₁ ⭢ᵃ 𝐒𝐞𝐭 U₂`. This is a type alias, not a new type —
correspondences inherit all set operations for free.

## Relationship to Relations

Relations and correspondences are parallel concepts at different levels of the
induction hierarchy:

- Relation `Rel U₁ U₂`: a set of dyads — classifies which individuals
  co-exist in relation
- Correspondence `Corr U₁ U₂`: a set of arrows — from an individual,
  produce a set

A relation naturally induces a correspondence, and vice versa.

## Role in the Framework

The natural way to select arrows is through relations, via the correspondences
they induce. When a correspondence is functional (all images are singletons),
it is isomorphic to a set of direct `Arrow U₁ U₂` arrows — from an
individual, produce an individual.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets
open Arrows

-- # Correspondences are sets of arrows from individuals to sets
def Corr (U₁: Universal) (U₂: Universal): Type := Set (U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂))


end Correspondences

end Universe
