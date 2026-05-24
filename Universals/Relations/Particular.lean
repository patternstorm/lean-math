import Universe
import Logic
import Universals.Sets
import Universals.Dyads

/-!
# Relations — Particular

A relation between U₁ and U₂ is a set of dyads. This is a type alias,
not a new type — relations inherit all set operations for free.

The `relation_from` constructor builds a relation from a congruent binary
predicate using uncurry: the curried predicate P a b becomes the unary
predicate (uncurry P) on dyads a ⋈ b.
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads

-- # Relations are sets of dyads
protected abbrev Particular (U₁: Universal) (U₂: Universal): Type := Set (U₁ ⧓ U₂)

-- # Relation constructor
-- Builds a relation from a congruent binary predicate.
-- The curried predicate P a b is converted to a unary predicate on dyads
-- via uncurry, and congruence is derived via uncurry_cong.
noncomputable def relation_from {U₁: Universal} {U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂): Relations.Particular U₁ U₂ :=
  -- { d: U₁ ⋈ U₂ | (uncurry (a: U₁.Particular, b: U₂.Particular ↦ (P.pred a).pred b)) d }
   { d: U₁ ⋈ U₂ | ∃ a: U₁.Particular, ∃ b: U₂.Particular, d =₍(U₁ ⧓ U₂)₎ (a ⋈ b) ∧ (P.pred a).pred b }
  -- let pred: CongruentUnaryPredicate (U₁ ⧓ U₂) := uncurry (a: U₁.Particular, b: U₂.Particular ↦ (P.pred a).pred b)
  -- pred

end Relations

end Universe
