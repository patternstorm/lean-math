import Universals.Relations.Universal
import Universals.Correspondences
import Universals.Sets
import Universals.Relations.Operations.Unary.L2RFiber.Operation

/-!
# Left-to-Right Correspondence

The induction from a relation to a correspondence. Given a relation
R: Rel U₁ U₂ (a set of dyads), produces the correspondence whose arrows
pair each individual a with its fiber set {b | a ⋈ b ∈ R}.

This is the bridge from the undirected world (relations/dyads) to the
directed world (correspondences/arrows).
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Arrows
open Correspondences

-- # l2r_correspondence: Relation → Correspondence
axiom l2r_correspondence: Rel U₁ U₂ → Corr U₁ U₂

-- # Axiom definition
-- An arrow a ⭢ S belongs to the correspondence iff S is the fiber of R at a:
-- S contains exactly those b for which the dyad a ⋈ b belongs to R.
axiom l2r_correspondence_def: ∀ (R: Rel U₁ U₂), ∀ (a: U₁.Particular), ∀ (S: Set U₂),
  (a ⭢ᵃ S) ∈ₛₑₜ (l2r_correspondence R) ↔ (S =ₛₑₜ l2r_fiber R a)

-- TODO: Prove Congruent Operation

end Relations

end Universe
