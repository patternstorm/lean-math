import Universals.Relations.Universal
import Universals.Correspondences
import Universals.Sets
import Universals.Relations.Operations.Unary.R2LFiber.Operation

/-!
# Right-to-Left Correspondence

The dual of l2r_correspondence. Given a relation R: Rel U₁ U₂ (a set of
dyads), produces the correspondence whose arrows pair each individual b of
U₂ with its fiber set {a | a ⋈ b ∈ R}.
-/

namespace Universe

namespace Relations

open Logic
open Logic.PC₁
open Sets
open Arrows
open Correspondences

-- # r2l_correspondence: Relation → Correspondence (reversed)
axiom r2l_correspondence: Rel U₁ U₂ → Corr U₂ U₁

-- # Axiom definition
-- An arrow b ⭢ S belongs to the correspondence iff S is the fiber of R at b:
-- S contains exactly those a for which the dyad a ⋈ b belongs to R.
axiom r2l_correspondence_def: ∀ (R: Rel U₁ U₂), ∀ (b: U₂.Particular), ∀ (S: Set U₁),
  (b ⭢ᵃ S) ∈ₛₑₜ (r2l_correspondence R) ↔ (S =ₛₑₜ r2l_fiber R b)

-- TODO: Prove Congruent Operation

end Relations

end Universe
