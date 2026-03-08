import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Sets

/-!
# Correspondence Apply

Applies a correspondence to a source particular, producing the set on the
right-hand side associated with that source.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets
open Arrows

axiom apply: Corr U₁ U₂ → U₁.Particular → Set U₂

axiom apply_def: ∀ (C: Corr U₁ U₂), ∀ (a: U₁.Particular), ∀ (S: Set U₂),
  S =ₛₑₜ (apply C a) ↔ (a ⭢ᵃ S) ∈ₛₑₜ C

-- TODO: Prove Congruent Operation

end Correspondences

end Universe
