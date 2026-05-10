import Universe
import Logic
import Universals.Dyads.Universal
import Universals.Dyads.Predicates.Binary.SubsumptionGraph

/-!
# Subsume — the dyad lift operation

Given sub-universal embeddings `e₁: U₁' <: U₁` and `e₂: U₂' <: U₂`, the
`subsume` operation lifts a dyad `(a' ⋈ b') ∈ U₁' ⧓ U₂'` into the dyad
`(e₁.embedding a' ⋈ e₂.embedding b') ∈ U₁ ⧓ U₂`. It is the canonical way to propagate
sub-universal relations through the dyad constructor.

## Construction — parameterized `UnaryOperation` pattern

The graph layer (predicate + properties) lives under
`Universals.Dyads.Predicates.SubsumptionGraph`. This module contributes the
axiomatic layer:

1. `subsume_sym e₁ e₂` — postulated function symbol `U₁' ⋈ U₂' → U₁ ⋈ U₂`.
2. `subsume_def e₁ e₂` — defining axiom tying `subsume_sym` to `subsume_graph`.
3. `subsume e₁ e₂` — the bundled `UnaryOperation (U₁' ⧓ U₂') ⟴ (U₁ ⧓ U₂)`.

Because the signature depends on `e₁` and `e₂`, we cannot use the
`unary_operation` macro and instead emit axioms and the bundle manually
(schema of axioms, one per `(e₁, e₂)` instance).
-/

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsume operation symbol
axiom subsume_sym {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): U₁' ⋈ U₂' → U₁ ⋈ U₂

-- # Subsume defining axiom — referring to the graph
axiom subsume_def {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
  ∀ (x: U₁' ⋈ U₂'), ∀ (y: U₁ ⋈ U₂), (subsume_sym e₁ e₂ x =ₗₓₗ y) ↔ ((subsumption_graph e₁ e₂).pred x).pred y

-- # Subsume — the bundled UnaryOperation
noncomputable def subsume {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): (U₁' ⧓ U₂') ⟴ (U₁ ⧓ U₂) :=
  { graph := subsumption_graph e₁ e₂,
    op := subsume_sym e₁ e₂,
    «def» := subsume_def e₁ e₂ }

end Dyads
end Universe
