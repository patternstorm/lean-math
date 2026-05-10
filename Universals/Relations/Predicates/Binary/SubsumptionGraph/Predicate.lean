import Universe
import Logic
import Universals.Relations.Universal

namespace Universe
namespace Relations

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsumption predicate
-- { d : U₁ ⋈ U₂ | ∃ d' a' b', d' ∈ R₁ ∧ d' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁ a' ⋈ e₂ b') }
-- Only the last conjunct mentions d — it is equal_to (e₁ a' ⋈ e₂ b').
-- The rest is constant in d. Congruence follows by composing constant_predicate,
-- conjunction_preserves_congruence, and existential_preserves_congruence.
def subsumption_of {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂) (R₁: Rel U₁' U₂'):
    CongruentUnaryPredicate (U₁ ⧓ U₂) :=
  existential_preserves_congruence (d': U₁' ⋈ U₂' ↦
    existential_preserves_congruence (a': U₁'.Particular ↦
      existential_preserves_congruence (b': U₂'.Particular ↦
        conjunction_preserves_congruence
          (constant_predicate (d' ∈ₛₑₜ R₁))
          (conjunction_preserves_congruence
            (constant_predicate (d' =ₗₓₗ (a' ⋈ b')))
            (equal_to (e₁.embedding a' ⋈ e₂.embedding b'))))))

-- # Subsume graph predicate
-- R₂ =ₛₑₜ { d : U₁ ⋈ U₂ | ∃ d' a' b', d' ∈ R₁ ∧ d' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁ a' ⋈ e₂ b') }
private def subsume_graph_pred {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂) (R₁: Rel U₁' U₂') (R₂: Rel U₁ U₂): Prop :=
  R₂ =ₛₑₜ subsumption_of e₁ e₂ R₁

end Relations
end Universe
