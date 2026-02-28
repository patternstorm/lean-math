import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁

-- # Predicate Uncurry
-- Axiom scheme: transports a binary predicate on two types to a unary predicate on their Dyad.
-- Each concrete binary predicate R generates one instance of this axiom scheme.
-- R is a metavariable ranging over predicate symbols, not a second-order quantification.
--
-- The name "uncurry" is borrowed from function theory, but here it operates on
-- statement templates, not functions. A binary predicate R(a, b) has two independent
-- placeholders. Predicate uncurry binds them together into a single dyad placeholder,
-- yielding a unary predicate uncurry R(d). The two previously independent placeholders
-- are now related via the dyad. The propositional content is preserved:
-- uncurry R (a ⋈ b) ↔ R a b.
--
-- Predicate uncurry must be postulated as an axiom scheme rather than proved via
-- lambda abstraction — see README.md § "Variable-Arity Predicates" for why.
--
-- Higher arities compose: for a ternary predicate R(x,y,z), uncurry the last two
-- arguments to get a binary predicate on U₁ and U₂ ⋈ U₃, then uncurry again to get
-- a unary predicate on U₁ ⋈ (U₂ ⋈ U₃). The same two axiom schemes handle any arity.
--
-- This is a conservative definitional extension: it introduces a new predicate symbol
-- defined by equivalence, adding no new theorems in the old language.
axiom uncurry {U₁: Universal}{U₂: Universal} (R: U₁.Particular → U₂.Particular → Prop): (U₁ ⋈ U₂).Particular → Prop
axiom uncurry_def {U₁: Universal}{U₂: Universal} (R: U₁.Particular → U₂.Particular → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), uncurry R (a ⋈ b) ↔ R a b

end Dyads
end Universe
