import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁

-- # Predicate Curry
-- Axiom scheme: transports a unary predicate on a Dyad to a binary predicate on its relata.
-- Each concrete unary predicate P generates one instance of this axiom scheme.
-- P is a metavariable ranging over predicate symbols, not a second-order quantification.
--
-- The name "curry" is borrowed from function theory, but here it operates on
-- statement templates, not functions. A unary predicate P(d) has one placeholder
-- ranging over dyads. Predicate curry splits that dyad placeholder into two
-- independent placeholders — one for each relatum — yielding a binary predicate
-- curry P(a, b). The propositional content is preserved: curry P a b ↔ P (a ⋈ b).
--
-- Predicate curry must be postulated as an axiom scheme rather than proved via
-- lambda abstraction — see README.md § "Variable-Arity Predicates" for why.
--
-- Predicate curry is the inverse of predicate uncurry: together they establish that
-- binary predicates on U₁.Particular and U₂.Particular and unary predicates on
-- U₁ ⋈ U₂ carry the same propositional content.
--
-- Higher arities compose: for a unary predicate on U₁ ⋈ (U₂ ⋈ U₃), curry once to get
-- a binary predicate on U₁ and U₂ ⋈ U₃, then curry the second argument again to get
-- a ternary predicate on U₁, U₂, U₃. The same two axiom schemes handle any arity.
--
-- This is a conservative definitional extension: it introduces a new predicate symbol
-- defined by equivalence, adding no new theorems in the old language.
axiom curry {U₁: Universal} {U₂: Universal} (P: (U₁ ⋈ U₂).Particular → Prop): U₁.Particular → U₂.Particular → Prop
axiom curry_def {U₁: Universal} {U₂: Universal} (P: (U₁ ⋈ U₂).Particular → Prop): ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), curry P a b ↔ P (a ⋈ b)

end Dyads
end Universe
