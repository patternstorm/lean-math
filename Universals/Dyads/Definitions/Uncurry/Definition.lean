import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁

-- # Predicate Uncurry
-- Axiom scheme: for any binary predicate R on two types, there exists a unary predicate
-- on their Dyad — called `uncurry R` — such that saying something about a and b
-- separately (R a b) is the same as saying it about their dyad (uncurry R (a ⋈ b)).
-- Whatever is true of the pair is true of the dyad, and vice versa. Uncurry just
-- changes the syntactic form — from two placeholders to one — without changing
-- what's being asserted.
--
-- Each concrete binary predicate R generates one instance of this axiom scheme.
-- R is a metavariable ranging over predicate symbols, not a second-order quantification.
--
-- The name "uncurry" is borrowed from function theory, but here it operates on
-- statement templates, not functions.
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
--
-- R is a named parameter (not universally quantified) because this is an axiom scheme:
-- each concrete R generates one instance.
axiom uncurry {U₁: Universal}{U₂: Universal} (R: U₁.Particular → U₂.Particular → Prop): U₁ ⋈ U₂ → Prop
axiom uncurry_def {U₁: Universal}{U₂: Universal} (R: U₁.Particular → U₂.Particular → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), (uncurry R) (a ⋈ b) ↔ R a b

end Dyads
end Universe
