import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁

-- # Predicate Curry
-- Axiom scheme: for any unary predicate P on a Dyad, there exists a binary predicate
-- on its relata — called `curry P` — such that saying something about the dyad
-- (P (a ⋈ b)) is the same as saying it about a and b separately (curry P a b).
-- Whatever is true of the dyad is true of the pair, and vice versa. Curry just
-- changes the syntactic form — from one placeholder to two — without changing
-- what's being asserted.
--
-- Each concrete unary predicate P generates one instance of this axiom scheme.
-- P is a metavariable ranging over predicate symbols, not a second-order quantification.
--
-- The name "curry" is borrowed from function theory, but here it operates on
-- statement templates, not functions.
--
-- Predicate curry is the inverse of predicate uncurry: together they establish that
-- saying something about a and b separately and saying it about their dyad a ⋈ b
-- are interchangeable forms of the same assertion.
--
-- Predicate curry must be postulated as an axiom scheme rather than proved via
-- lambda abstraction — see README.md § "Variable-Arity Predicates" for why.
--
-- Higher arities compose: for a unary predicate on U₁ ⋈ (U₂ ⋈ U₃), curry once to get
-- a binary predicate on U₁ and U₂ ⋈ U₃, then curry the second argument again to get
-- a ternary predicate on U₁, U₂, U₃. The same two axiom schemes handle any arity.
--
-- This is a conservative definitional extension: it introduces a new predicate symbol
-- defined by equivalence, adding no new theorems in the old language.
--
-- P is a named parameter (not universally quantified) because this is an axiom scheme:
-- each concrete P generates one instance.
axiom curry {U₁: Universal} {U₂: Universal} (P: U₁ ⋈ U₂ → Prop): U₁.Particular → U₂.Particular → Prop
axiom curry_def {U₁: Universal} {U₂: Universal} (P: U₁ ⋈ U₂ → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), (curry P) a b ↔ P (a ⋈ b)

end Dyads
end Universe
