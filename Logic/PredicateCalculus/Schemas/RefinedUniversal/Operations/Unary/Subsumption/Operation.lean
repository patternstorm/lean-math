import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Predicates.SubsumptionGraph

namespace Logic

namespace PC₁


-- The subsume operation symbol: the canonical injection (U ↾ P) → U.
-- Satisfies axiom: `subsume_sym P` lands in the subsumption graph at every input.
--
-- `subsume_sym` is defined as `Subtype.val` (Lean's built-in subtype projection).
-- This is the unique implementation choice consistent with the framework's
-- axioms — any other choice would contradict `subsume_satisfies`. Making it
-- a `def` (not an axiom) lets Lean's elaborator see that `(subsume P).op x = x.val`
-- definitionally, so the `CoeDep` coercion mechanism produces `x.val`
-- automatically. Framework proofs must continue to reason about `subsume_sym`
-- symbolically (via `subsume.satisfies`, the framework-derived `subsume.«def»`,
-- and `subsume_particular`) — the definitional equality is plumbing for
-- coercion, not a proof technique.
def subsume_sym {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P).Particular → U.Particular := fun x => x.val

axiom subsume_satisfies {U: Universal} (P: CongruentUnaryPredicate U): ∀ (x: (U ↾ P).Particular), (subsumption_graph P).pred x (subsume_sym P x)

-- The bundled `UnaryOperation`. With satisfies as the axiom, the noncomputable
-- def uses it directly — no derivation needed. The framework-level
-- `UnaryOperation.def` derived theorem provides `(subsume P).«def»` (iff form)
-- via dot notation, matching the shape of macro-declared operations.
noncomputable def subsume {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P) ⟴ U := {
  graph := subsumption_graph P
  op := subsume_sym P
  satisfies := subsume_satisfies P
}

end PC₁

end Logic
