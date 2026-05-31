import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Predicates.SubsumptionGraph

namespace Logic

namespace PC₁


-- The subsume operation symbol: the canonical injection (U ↾ P) → U.
-- Defining axiom: subsume_sym P x =₍U₎ y ↔ ↑x =₍U₎ y.
--
-- subsume_sym is defined as Subtype.val (Lean's built-in subtype projection). This
-- is the unique implementation choice consistent with the framework's axioms — any
-- other choice would contradict subsume_def. Making it a def (not an axiom) lets
-- Lean's elaborator see that `(subsume P).op x = x.val` definitionally, so the
-- CoeDep coercion mechanism produces `x.val` automatically. Framework proofs must
-- continue to reason about subsume_sym symbolically (via subsume_def and
-- subsume_particular) — the definitional equality is plumbing for coercion, not
-- a proof technique.
def subsume_sym {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P).Particular → U.Particular :=
  fun x => x.val
axiom subsume_def {U: Universal} (P: CongruentUnaryPredicate U): ∀ (x: (U ↾ P).Particular), ∀ (y: U.Particular),
    (subsume_sym P x =₍U₎ y) ↔ (subsumption_graph P).pred x y

noncomputable def subsume {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P) ⟴ U :=
  { graph := subsumption_graph P, op := subsume_sym P, «def» := subsume_def P }

end PC₁

end Logic
