import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.UnaryOperationGraph
import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity.Operation
import Logic.PredicateCalculus.Definitions
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Predicates.SubsumptionGraph.Properties

namespace Logic

namespace PC₁

-- # Subsume — the embedding operation from a refined universal into its parent
--
-- The graph of subsumption maps each element of `U ↾ P` to the element of `U`
-- it embeds to. As a flat congruent binary predicate over `Uₚ × U`:
--
--   pred a b  ≡  a.val =₍U₎ b
--
-- Because `x₁ =₍Uₚ₎ x₂` is definitionally `x₁.val =₍U₎ x₂.val`, the `cong`
-- obligation reduces to instantiating `identity_graph.cong` (the combined cong
-- on `U`) at `x₁.val, x₂.val, y₁, y₂` and discharging the two implications
-- with the assumed equalities. `ltot` and `rdet` come from the dedicated
-- `subsume_*` lemmas.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
noncomputable def subsumption_graph {U: Universal} (P: CongruentUnaryPredicate U): UnaryOperationGraph (U ↾ P) U :=
  let Uₚ: Universal := U ↾ P
  let pred: Uₚ.Particular → U.Particular → Prop := (a: Uₚ.Particular, b: U.Particular ↦ a.val =₍U₎ b)
  let cong: ∀ (x₁: Uₚ.Particular), ∀ (x₂: Uₚ.Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular),
        x₁ =₍Uₚ₎ x₂ → y₁ =₍U₎ y₂ → (x₁.val =₍U₎ y₁ ↔ x₂.val =₍U₎ y₂) := by forall_intro
    variable(x₁: Uₚ.Particular)
    variable(x₂: Uₚ.Particular)
    variable(y₁: U.Particular)
    variable(y₂: U.Particular)
    assume(h₁: x₁ =₍Uₚ₎ x₂)
    assume(h₂: y₁ =₍U₎ y₂)
    have h₃: x₁.val =₍U₎ x₂.val → y₁ =₍U₎ y₂ → (x₁.val =₍U₎ y₁ ↔ x₂.val =₍U₎ y₂) := by forall_elim identity_graph.cong, (x₁.val: U.Particular), x₂.val, y₁, y₂
    have h₄: y₁ =₍U₎ y₂ → (x₁.val =₍U₎ y₁ ↔ x₂.val =₍U₎ y₂) := by modus_ponens h₃, h₁
    have h₅: x₁.val =₍U₎ y₁ ↔ x₂.val =₍U₎ y₂ := by modus_ponens h₄, h₂
    iterate h₅
  let ltot: ∀ (x: Uₚ.Particular), ∃ (y: U.Particular), x.val =₍U₎ y := subsume_left_totality P
  let rdet: ∀ (x: Uₚ.Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), x.val =₍U₎ y₁ ∧ x.val =₍U₎ y₂ → y₁ =₍U₎ y₂ := subsume_right_determinacy P
  { pred := pred, cong := cong, ltot := ltot, rdet := rdet }


end PC₁

end Logic
