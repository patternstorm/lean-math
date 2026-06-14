import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.PowersetGraph
import Universals.Sets.Operations.Unary.Powerset.Operation

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Membership characterization of the powerset
--
-- The classical "S' is a member of 𝒫 S iff S' is a subset of S" — derived
-- from `powerset.def` (the operation's equational defining axiom). In the
-- OLD pattern this was an independent axiom; here it is a theorem proven
-- once from the framework's `unary_operation` machinery.
--
-- Proof shape:
-- 1. Instantiate `powerset.def` at (S, 𝒫 S) — gives the equational form of
--    the defining axiom, with the RHS being `powerset_graph_pred S (𝒫 S)`.
-- 2. By reflexivity of `=ₛₑₜ` at `𝒫 S`, the LHS of the iff holds.
-- 3. `PC₀.deductive_eq_l2r` extracts `powerset_graph_pred S (𝒫 S)`, which
--    definitionally unfolds to `∀ S', S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S` — the goal.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem powerset_membership {U: Universal}: ∀ (S: Set U), ∀ (S': Set U), S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S := by forall_intro
  variable(S: Set U)
  -- Instantiate powerset.def at S.
  have h₁: ∀ (y: Set (𝐒𝐞𝐭 U)), (𝒫 S =ₛₑₜ y) ↔ powerset_graph.pred S y := by forall_elim powerset.«def», S
  -- Instantiate at y := 𝒫 S.
  have h₂: (𝒫 S =ₛₑₜ 𝒫 S) ↔ powerset_graph.pred S (𝒫 S) := by forall_elim h₁, (𝒫 S)
  -- Reflexivity of =ₛₑₜ at 𝒫 S.
  have h₃: 𝒫 S =ₛₑₜ 𝒫 S := by forall_elim (𝐒𝐞𝐭 (𝐒𝐞𝐭 U)).eq.refl, (𝒫 S)
  -- Extract powerset_graph.pred S (𝒫 S), which definitionally unfolds to
  -- powerset_graph_pred S (𝒫 S) and then to ∀ S', S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S.
  have h₄: powerset_graph.pred S (𝒫 S) := PC₀.deductive_eq_l2r h₂ h₃
  iterate h₄


end Sets

end Universe
