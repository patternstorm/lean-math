import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Ternary.UnionGraph
import Universals.Sets.Operations.Binary.Union.Operation

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Membership characterization of the union
--
-- The classical "x is a member of A ∪ B iff x is a member of A or x is a
-- member of B" — derived from `union.def` (the operation's equational
-- defining axiom). In the OLD pattern this was an independent axiom; here it
-- is a theorem proven once from the framework's `binary_operation` machinery.
--
-- Proof shape:
-- 1. Instantiate `union.def` at (A, B, A ∪ₛₑₜ B) — gives the equational form
--    of the defining axiom, with the RHS being `union_graph.pred A B (A ∪ₛₑₜ B)`.
-- 2. By reflexivity of `=ₛₑₜ` at `A ∪ₛₑₜ B`, the LHS of the iff holds.
-- 3. `PC₀.deductive_eq_l2r` extracts `union_graph.pred A B (A ∪ₛₑₜ B)`, which
--    definitionally unfolds to `union_graph_pred A B (A ∪ₛₑₜ B)`, and then to
--    `∀ x, x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B)` — the goal.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-13
theorem union_membership {U: Universal}: ∀ (A: Set U), ∀ (B: Set U), ∀ (x: U.Particular),
      x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by forall_intro
  variable(A: Set U)
  variable(B: Set U)
  -- Instantiate union.def at (A, B).
  have h₁: ∀ (C: Set U), (A ∪ₛₑₜ B =ₛₑₜ C) ↔ union_graph.pred A B C := by forall_elim union.«def», A, B
  -- Instantiate at C := A ∪ₛₑₜ B.
  have h₂: (A ∪ₛₑₜ B =ₛₑₜ A ∪ₛₑₜ B) ↔ union_graph.pred A B (A ∪ₛₑₜ B) := by forall_elim h₁, (A ∪ₛₑₜ B)
  -- Reflexivity of =ₛₑₜ at A ∪ₛₑₜ B.
  have h₃: A ∪ₛₑₜ B =ₛₑₜ A ∪ₛₑₜ B := by forall_elim (𝐒𝐞𝐭 U).eq.refl, (A ∪ₛₑₜ B)
  -- Extract union_graph.pred A B (A ∪ₛₑₜ B), which definitionally unfolds to
  -- union_graph_pred A B (A ∪ₛₑₜ B) and then to ∀ x, x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B).
  have h₄: union_graph.pred A B (A ∪ₛₑₜ B) := PC₀.deductive_eq_l2r h₂ h₃
  iterate h₄


end Sets

end Universe
