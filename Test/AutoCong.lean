import Universals.Sets
import Universals.Sets.Predicates.Ternary.Definitions.UnionGraphPredicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Test: typeclass-driven auto-cong for ternary graph predicates.
--
-- Goal: `union_graph_pred` (a `@[reducible]` `Set U → Set U → Set U → Prop` def)
-- should auto-resolve to a `CongruentTernaryPredicate` via the chain:
--
--   union_graph_pred has body  ∀ x, x ∈ₛₑₜ C ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B)
--
-- For each fixed pair of args, the body must be `CongruentUnary` in the third
-- arg. Typeclass synthesis chains:
--   congruent_universal → congruent_iff → (fiber_*_binary_congruent_unary,
--   congruent_disjunction, congruent_constant)
--
-- Then `congruent_ternary_from_fibers` (bridge) lifts the three unary instances
-- into `CongruentTernary U U U union_graph_pred`, and the `CoeDep` from
-- typeclass to structure yields a `CongruentTernaryPredicate U U U`.

-- Test 1: typeclass synthesis succeeds end-to-end for ternary.
example {U: Universal}: CongruentTernary (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (union_graph_pred (U := U)) :=
  inferInstance

-- Test 2: CoeDep into the structure also works (for ternary).
example {U: Universal}: CongruentTernaryPredicate (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) :=
  union_graph_pred (U := U)

-- Test 3: cbp.pred = original_pred is rfl-provable after CoeDep
-- (the structural projection reduces transparently through the coercion).
example {U: Universal}:
    let cbp: CongruentTernaryPredicate (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) := union_graph_pred (U := U)
    cbp.pred = union_graph_pred (U := U) := rfl


end Sets

end Universe
