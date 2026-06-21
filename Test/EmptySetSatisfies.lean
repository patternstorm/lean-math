import Universals.Sets
import Universals.Sets.Predicates.Unary.EmptySetGraph
import Universals.Sets.Operations.Constants.EmptySet.Constant

/-!
Verify that `empty_set.satisfies` has type `empty_set_graph_pred ∅ₛₑₜ` —
i.e., the empty set satisfies the predicate "has no elements" applied to
itself.

Two assertions:
  1. Type-level: `empty_set.satisfies` is a proof of `empty_set_graph_pred ∅ₛₑₜ`.
  2. Reduction-level: `empty_set_graph_pred ∅ₛₑₜ` unfolds to `∀ x, x ∉ₛₑₜ ∅ₛₑₜ`.
-/

namespace Test

open Universe Universe.Sets Logic Logic.PC₁

-- (1) Type-level check: `empty_set.satisfies` is a proof of
-- `empty_set_graph_pred (U := U) ∅ₛₑₜ`.
example {U: Universal}: empty_set_graph_pred (U := U) ∅ₛₑₜ := empty_set.satisfies

-- (2) Reduction-level check: that type is definitionally equal to the
-- raw "has no elements" assertion.
example {U: Universal}: ∀ (x: U.Particular), x ∉ₛₑₜ ∅ₛₑₜ := by
  have h₁: ∀ (x: U.Particular), x ∉ₛₑₜ ∅ₛₑₜ := empty_set.satisfies
  iterate h₁

end Test
