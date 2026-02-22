import Universe
import Logic
import Universals.Sets.Universal

namespace Universe

namespace Sets

open Logic.PC₁

-- A set S over U induces a sub-universal of U: the type of elements belonging to S.
--
-- This is syntactic sugar over FOL. We are NOT leaving FOL behind.
-- Quantifying over the induced universal is equivalent to using membership with implication:
--   ∀ x : (set_as_universal U S).Particular, Q(x)   ≡   ∀ x : U.Particular, x ∈ S → Q(x)
--
-- Since Set U = CongruentUnaryPredicate U, we can directly apply sub_universal.
def set_as_universal (S : Set U) : Universal := sub_universal U S

-- Working with elements of a set-as-universal (see SubUniversal/Schema.lean for details):
--   x : (set_as_universal S).Particular   -- x is the subtype element (value + proof)
--   ↑x : U.Particular                     -- the underlying element of U
--   x.property : S.pred ↑x                -- proof that ↑x satisfies S

-- EXAMPLE 1: No ↑ needed - using sub-universal's equality on subtype elements
example (S : Set U) :
    ∀ (x : (set_as_universal S).Particular), x =₍set_as_universal S₎ x :=
  (set_as_universal S).eq.refl

-- EXAMPLE 2: ↑ needed - using a predicate Q defined on U
example (S : Set U) (Q : CongruentUnaryPredicate U) :
    ∀ (x : (set_as_universal S).Particular), Q.pred ↑x → Q.pred ↑x :=
  fun _ h => h

-- EXAMPLE 3: Mixed - sub-universal equality + predicate on U
-- "If x equals y in the sub-universal, and Q holds for x, then Q holds for y"
-- Here: x =₍...₎ y uses subtype elements, but Q.pred needs ↑
example (S : Set U) (Q : CongruentUnaryPredicate U) :
    ∀ (x : (set_as_universal S).Particular), ∀ (y : (set_as_universal S).Particular),
    x =₍set_as_universal S₎ y → Q.pred ↑x → Q.pred ↑y :=
  fun x y heq hq => (Q.cong ↑x ↑y heq).mp hq

-- EXAMPLE 4: ↑ needed - membership in another set T
-- "Every element of S is also in T" requires ↑ because ∈ₛₑₜ expects U.Particular
-- (Would need: ∀ x : (set_as_universal S).Particular, ↑x ∈ₛₑₜ T)

end Sets

end Universe
