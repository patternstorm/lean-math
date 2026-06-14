import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Ternary.UnionGraph

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # The `Union` operation
--
-- Given two sets `A B : Set U`, returns the set whose members are exactly
-- those in `A` or in `B`.
--
-- In ZFC, the Union Axiom must be postulated. Our framework avoids this:
-- "x is in A or x is in B" is a well-formed unary predicate over
-- `U.Particular`, so the union is simply the extension of that predicate via
-- set comprehension — no existence axiom required. Totality and
-- right-determinacy of the union graph (`union_graph`) discharge any potential
-- consistency concern: there always exists exactly one such set, by construction.
--
-- The `binary_operation` macro takes `union_graph` as input and introduces:
-- - `union_sym : Set U → Set U → Set U`                                       (opaque axiom — the function symbol)
-- - `union_def : ∀ A B C, (union_sym A B =ₛₑₜ C) ↔ union_graph_pred A B C`   (axiom — defining equation)
-- - `union     : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U`                                  (the bundled curried operation value)
-- The operation's congruence (`union.cong`) is then derived as a theorem by
-- the schema — never assumed. Partial application `union A : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U`
-- is itself a framework-level `UnaryOperation`, with its own graph (the fiber
-- of `union_graph` at `A`), opaque symbol, and derived congruence.
--
-- The classical "membership" characterization
-- `x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B)` is derived from `union.def`
-- in `Properties/Membership.lean`.

binary_operation union : (𝐒𝐞𝐭 U) ⟴ (𝐒𝐞𝐭 U) ⟴ (𝐒𝐞𝐭 U) from union_graph
infixl:65 " ∪ₛₑₜ " => union


end Sets

end Universe
