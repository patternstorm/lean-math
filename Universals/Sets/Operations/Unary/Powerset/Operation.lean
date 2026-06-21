import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.PowersetGraph

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # The `Powerset` operation
--
-- Given a set `S : Set U`, returns the set of all subsets of `S` —
-- i.e., `𝒫 S : Set (𝐒𝐞𝐭 U)`.
--
-- In ZFC, the Powerset Axiom must be postulated: "∀A ∃P ∀B (B ∈ P ↔ B ⊆ A)".
-- This is an existence claim — without it, ZFC cannot prove that the
-- collection of all subsets of a set forms a set.
--
-- Our framework avoids this. The predicate "S' is a subset of S" is
-- well-formed over `Set U` (it's a unary predicate, captured by `subsets_of`),
-- so the powerset is simply the extension of that predicate via set
-- comprehension — no existence axiom required. Totality and right-determinacy
-- of the powerset graph (`powerset_graph`) discharge any potential consistency
-- concern: there always exists exactly one such set, by construction.
--
-- The `unary_operation` macro takes `powerset_graph` as input and introduces:
-- - `powerset_sym : Set U → Set (𝐒𝐞𝐭 U)`                  (opaque axiom — the function symbol)
-- - `powerset_def : ∀ S P, (powerset_sym S =ₛₑₜ P) ↔ powerset_graph_pred S P`   (axiom — defining equation)
-- - `powerset     : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 (𝐒𝐞𝐭 U)`                  (the bundled operation value)
-- The operation's congruence (`powerset.cong`) is then derived as a theorem
-- by the schema — never assumed.
--
-- The classical "membership" characterization `S' ∈ₛₑₜ 𝒫 S ↔ S' ⊆ₛₑₜ S` is
-- derived from `powerset.def` in `Properties/PowersetMembership.lean`.

unary_operation powerset : (𝐒𝐞𝐭 U) ⟴ (𝐒𝐞𝐭 (𝐒𝐞𝐭 U)) from powerset_graph
prefix:max "𝒫" => powerset.op


end Sets

end Universe
