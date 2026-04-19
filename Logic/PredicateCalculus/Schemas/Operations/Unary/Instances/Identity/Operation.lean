import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Definitions.Operations.Unary.Definition

-- # Identity — the UnaryOperation U ⟴ U whose graph is `equals`
--
-- Declared via the `unary_operation` macro, which generates:
-- - axiom `identity_sym : U.Particular → U.Particular` — the operation function symbol,
-- - axiom `identity_def : ∀ x y, (identity_sym x =₍U₎ y) ↔ (equals.pred x).pred y` — defining axiom,
-- - `noncomputable def identity : U ⟴ U := { ext := equals, op := identity_sym, def := identity_def }`.
--
-- Since `(equals.pred x).pred y` unfolds to `x =₍U₎ y` (domain-first graph
-- convention), the defining axiom reads:
--   identity_sym x =₍U₎ y ↔ x =₍U₎ y.

namespace Logic

namespace PC₁

unary_operation identity : U ⟴ U from equals

end PC₁

end Logic
