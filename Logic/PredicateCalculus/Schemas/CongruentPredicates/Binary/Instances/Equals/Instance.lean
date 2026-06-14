import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

-- # `equals` — equality as a `CongruentBinaryPredicate U U`.
--
-- This packages the universe's equality (`U.eq.pred`, with cong derived in
-- `Equality.cong` at the schema) into the framework's `CongruentBinaryPredicate`
-- form, making it consumable by framework constructs that take CBPs (fiber
-- preservation theorems, downstream operation graphs, etc.). The actual
-- mathematical content lives in `Equality/Schema.lean`; this file is the
-- thin framework-side packaging.
def equals: CongruentBinaryPredicate U U :=
  { pred := U.eq.pred
    cong := U.eq.cong }


-- # `=₍U₎` notation.
--
-- Expands through `@equals U` (via the framework's `CoeFun` on
-- `CongruentBinaryPredicate`), so `a =₍U₎ b` elaborates to `equals.pred a b`.
-- This shape is what the standard `fiber_*_binary_congruent_unary equals a`
-- typeclass instances pattern-match against — auto-cong fires for `=₍U₎`
-- bodies without any bridge instance.
notation:50 a:51 " =₍" U:51 "₎ " b:51 => @equals U a b


end PC₁

end Logic
