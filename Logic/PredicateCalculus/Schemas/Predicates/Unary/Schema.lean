import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema

namespace Logic

namespace PC₁

-- # `UnaryPredicate U body` — a named unary predicate with an opaque symbol,
-- a propositional definition, and a congruence proof.
--
-- The structure extends `CongruentUnaryPredicate U` so `pred` and `cong` are
-- inherited; the only new field is `def`, which states that the (opaque)
-- predicate symbol `pred` is propositionally equivalent to `body`.
-- The `body` parameter records what the symbol is supposed to mean — it's
-- visible in the type, so dot notation `<name>.def` exposes the iff bridge.
--
-- Use the `unary_predicate` macro in
-- `Logic.PredicateCalculus.Definitions.Predicates.Unary.Definition` to
-- declare a named unary predicate in one line.
structure UnaryPredicate (U: Universal) (body: U.Particular → Prop) extends CongruentUnaryPredicate U where
  «def»: ∀ (x: U.Particular), pred x ↔ body x

-- Auto-upcast `UnaryPredicate U body` → `CongruentUnaryPredicate U` whenever
-- the parent type is expected. Lean's `extends` generates the projection
-- `toCongruentUnaryPredicate`, but does NOT install a `Coe` instance for it,
-- so we wire it up explicitly here. This lets a named predicate be passed
-- anywhere a `CongruentUnaryPredicate` is required (e.g. `U ↾ is_singleton`)
-- without writing `.toCongruentUnaryPredicate` at the call site.
instance {U: Universal} {body: U.Particular → Prop}:
    CoeHead (UnaryPredicate U body) (CongruentUnaryPredicate U) where
  coe P := P.toCongruentUnaryPredicate

-- CoeFun for `UnaryPredicate` so consumers can apply a named predicate as a
-- function — `is_reflexive R` instead of `is_reflexive.pred R` — matching the
-- way predicates are applied in ordinary mathematical notation.
--
-- Redeclared at this level because the parent's CoeFun applies to
-- `CongruentUnaryPredicate U`, and Lean doesn't chain Coe + CoeFun
-- automatically through the auto-generated projection.
instance {U: Universal} {body: U.Particular → Prop}:
    CoeFun (UnaryPredicate U body) (fun _ => U.Particular → Prop) where
  coe P := P.pred

end PC₁

end Logic
