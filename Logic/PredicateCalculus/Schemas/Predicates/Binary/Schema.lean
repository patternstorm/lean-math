import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema

namespace Logic

namespace PC₁

-- # `BinaryPredicate U₁ U₂ body` — a named binary predicate with an opaque
-- symbol, a propositional definition, and a congruence proof.
--
-- The structure extends `CongruentBinaryPredicate U₁ U₂` so `pred` and `cong`
-- are inherited; the only new field is `def`, which states that the (opaque)
-- predicate symbol `pred` is propositionally equivalent to `body`.
-- The `body` parameter records what the symbol is supposed to mean — it's
-- visible in the type, so dot notation `<name>.def` exposes the iff bridge.
--
-- Use the `binary_predicate` macro in
-- `Logic.PredicateCalculus.Definitions.Predicates.Binary.Definition` to
-- declare a named binary predicate in one line.
structure BinaryPredicate (U₁ U₂: Universal) (body: U₁.Particular → U₂.Particular → Prop) extends CongruentBinaryPredicate U₁ U₂ where
  «def»: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), pred x y ↔ body x y

-- Auto-upcast `BinaryPredicate U₁ U₂ body` → `CongruentBinaryPredicate U₁ U₂`
-- whenever the parent type is expected. Lean's `extends` generates the
-- projection `toCongruentBinaryPredicate`, but does NOT install a `Coe`
-- instance for it, so we wire it up explicitly here. This lets a named
-- predicate be passed anywhere a `CongruentBinaryPredicate` is required
-- (e.g. `fiber_first_preserves_binary_congruence inclusion A`) without
-- writing `.toCongruentBinaryPredicate` at the call site.
instance {U₁ U₂: Universal} {body: U₁.Particular → U₂.Particular → Prop}:
    CoeHead (BinaryPredicate U₁ U₂ body) (CongruentBinaryPredicate U₁ U₂) where
  coe P := P.toCongruentBinaryPredicate

-- CoeFun for `BinaryPredicate` so consumers can apply a named predicate as a
-- function — `subsumes R₁ R₂` instead of `subsumes.pred R₁ R₂` — matching
-- the way binary predicates are applied in ordinary mathematical notation.
--
-- Redeclared at this level because the parent's CoeFun applies to
-- `CongruentBinaryPredicate U₁ U₂`, and Lean doesn't chain Coe + CoeFun
-- automatically through the auto-generated projection.
instance {U₁ U₂: Universal} {body: U₁.Particular → U₂.Particular → Prop}:
    CoeFun (BinaryPredicate U₁ U₂ body) (fun _ => U₁.Particular → U₂.Particular → Prop) where
  coe P := P.pred

end PC₁

end Logic
