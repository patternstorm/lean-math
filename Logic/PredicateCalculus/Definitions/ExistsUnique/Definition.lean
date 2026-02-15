import Logic.PredicateCalculus.Schemas.Universal.Schema

namespace Logic

namespace PC₁

-- # Unique Existence Quantifier
-- ExistsUnique must remain an axiom (not def/abbrev). Lean's elaborator does not
-- unfold def/abbrev through `let` bindings, so `exists_elim` and ⟨...⟩
-- destructuring fail when ExistsUnique is definitional. The axiom + iff approach
-- (exists_unique_def) works reliably with our natural deduction proof style.
axiom ExistsUnique (U : Universal) : (U.Particular → Prop) → Prop

syntax "∃!" "₍" term "₎" ident "," term : term
syntax "∃!" "₍" term "₎" ident ":" term ", " term : term
syntax "∃!" "₍" term "₎" "(" ident ":" term ")" ", " term : term

macro_rules
  | `(∃!₍$U₎ $x:ident, $body)      => `(ExistsUnique $U (fun ($x) => $body))
  | `(∃!₍$U₎ $x:ident : $t, $body) => `(ExistsUnique $U (fun ($x : $t) => $body))
  | `(∃!₍$U₎ ($x:ident : $t), $body) => `(ExistsUnique $U (fun ($x : $t) => $body))

-- ## Axiom defining its meaning
-- The quantification over U : Universal and P : U.Particular → Prop is NOT
-- second-order logic. This is an axiom schema: both U and P are schema
-- parameters. Each concrete Universal and concrete predicate produces a
-- first-order axiom instance. Lean's ∀ is type-theoretic machinery encoding
-- what would be syntactic substitution on paper. This is how unique existence
-- is standardly defined in first-order logic.
axiom exists_unique_def : ∀ (U : Universal), ∀ (P : U.Particular → Prop), ExistsUnique U P ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x))

end PC₁

end Logic
