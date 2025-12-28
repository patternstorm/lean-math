import Logic.PredicateCalculus.Schemas.Universal.Schema

namespace Logic

namespace PC₁

-- # Unique Existence Quantifier
axiom ExistsUnique (U : Universal) : (U.Particular → Prop) → Prop

syntax "∃!" "₍" term "₎" ident "," term : term
syntax "∃!" "₍" term "₎" ident ":" term ", " term : term
syntax "∃!" "₍" term "₎" "(" ident ":" term ")" ", " term : term

macro_rules
  | `(∃!₍$U₎ $x:ident, $body)      => `(ExistsUnique $U (fun ($x) => $body))
  | `(∃!₍$U₎ $x:ident : $t, $body) => `(ExistsUnique $U (fun ($x : $t) => $body))
  | `(∃!₍$U₎ ($x:ident : $t), $body) => `(ExistsUnique $U (fun ($x : $t) => $body))

-- ## Axiom defining its meaning
axiom exists_unique_def : ∀ (U : Universal), ∀ (P : U.Particular → Prop), ExistsUnique U P ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x))

end PC₁

end Logic
