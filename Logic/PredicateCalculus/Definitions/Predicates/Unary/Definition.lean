import Logic.PredicateCalculus.Schemas.Predicates.Unary
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Properties.PropositionalEquivalencePreservesCongruence
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

/-!
# `unary_predicate` — single-line declaration of a named unary predicate.

Declaring a `UnaryPredicate U body` manually requires three steps:

1. `axiom my_pred_sym : T → Prop` — the opaque predicate symbol,
2. `axiom my_pred_def : ∀ (x : T), my_pred_sym x ↔ body x` — the defining axiom,
3. `noncomputable def my_pred : UnaryPredicate U body := { pred := my_pred_sym, def := my_pred_def, cong := … }`.

This macro produces all three from a single line:

    unary_predicate my_pred : (x : T ↦ body)             -- congruence auto-derived
    unary_predicate my_pred : (x : T ↦ body) with cong   -- explicit congruence

After declaration, the following are available:

- `my_pred x`      — apply the opaque symbol (via CoeFun, ι-opaque through CoeFun)
- `my_pred.def`    — the propositional bridge `my_pred x ↔ body x`
- `my_pred.cong`   — derived congruence on `my_pred`
- `my_pred.toCongruentUnaryPredicate` — the underlying congruent predicate

The right-hand side of `:` is a statement template `(x : T ↦ body)`, the
same notation used elsewhere in the project. The macro extracts the binder
type as the domain and the body as the defining condition.
-/

-- With explicit cong proof
syntax (name := unaryPredicateCmd)
  "unary_predicate " ident " : " "(" stmtBinder " ↦ " term ")" (" with " term)? : command

macro_rules
  | `(unary_predicate $name:ident : ($b:stmtBinder ↦ $body:term) with $cong:term) => do
    let nameStr := name.getId.toString
    let symIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_sym"))
    let defIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_def"))
    match b with
    | `(stmtBinder| $x:ident : $t:term) =>
      `(
        axiom $symIdent : $t → Prop
        axiom $defIdent : ∀ ($x : $t), $symIdent $x ↔ $body
        noncomputable def $name : UnaryPredicate _ (fun $x : $t => $body) := {
          pred  := $symIdent
          «def» := $defIdent
          cong  := propositional_equivalence_preserves_congruence $symIdent (fun $x : $t => $body) $defIdent $cong
        }
      )
    | _ => Lean.Macro.throwError "expected named binder (x : T ↦ body) in unary_predicate"

-- Without explicit cong — auto-derive via [CongruentUnary] typeclass
macro_rules
  | `(unary_predicate $name:ident : ($b:stmtBinder ↦ $body:term)) => do
    let nameStr := name.getId.toString
    let symIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_sym"))
    let defIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_def"))
    match b with
    | `(stmtBinder| $x:ident : $t:term) =>
      `(
        axiom $symIdent : $t → Prop
        axiom $defIdent : ∀ ($x : $t), $symIdent $x ↔ $body
        noncomputable def $name : UnaryPredicate _ (fun $x : $t => $body) := {
          pred  := $symIdent
          «def» := $defIdent
          cong  := propositional_equivalence_preserves_congruence $symIdent (fun $x : $t => $body) $defIdent (inferInstance : Logic.PC₁.CongruentUnary _ (fun $x : $t => $body)).cong
        }
      )
    | _ => Lean.Macro.throwError "expected named binder (x : T ↦ body) in unary_predicate"

end PC₁

end Logic
