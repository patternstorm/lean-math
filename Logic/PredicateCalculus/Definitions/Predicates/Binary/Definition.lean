import Logic.PredicateCalculus.Schemas.Predicates.Binary
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Properties.PropositionalEquivalencePreservesBinaryCongruence
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Properties.BinaryCongruenceFromCongruentFibers
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

-- Macro-local helper: package `binary_congruence_from_congruent_fibers` for
-- `[CongruentBinary]` typeclass instances. The underlying theorem takes inner
-- and outer cong proofs explicitly; this wrapper takes them from a typeclass
-- instance. Only used by the auto-cong branch of `binary_predicate` below.
private theorem combined_cong_from_typeclass
    {U₁ U₂: Universal} (body: U₁.Particular → U₂.Particular → Prop)
    [c: CongruentBinary U₁ U₂ body]:
    ∀ (x₁ x₂: U₁.Particular), ∀ (y₁ y₂: U₂.Particular),
      x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → (body x₁ y₁ ↔ body x₂ y₂) :=
  binary_congruence_from_congruent_fibers c.inner_cong c.outer_cong

/-!
# `binary_predicate` — single-line declaration of a named binary predicate.

Declaring a `BinaryPredicate U₁ U₂ body` manually requires three steps:

1. `axiom my_pred_sym : T₁ → T₂ → Prop` — the opaque predicate symbol,
2. `axiom my_pred_def : ∀ (x : T₁) (y : T₂), my_pred_sym x y ↔ body x y` — the defining axiom,
3. `noncomputable def my_pred : BinaryPredicate U₁ U₂ body := { pred := my_pred_sym, def := my_pred_def, cong := … }`.

This macro produces all three from a single line:

    binary_predicate my_pred : (x : T₁, y : T₂ ↦ body)             -- congruence auto-derived
    binary_predicate my_pred : (x : T₁, y : T₂ ↦ body) with cong   -- explicit congruence

After declaration, the following are available:

- `my_pred x y`     — apply the opaque symbol (via CoeFun)
- `my_pred.def`     — the propositional bridge `my_pred x y ↔ body x y`
- `my_pred.cong`    — derived combined congruence on `my_pred`
- `my_pred.toCongruentBinaryPredicate` — the underlying congruent binary predicate

The right-hand side of `:` is a binary statement template `(x : T₁, y : T₂ ↦ body)`,
the same notation used elsewhere in the project. The macro extracts the
binder types as the two domains and the body as the defining condition.
-/

-- With explicit cong proof
syntax (name := binaryPredicateCmd)
  "binary_predicate " ident " : " "(" stmtBinder ", " stmtBinder " ↦ " term ")" (" with " term)? : command

macro_rules
  | `(binary_predicate $name:ident : ($b₁:stmtBinder, $b₂:stmtBinder ↦ $body:term) with $cong:term) => do
    let nameStr := name.getId.toString
    let symIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_sym"))
    let defIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_def"))
    match b₁, b₂ with
    | `(stmtBinder| $x:ident : $t₁:term), `(stmtBinder| $y:ident : $t₂:term) =>
      `(
        axiom $symIdent : $t₁ → $t₂ → Prop
        axiom $defIdent : ∀ ($x : $t₁) ($y : $t₂), $symIdent $x $y ↔ $body
        noncomputable def $name : BinaryPredicate _ _ (fun $x : $t₁ => fun $y : $t₂ => $body) := {
          pred  := $symIdent
          «def» := $defIdent
          cong  := propositional_equivalence_preserves_binary_congruence $symIdent (fun $x : $t₁ => fun $y : $t₂ => $body) $defIdent $cong
        }
      )
    | _, _ => Lean.Macro.throwError "expected named binders (x : T₁, y : T₂ ↦ body) in binary_predicate"

-- Without explicit cong — auto-derive via [CongruentBinary] typeclass
macro_rules
  | `(binary_predicate $name:ident : ($b₁:stmtBinder, $b₂:stmtBinder ↦ $body:term)) => do
    let nameStr := name.getId.toString
    let symIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_sym"))
    let defIdent := Lean.mkIdent (Lean.Name.mkSimple (nameStr ++ "_def"))
    match b₁, b₂ with
    | `(stmtBinder| $x:ident : $t₁:term), `(stmtBinder| $y:ident : $t₂:term) =>
      `(
        axiom $symIdent : $t₁ → $t₂ → Prop
        axiom $defIdent : ∀ ($x : $t₁) ($y : $t₂), $symIdent $x $y ↔ $body
        noncomputable def $name : BinaryPredicate _ _ (fun $x : $t₁ => fun $y : $t₂ => $body) := {
          pred  := $symIdent
          «def» := $defIdent
          cong  := propositional_equivalence_preserves_binary_congruence $symIdent (fun $x : $t₁ => fun $y : $t₂ => $body) $defIdent (combined_cong_from_typeclass (fun $x : $t₁ => fun $y : $t₂ => $body))
        }
      )
    | _, _ => Lean.Macro.throwError "expected named binders (x : T₁, y : T₂ ↦ body) in binary_predicate"

end PC₁

end Logic
