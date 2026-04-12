import Logic.PredicateCalculus.Schemas.Operations.Unary.Schema
import Lean

namespace Logic

namespace PC₁

/-!
# `unary_operation` — convenience macro

Declaring a `UnaryOperation` manually requires three steps:

1. `axiom my_op_sym : U₁.Particular → U₂.Particular` — the operation function symbol
2. `axiom my_op_def : ∀ x y, (my_op_sym x =₍U₂₎ y) ↔ (G.pred x).pred y` — the defining axiom
3. `noncomputable def my_op : U₁ ⟴ U₂ := { ext := G, op := my_op_sym, def := my_op_def }`

This macro generates all three from a single line:

    unary_operation my_op : U₁ ⟴ U₂ from G

## Usage example

Given a congruent binary predicate `G : CongruentBinaryPredicate U₁ U₂`:

    unary_operation powerset : Set U ⟴ Set (Set U) from powerset_graph

This generates:
- `axiom powerset_sym : (Set U).Particular → (Set (Set U)).Particular`
- `axiom powerset_def : ∀ x y, (powerset_sym x =₍Set (Set U)₎ y) ↔ (powerset_graph.pred x).pred y`
- `noncomputable def powerset : Set U ⟴ Set (Set U)`

After declaration, the following are available:
- `powerset x` — apply the operation (via CoeFun)
- `powerset.ext` — the graph predicate (reduces to `powerset_graph`)
- `powerset.def` — the defining axiom (usable via `forall_elim`)
- `powerset.cong` — congruence (derived theorem, never assumed)
-/
open Lean Elab Command in
elab "unary_operation " name:ident " : " U₁:term:max " ⟴ " U₂:term:max " from " ext:term : command => do
  let symName := mkIdent (name.getId.appendAfter "_sym")
  let defName := mkIdent (name.getId.appendAfter "_def")
  elabCommand (← `(axiom $symName : ($U₁).Particular → ($U₂).Particular))
  elabCommand (← `(axiom $defName : ∀ (x: ($U₁).Particular), ∀ (y: ($U₂).Particular),
    ($symName x =₍$U₂₎ y) ↔ (($ext).pred x).pred y))
  elabCommand (← `(noncomputable def $name : UnaryOperation $U₁ $U₂ :=
    { ext := $ext, op := $symName, «def» := $defName }))

end PC₁

end Logic
