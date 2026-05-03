import Logic.PredicateCalculus.Schemas.Operations.Unary.Schema
import Lean

namespace Logic

namespace PC₁

/-!
# `unary_operation` — convenience macro

Declaring a `UnaryOperation` manually requires three steps:

1. `axiom my_op_sym : U₁.Particular → U₂.Particular` — the operation function symbol
2. `axiom my_op_def : ∀ x y, (my_op_sym x =₍U₂₎ y) ↔ (G.pred x).pred y` — the defining axiom
3. `noncomputable def my_op : U₁ ⟴ U₂ := { graph := G, op := my_op_sym, def := my_op_def }`

This macro generates all three from a single line:

    unary_operation my_op : U₁ ⟴ U₂ from G

The `from` term must have type `UnaryOperationGraph U₁ U₂` — a plain
`CongruentBinaryPredicate` is not accepted, because totality and
functionality are required to keep the generated defining axiom consistent.

## Usage example

Given a unary operation graph `powerset_graph : UnaryOperationGraph (Set U) (Set (Set U))`:

    unary_operation powerset : Set U ⟴ Set (Set U) from powerset_graph

This generates:
- `axiom powerset_sym : (Set U).Particular → (Set (Set U)).Particular`
- `axiom powerset_def : ∀ x y, (powerset_sym x =₍Set (Set U)₎ y) ↔ (powerset_graph.pred x).pred y`
- `noncomputable def powerset : Set U ⟴ Set (Set U)`

After declaration, the following are available:
- `powerset x` — apply the operation (via CoeFun)
- `powerset.graph` — the operation's graph (exposes `.pred`, `.cong`, `.tot`, `.func`)
- `powerset.def` — the defining axiom (usable via `forall_elim`)
- `powerset.cong` — congruence (derived theorem, never assumed)
-/
open Lean Elab Command in
elab "unary_operation " name:ident " : " U₁:term:max " ⟴ " U₂:term:max " from " graph:term : command => do
  let symName := mkIdent (name.getId.appendAfter "_sym")
  let defName := mkIdent (name.getId.appendAfter "_def")
  -- Type ascription `(U : Universal)` on each Universal occurrence triggers
  -- Lean's auto-implicit binding when the caller uses a free variable (e.g.,
  -- `U ⟴ U from equals`). Without the ascription, `(U).Particular` is parsed
  -- as field notation on an un-typed term, which blocks auto-implicit before
  -- it can bind `U`. The ascription is a no-op when the caller passes a term
  -- already of type `Universal` (e.g., `Set U`).
  elabCommand (← `(axiom $symName : ($U₁ : Universal).Particular → ($U₂ : Universal).Particular))
  -- `$graph` must be a `UnaryOperationGraph U₁ U₂`. Its `.pred` projection
  -- comes from the inherited `CongruentBinaryPredicate` structure.
  elabCommand (← `(axiom $defName : ∀ (x: ($U₁ : Universal).Particular), ∀ (y: ($U₂ : Universal).Particular),
    ($symName x =₍$U₂₎ y) ↔ (($graph).pred x).pred y))
  elabCommand (← `(noncomputable def $name : UnaryOperation $U₁ $U₂ :=
    { graph := $graph, op := $symName, «def» := $defName }))

end PC₁

end Logic
