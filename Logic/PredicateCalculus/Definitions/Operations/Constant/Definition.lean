import Logic.PredicateCalculus.Schemas.Operations.Constant.Schema
import Lean

namespace Logic

namespace PC₁

/-!
# `constant` — convenience macro

Declaring a `ConstantOperation` manually requires three steps:

1. `axiom my_const_sym : U.Particular` — the constant function symbol
2. `axiom my_const_satisfies : G.pred my_const_sym` — the satisfies axiom
3. `noncomputable def my_const : ConstantOperation U := { graph := G, op := my_const_sym, satisfies := my_const_satisfies }`

This macro generates all three from a single line:

    constant my_const : U from G

The `from` term must have type `ConstantOperationGraph U` — a plain
`CongruentUnaryPredicate` is not accepted, because left-totality and
right-determinacy are required to keep the generated satisfies axiom consistent.

## Usage example

Given a constant operation graph `empty_set_graph : ConstantOperationGraph (𝐒𝐞𝐭 U)`:

    constant empty_set : (𝐒𝐞𝐭 U) from empty_set_graph

This generates:
- `axiom empty_set_sym : (𝐒𝐞𝐭 U).Particular`
- `axiom empty_set_satisfies : empty_set_graph.pred empty_set_sym`
- `noncomputable def empty_set : ConstantOperation (𝐒𝐞𝐭 U)`

After declaration, the following are available:
- `empty_set`            — refer to the constant directly (via Coe, behaves as the particular)
- `empty_set.graph`      — the graph (exposes `.pred`, `.cong`, `.ltot`, `.rdet`)
- `empty_set.satisfies`  — the satisfies axiom (`graph.pred empty_set.op`)
- `empty_set.def`        — derived defining iff `∀ c, (op =₍U₎ c) ↔ graph.pred c`
- `empty_set.cong`       — derived reflexivity `empty_set.op =₍U₎ empty_set.op`
-/
open Lean Elab Command in
elab "constant " name:ident " : " U:term:max " from " graph:term : command => do
  let symName := mkIdent (name.getId.appendAfter "_sym")
  let satisfiesName := mkIdent (name.getId.appendAfter "_satisfies")
  -- Type ascription `($U : Universal)` on each Universal occurrence triggers
  -- Lean's auto-implicit binding when the caller uses a free variable (e.g.,
  -- `U from g`). Without the ascription, `($U).Particular` is parsed as field
  -- notation on an un-typed term, which blocks auto-implicit before it can
  -- bind `U`. The ascription is a no-op when the caller passes a term
  -- already of type `Universal` (e.g., `Set U`).
  elabCommand (← `(axiom $symName : ($U : Universal).Particular))
  -- `$graph` must be a `ConstantOperationGraph U`. Its `.pred` projection
  -- comes from the inherited `CongruentUnaryPredicate` structure. Explicit
  -- type ascriptions on `$graph` and `$symName` pin the universe `$U` —
  -- without them, the satisfies axiom (no binder to give context) would
  -- leave `U` as an unbound metavariable that Lean cannot synthesize.
  elabCommand (← `(axiom $satisfiesName :
    (($graph) : ConstantOperationGraph ($U : Universal)).pred
    (($symName) : ($U : Universal).Particular)))
  elabCommand (← `(noncomputable def $name : ConstantOperation $U :=
    { graph := $graph, op := $symName, satisfies := $satisfiesName }))

end PC₁

end Logic
