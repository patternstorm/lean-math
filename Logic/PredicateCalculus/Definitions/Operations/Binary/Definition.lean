import Logic.PredicateCalculus.Schemas.Operations.Binary.Schema
import Lean

namespace Logic

namespace PC₁

/-!
# `binary_operation` — convenience macro

Declaring a `BinaryOperation` manually requires three steps:

1. `axiom my_op_sym : U₁.Particular → U₂.Particular → U₃.Particular` — the binary function symbol
2. `axiom my_op_satisfies : ∀ x y, G.pred x y (my_op_sym x y)` — the satisfies axiom
3. `noncomputable def my_op : U₁ ⟴ U₂ ⟴ U₃ :=
      { graph := G,
        op := fun x => { graph := G.fiber x, op := my_op_sym x, satisfies := fun y => my_op_satisfies x y },
        satisfies := my_op_satisfies }`

This macro generates all three from a single line:

    binary_operation my_op : U₁ ⟴ U₂ ⟴ U₃ from G

The `from` term must have type `BinaryOperationGraph U₁ U₂ U₃`.

## Usage example

Given a binary operation graph `union_graph : BinaryOperationGraph (Set U) (Set U) (Set U)`:

    binary_operation union : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U from union_graph

This generates:
- `axiom union_sym : Set U → Set U → Set U`
- `axiom union_satisfies : ∀ A B, union_graph.pred A B (union_sym A B)`
- `noncomputable def union : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U`

After declaration, the following are available:
- `union x y`         — apply the operation (via curried CoeFun chain)
- `union x`           — partial application: a `UnaryOperation U₂ U₃`
- `union.graph`       — the ternary graph (exposes `.pred`, `.cong`, `.ltot`, `.rdet`)
- `union.satisfies`   — the satisfies axiom (`∀ x y, graph.pred x y (op x y)`)
- `union.def`         — derived defining iff `∀ x y z, (op x y =₍U₃₎ z) ↔ graph.pred x y z`
- `union.cong`        — derived congruence (conjunctive hypothesis)
- `(union x).graph`, `(union x).satisfies`, `(union x).def`, `(union x).cong` — fiber unary operation's data
-/
open Lean Elab Command in
elab "binary_operation " name:ident " : " U₁:term:max " ⟴ " U₂:term:max " ⟴ " U₃:term:max " from " graph:term : command => do
  let symName := mkIdent (name.getId.appendAfter "_sym")
  let satisfiesName := mkIdent (name.getId.appendAfter "_satisfies")
  -- Opaque binary function symbol.
  elabCommand (← `(axiom $symName : ($U₁ : Universal).Particular → ($U₂ : Universal).Particular → ($U₃ : Universal).Particular))
  -- Satisfies axiom: the binary symbol applied to its inputs lands in the graph.
  elabCommand (← `(axiom $satisfiesName : ∀ (x: ($U₁ : Universal).Particular), ∀ (y: ($U₂ : Universal).Particular),
    ($graph).pred x y ($symName x y)))
  -- The BinaryOperation value with curried op field. For each x, the fiber
  -- unary operation has graph = G.fiber x, op = sym x (partial app),
  -- and satisfies = the binary satisfies at fixed x (the fiber's pred at
  -- (y, z) reduces definitionally to the original pred at (x, y, z)).
  elabCommand (← `(noncomputable def $name : BinaryOperation $U₁ $U₂ $U₃ :=
    { graph := $graph
      op := fun x =>
        { graph := ($graph).fiber x
          op := $symName x
          satisfies := fun y => $satisfiesName x y }
      satisfies := $satisfiesName }))

end PC₁

end Logic
