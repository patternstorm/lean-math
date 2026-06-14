import Logic.PredicateCalculus.Schemas.Operations.Binary.Schema
import Lean

namespace Logic

namespace PC₁

/-!
# `binary_operation` — convenience macro

Declaring a `BinaryOperation` manually requires three steps:

1. `axiom my_op_sym : U₁.Particular → U₂.Particular → U₃.Particular` — the binary function symbol
2. `axiom my_op_def : ∀ x y z, (my_op_sym x y =₍U₃₎ z) ↔ G.pred x y z` — defining axiom
3. `noncomputable def my_op : U₁ ⟴ U₂ ⟴ U₃ :=
      { graph := G,
        op := fun x => { graph := G.fiber x, op := my_op_sym x, def := my_op_def x },
        def := my_op_def }`

This macro generates all three from a single line:

    binary_operation my_op : U₁ ⟴ U₂ ⟴ U₃ from G

The `from` term must have type `BinaryOperationGraph U₁ U₂ U₃`.

## Usage example

Given a binary operation graph `union_graph : BinaryOperationGraph (Set U) (Set U) (Set U)`:

    binary_operation union : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U from union_graph

This generates:
- `axiom union_sym : Set U → Set U → Set U`
- `axiom union_def : ∀ x y z, (union_sym x y =ₛₑₜ z) ↔ union_graph.pred x y z`
- `noncomputable def union : 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U ⟴ 𝐒𝐞𝐭 U`

After declaration, the following are available:
- `union x y`     — apply the operation (via curried CoeFun chain)
- `union x`       — partial application: a `UnaryOperation U₂ U₃`
- `union.graph`   — the ternary graph (exposes `.pred`, `.cong`, `.ltot`, `.rdet`)
- `union.def`     — the defining axiom (usable via `forall_elim`)
- `union.cong`    — congruence (derived theorem)
- `(union x).graph`, `(union x).def`, `(union x).cong` — the fiber unary operation's data
-/
open Lean Elab Command in
elab "binary_operation " name:ident " : " U₁:term:max " ⟴ " U₂:term:max " ⟴ " U₃:term:max " from " graph:term : command => do
  let symName := mkIdent (name.getId.appendAfter "_sym")
  let defName := mkIdent (name.getId.appendAfter "_def")
  -- Opaque binary function symbol.
  elabCommand (← `(axiom $symName : ($U₁ : Universal).Particular → ($U₂ : Universal).Particular → ($U₃ : Universal).Particular))
  -- Defining axiom: relates the binary symbol to the graph's ternary predicate.
  elabCommand (← `(axiom $defName : ∀ (x: ($U₁ : Universal).Particular), ∀ (y: ($U₂ : Universal).Particular), ∀ (z: ($U₃ : Universal).Particular),
    ($symName x y =₍$U₃₎ z) ↔ ($graph).pred x y z))
  -- The BinaryOperation value with curried op field. For each x, the fiber
  -- unary operation has graph = G.fiber x, op = sym x (partial app),
  -- and def = the binary def at fixed x.
  elabCommand (← `(noncomputable def $name : BinaryOperation $U₁ $U₂ $U₃ :=
    { graph := $graph
      op := fun x =>
        { graph := ($graph).fiber x
          op := $symName x
          «def» := fun y z => $defName x y z }
      «def» := $defName }))

end PC₁

end Logic
