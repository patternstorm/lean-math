import Lean

macro x:ident ":" t:term " ↦ " y:term : term => do
`(fun $x : $t => $y)

#eval (x: Nat ↦ x + 1) 2
