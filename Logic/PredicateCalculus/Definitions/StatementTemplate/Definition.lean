namespace Logic

namespace PC₁

-- Syntax for "Statement Templates", i.e. `Predicates` with free variables
-- Allows writing: (x: T ↦ body) instead of fun x: T => body
macro "(" x:ident ":" t:term " ↦ " y:term ")" : term => do
    `(fun $x : $t => $y)

end PC₁

end Logic
