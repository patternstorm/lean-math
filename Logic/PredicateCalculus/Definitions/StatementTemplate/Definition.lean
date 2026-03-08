namespace Logic

namespace PC₁

-- # Statement Template Binder
-- A custom syntax category for predicate variable bindings (x: T).
-- Using a dedicated category prevents the term parser from greedily
-- consuming commas that separate multiple binders.
declare_syntax_cat stmtBinder
syntax ident ":" term : stmtBinder

-- # Statement Templates
-- Syntax for "Statement Templates", i.e. `Predicates` with free variables.
-- Allows writing: (x: T ↦ body) instead of fun x: T => body.
-- Supports unary, binary, and ternary predicates.

-- Unary: (x: T ↦ body)
syntax:max "(" stmtBinder " ↦ " term ")" : term
macro_rules
  | `(($x:ident : $t:term ↦ $y)) => `(fun $x : $t => $y)

-- Binary: (x: T₁, y: T₂ ↦ body)
syntax:max "(" stmtBinder ", " stmtBinder " ↦ " term ")" : term
macro_rules
  | `(($x₁:ident : $t₁:term, $x₂:ident : $t₂:term ↦ $y)) =>
    `(fun $x₁ : $t₁ => fun $x₂ : $t₂ => $y)

-- Ternary: (x: T₁, y: T₂, z: T₃ ↦ body)
syntax:max "(" stmtBinder ", " stmtBinder ", " stmtBinder " ↦ " term ")" : term
macro_rules
  | `(($x₁:ident : $t₁:term, $x₂:ident : $t₂:term, $x₃:ident : $t₃:term ↦ $y)) =>
    `(fun $x₁ : $t₁ => fun $x₂ : $t₂ => fun $x₃ : $t₃ => $y)

end PC₁

end Logic
