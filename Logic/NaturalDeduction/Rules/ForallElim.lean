namespace Logic

namespace ND

-- Eliminate universal quantifier: instantiate with one or more terms.
-- forall_elim h, t             — single ∀-elimination
-- forall_elim h, t₁, t₂       — two ∀-eliminations (left to right)
-- forall_elim h, t₁, t₂, t₃   — three ∀-eliminations (left to right)
-- forall_elim h, t₁, t₂, t₃, t₄ — four ∀-eliminations (left to right)

-- Longer alternatives first so the parser tries them before the shorter one.
syntax "forall_elim" term "," term "," term "," term "," term : tactic
syntax "forall_elim" term "," term "," term "," term : tactic
syntax "forall_elim" term "," term "," term : tactic
syntax "forall_elim" term "," term : tactic

macro_rules
  | `(tactic| forall_elim $h, $t) => `(tactic| exact $h $t)

macro_rules
  | `(tactic| forall_elim $h, $t₁, $t₂) =>
    `(tactic| forall_elim ($h $t₁), $t₂)

macro_rules
  | `(tactic| forall_elim $h, $t₁, $t₂, $t₃) =>
    `(tactic| forall_elim ($h $t₁), $t₂, $t₃)

macro_rules
  | `(tactic| forall_elim $h, $t₁, $t₂, $t₃, $t₄) =>
    `(tactic| forall_elim ($h $t₁), $t₂, $t₃, $t₄)

end ND

end Logic
