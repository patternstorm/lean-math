namespace Logic

namespace ND

-- Or elimination: from P ∨ Q, P → R, Q → R, derive R
syntax (name := ndOrElim) "or_elimination" term "," term "," term: tactic

macro_rules (kind := ndOrElim)
  | `(tactic| or_elimination $hpq , $hpr , $hqr) =>
      `(tactic| exact Or.elim $hpq $hpr $hqr)

end ND

end Logic
