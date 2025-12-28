namespace Logic

namespace ND

-- Eliminate universal quantifier: instantiate with a term
syntax "forall_elim" term "," term: tactic
macro_rules
  | `(tactic| forall_elim $h, $t) => `(tactic| exact $h $t)

end ND

end Logic
