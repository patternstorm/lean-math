namespace Logic

namespace ND

-- Negation elimination: from ¬¬P, derive P
syntax (name := ndNegElim) "neg_elim" term: tactic

macro_rules (kind := ndNegElim)
  | `(tactic| neg_elim $h) => `(tactic| exact Classical.byContradiction $h)

end ND

end Logic
