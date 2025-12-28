namespace Logic

namespace ND

-- Introduce existential quantifier: provide witness and proof
syntax "exists_intro" term "," term: tactic
macro_rules
  | `(tactic| exists_intro $h, $t) => `(tactic| exact ⟨$t, $h⟩)

end ND

end Logic
