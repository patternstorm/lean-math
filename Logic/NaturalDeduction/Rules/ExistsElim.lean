namespace Logic

namespace ND

-- Eliminate existential quantifier
def exists_elim {α: Type} {P: α → Prop} (h: ∃ x, P x): ∃ x, P x := h

end ND

end Logic
