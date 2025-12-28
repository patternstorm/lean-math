namespace Logic

namespace ND

-- Iterate an existing premise somwhere else in the proof
syntax (name := ndIterate) "iterate" term: tactic

macro_rules (kind := ndIterate)
  | `(tactic| iterate $h) => `(tactic| exact $h)

end ND

end Logic
