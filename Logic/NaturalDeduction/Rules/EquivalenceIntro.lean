namespace Logic

namespace ND


-- Double Implication introduction
syntax (name := ndIffIntro) "iff_intro" term "," term: tactic

macro_rules (kind := ndIffIntro)
  | `(tactic| iff_intro $hForward , $hBackward) =>
      `(tactic| exact Iff.intro $hForward $hBackward)

end ND

end Logic
