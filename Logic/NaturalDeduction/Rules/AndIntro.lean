namespace Logic

namespace ND


-- And introduction: from P, Q, derive P ∧ Q
syntax (name := ndAndIntro) "and_intro" term "," term: tactic

macro_rules (kind := ndAndIntro)
  | `(tactic| and_intro $hLeft , $hRight) =>
      `(tactic| exact And.intro $hLeft $hRight)

end ND

end Logic
