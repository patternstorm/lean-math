namespace Logic

namespace ND

-- Truth introduction: allows introducing a prop that reduces/is equivalent to True
syntax (name := ndTrueIntro) "true_intro": tactic

macro_rules (kind := ndTrueIntro)
  | `(tactic| true_intro) => `(tactic| exact True.intro)

end ND

end Logic
