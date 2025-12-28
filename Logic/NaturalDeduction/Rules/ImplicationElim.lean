namespace Logic

namespace ND

-- Modus Ponens
def modusPonensFn {P Q: Prop} (hpq: P → Q) (hp: P): Q :=
  hpq hp

syntax (name := ndModusPonens) "modus_ponens" term "," term: tactic

macro_rules (kind := ndModusPonens)
  | `(tactic| modus_ponens $hpq , $hp) =>
      `(tactic| exact modusPonensFn $hpq $hp)

end ND

end Logic
