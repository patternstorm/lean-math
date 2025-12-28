import Lean

namespace Logic

namespace ND

open Lean Meta Elab Tactic

-- Contradiction, infers false from two contradictory propositions, the second is the negation of the first
syntax (name := ndContradiction) "contradiction" term "," term : tactic

elab_rules (kind := ndContradiction): tactic
  | `(tactic| contradiction $hp , $hn) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let hpExpr ← Term.elabTerm hp none
        let hnExpr ← Term.elabTerm hn none
        let falseProof := mkApp hnExpr hpExpr
        let result := mkApp2 (mkConst ``False.elim [levelZero]) targetType falseProof
        goal.assign result

-- Reductio ad absurdum: from P → False, derive ¬P
syntax (name := ndReductio) "reductio_ad_absurdum" term : tactic

macro_rules (kind := ndReductio)
  | `(tactic| reductio_ad_absurdum $h) => `(tactic| exact $h)

end ND

end Logic
