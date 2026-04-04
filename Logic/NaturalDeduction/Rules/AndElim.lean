import Lean

namespace Logic

namespace ND

open Lean Meta Elab Tactic

-- And elimination: from P ∧ Q, derive P or derive Q
syntax (name := ndAndElim) "and_elim" term: tactic

elab_rules (kind := ndAndElim) : tactic
  | `(tactic| and_elim $h) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let hExpr ← Term.elabTerm h none
        let hType ← inferType hExpr
        let hType ← whnf hType
        match hType.consumeMData with
        | Expr.app (Expr.app (Expr.const ``And _) left) right =>
            if ← isDefEq targetType left then
              let result ← mkAppM ``And.left #[hExpr]
              goal.assign result
            else if ← isDefEq targetType right then
              let result ← mkAppM ``And.right #[hExpr]
              goal.assign result
            else
              throwError "and_elim: goal {targetType} does not match components {left} or {right}"
        | _ =>
            throwError "and_elim: hypothesis must be a conjunction, got {hType}"

end ND

end Logic
