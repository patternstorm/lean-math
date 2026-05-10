import Lean

namespace Logic

namespace ND

open Lean Meta Elab Tactic

-- Or introduction: from P, derive P ∨ Q (or from Q, derive P ∨ Q)
syntax (name := ndOrIntro) "or_intro" term: tactic

elab_rules (kind := ndOrIntro) : tactic
  | `(tactic| or_intro $h) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← instantiateMVars (← whnf (← goal.getType))
        let hExpr ← Term.elabTerm h none
        let hType ← inferType hExpr
        -- Check if goal is P ∨ Q
        match targetType with
        | Expr.app (Expr.app (Expr.const ``Or _) left) right =>
            -- Try left injection first
            if ← isDefEq hType left then
              let result := mkApp (mkApp2 (mkConst ``Or.inl) left right) hExpr
              goal.assign result
            -- Otherwise try right injection
            else if ← isDefEq hType right then
              let result := mkApp (mkApp2 (mkConst ``Or.inr) left right) hExpr
              goal.assign result
            else
              throwError "or_intro: hypothesis type {hType} does not match either side of {targetType}"
        | _ =>
            throwError "or_intro: goal must be a disjunction P ∨ Q, got {targetType}"

end ND

end Logic
