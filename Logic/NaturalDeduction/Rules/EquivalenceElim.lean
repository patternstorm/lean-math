import Lean

namespace Logic

namespace ND


open Lean Meta Elab Tactic

-- Double Implication elimination
syntax (name := ndIffElim) "iff_elim" term: tactic

elab_rules (kind := ndIffElim): tactic
  | `(tactic| iff_elim $h) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let hExpr ← Term.elabTerm h none
        let hType ← inferType hExpr
        match hType.consumeMData with
        | Expr.app (Expr.app (Expr.const ``Iff _) left) right =>
            let forwardType ← mkArrow left right
            let backwardType ← mkArrow right left
            if ← isDefEq targetType forwardType then
              let forward ← mkAppM ``Iff.mp #[hExpr]
              goal.assign forward
            else if ← isDefEq targetType backwardType then
              let backward ← mkAppM ``Iff.mpr #[hExpr]
              goal.assign backward
            else
              -- Check if goal is a conjunction
              match targetType.consumeMData with
              | Expr.app (Expr.app (Expr.const ``And _) goalLeft) goalRight =>
                  -- Check if it matches (forward ∧ backward) or (backward ∧ forward)
                  let matchesForwardBackward ← isDefEq goalLeft forwardType <&&> isDefEq goalRight backwardType
                  let matchesBackwardForward ← isDefEq goalLeft backwardType <&&> isDefEq goalRight forwardType
                  if matchesForwardBackward then
                    let forward ← mkAppM ``Iff.mp #[hExpr]
                    let backward ← mkAppM ``Iff.mpr #[hExpr]
                    let result ← mkAppM ``And.intro #[forward, backward]
                    goal.assign result
                  else if matchesBackwardForward then
                    let backward ← mkAppM ``Iff.mpr #[hExpr]
                    let forward ← mkAppM ``Iff.mp #[hExpr]
                    let result ← mkAppM ``And.intro #[backward, forward]
                    goal.assign result
                  else
                    throwError "iff_elim: goal is conjunction {targetType} but components don't match {forwardType} and {backwardType}"
              | _ =>
                  throwError "iff_elim: goal {targetType} does not match {forwardType}, {backwardType}, or a conjunction of them"
        | _ =>
            throwError "iff_elim: hypothesis must be an equivalence, got {hType}"

-- Double Implication elimination (left-to-right direction)
syntax (name := ndIffElimL2R) "iff_elim_l2r" term: tactic

macro_rules (kind := ndIffElimL2R)
  | `(tactic| iff_elim_l2r $h) => `(tactic| exact Iff.mp $h)

-- Double Implication elimination (right-to-left direction)
syntax (name := ndIffElimR2L) "iff_elim_r2l" term: tactic

macro_rules (kind := ndIffElimR2L)
  | `(tactic| iff_elim_r2l $h) => `(tactic| exact Iff.mpr $h)

end ND

end Logic
