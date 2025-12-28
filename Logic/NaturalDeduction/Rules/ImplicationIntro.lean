import Lean

namespace Logic

namespace ND

open Lean Meta Elab Tactic

-- Assume a premise
syntax (name := ndAssume) "assume" "(" ident ":" term ")": tactic

elab_rules (kind := ndAssume): tactic
  | `(tactic| assume ($h:ident: $ty)) => do
      let goal ← getMainGoal
      goal.withContext do
        let goalType ← goal.getType
        -- Reduce to weak head normal form to handle ¬P → (P → False)
        let goalTypeWhnf ← whnf goalType
        -- Check if goal is an implication/function type
        unless goalTypeWhnf.isForall do
          throwError "assume: goal must be an implication or function type, got {goalType}"
        -- Elaborate the expected type
        let expectedType ← Term.elabTerm ty none
        let actualType := goalTypeWhnf.bindingDomain!
        -- Check if the types match
        unless ← isDefEq expectedType actualType do
          throwError "assume: type mismatch\n  expected: {expectedType}\n  actual:   {actualType}"
        -- Introduce the hypothesis
        let (_, newGoal) ← goal.intro h.getId
        replaceMainGoal [newGoal]

-- Implication Introduction
syntax (name := ndImplicationIntro) "implication_intro" term "," term: tactic

elab_rules (kind := ndImplicationIntro): tactic
  | `(tactic| implication_intro $hyp , $hq) => do
      withMainContext do
        let goal ← getMainGoal
        let hypExpr ← Term.elabTerm hyp none
        unless hypExpr.isFVar do
          throwError "implication_intro expects a local hypothesis"
        let hqExpr ← Term.elabTerm hq none
        goal.assign hqExpr

end ND

end Logic
