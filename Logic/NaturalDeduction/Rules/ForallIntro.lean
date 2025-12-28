import Lean

namespace Logic

namespace ND

open Lean Meta Elab Tactic

syntax (name := ndForallIntro) "forall_intro" tacticSeq: tactic

elab_rules (kind := ndForallIntro): tactic
  | `(tactic| forall_intro $body) => do
      let goal ← getMainGoal
      let originalLocals ← goal.withContext do
        pure (← getLCtx).getFVarIds
      evalTactic body
      let goals ← getGoals
      match goals with
      | [] => pure ()
      | g :: rest => do
          let chosenFVarId ← g.withContext do
            let goalType ← g.getType
            let lctx ← getLCtx
            let mut chosen: Option FVarId := none
            for decl in lctx.decls.toList.reverse do
              if let some decl := decl then
                unless originalLocals.contains decl.fvarId do
                  if ← isDefEq decl.type goalType then
                    chosen := some decl.fvarId
                    break
            match chosen with
            | some fVarId => pure fVarId
            | none => throwError "forall_intro: unable to find hypothesis matching current goal"
          g.assign (mkFVar chosenFVarId)
          setGoals rest

-- Introduce a variable
syntax (name := ndVariable) "variable" "(" ident ":" term ")": tactic

elab_rules (kind := ndVariable): tactic
  | `(tactic| variable ($x:ident: $ty)) => do
      let goal ← getMainGoal
      goal.withContext do
        let goalType ← goal.getType
        let goalTypeWhnf ← whnf goalType
        unless goalTypeWhnf.isForall do
          throwError "variable: goal must be a forall type, got {goalType}"
        let expectedType ← Term.elabTerm ty none
        let actualType := goalTypeWhnf.bindingDomain!
        unless ← isDefEq expectedType actualType do
          throwError "variable: type mismatch\n  expected: {expectedType}\n  actual:   {actualType}"
        let (_, newGoal) ← goal.intro x.getId
        replaceMainGoal [newGoal]

-- Introduce a constant from an inhabited type
syntax (name := ndConstant) "constant" "(" ident ":" term ")": tactic

macro_rules (kind := ndConstant)
  | `(tactic| constant ($x:ident: $ty)) =>
      `(tactic|
        classical
        obtain ⟨$x⟩ := (inferInstance: Nonempty $ty)
      )

end ND

end Logic
