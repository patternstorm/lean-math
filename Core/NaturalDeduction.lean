import Lean

open Lean Meta Elab Tactic

-- Assume a premise
syntax (name := ndAssume) "assume" "(" ident ":" term ")" : tactic

elab_rules (kind := ndAssume) : tactic
  | `(tactic| assume ($h:ident : $ty)) => do
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

-- Introduce a variable
syntax (name := ndVariable) "variable" "(" ident ":" term ")" : tactic

macro_rules (kind := ndVariable)
  | `(tactic| variable ($x:ident : $_ty)) => `(tactic| intro $x:ident)

-- Introduce a constant from an inhabited type
syntax (name := ndConstant) "constant" "(" ident ":" term ")" : tactic

macro_rules (kind := ndConstant)
  | `(tactic| constant ($x:ident : $ty)) =>
      `(tactic|
        classical
        obtain ⟨$x⟩ := (inferInstance : Nonempty $ty)
      )

syntax (name := ndForallIntro) "forall_intro" tacticSeq : tactic

elab_rules (kind := ndForallIntro) : tactic
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
            let mut chosen : Option FVarId := none
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

-- Introduce existential quantifier: provide witness and proof
syntax "exists_intro" term "," term : tactic
macro_rules
  | `(tactic| exists_intro $h, $t) => `(tactic| exact ⟨$t, $h⟩)

-- Eliminate existential quantifier
def exists_elim {α : Type} {P : α → Prop} (h : ∃ x, P x) : ∃ x, P x := h

-- Eliminate universal quantifier: instantiate with a term
syntax "forall_elim" term "," term : tactic
macro_rules
  | `(tactic| forall_elim $h, $t) => `(tactic| exact $h $t)


-- Modus Ponens
def modusPonensFn {P Q : Prop} (hpq : P → Q) (hp : P) : Q :=
  hpq hp

syntax (name := ndModusPonens) "modus_ponens" term "," term : tactic

macro_rules (kind := ndModusPonens)
  | `(tactic| modus_ponens $hpq , $hp) =>
      `(tactic| exact modusPonensFn $hpq $hp)

-- Implication Introduction
syntax (name := ndImplicationIntro) "implication_intro" term "," term : tactic

elab_rules (kind := ndImplicationIntro) : tactic
  | `(tactic| implication_intro $hyp , $hq) => do
      withMainContext do
        let goal ← getMainGoal
        let hypExpr ← Term.elabTerm hyp none
        unless hypExpr.isFVar do
          throwError "implication_intro expects a local hypothesis"
        let hqExpr ← Term.elabTerm hq none
        goal.assign hqExpr

-- Double Implication introduction
syntax (name := ndIffIntro) "iff_intro" term "," term : tactic

macro_rules (kind := ndIffIntro)
  | `(tactic| iff_intro $hForward , $hBackward) =>
      `(tactic| exact Iff.intro $hForward $hBackward)

-- Double Implication elimination
syntax (name := ndIffElim) "iff_elim" term : tactic

elab_rules (kind := ndIffElim) : tactic
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

-- Deductive Equivalence substitution rule
syntax (name := ndDeductiveEq) "deductive_eq" term "," term : tactic

macro_rules (kind := ndDeductiveEq)
  | `(tactic| deductive_eq $hIff , $h) =>
      `(tactic|
        first
          | exact Iff.mp $hIff $h
          | exact Iff.mpr $hIff $h
      )

-- Contradiction, infers false from two contradictory propositions, the second is the negation of the first
syntax (name := ndContradiction) "contradiction" term "," term : tactic

elab_rules (kind := ndContradiction) : tactic
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

-- Negation elimination: from ¬¬P, derive P
syntax (name := ndNegElim) "neg_elim" term : tactic

macro_rules (kind := ndNegElim)
  | `(tactic| neg_elim $h) => `(tactic| exact Classical.byContradiction $h)

-- Iterate an existing premise somwhere else in the proof
syntax (name := ndIterate) "iterate" term : tactic

macro_rules (kind := ndIterate)
  | `(tactic| iterate $h) => `(tactic| exact $h)

-- And introduction: from P, Q, derive P ∧ Q
syntax (name := ndAndIntro) "and_intro" term "," term : tactic

macro_rules (kind := ndAndIntro)
  | `(tactic| and_intro $hLeft , $hRight) =>
      `(tactic| exact And.intro $hLeft $hRight)

-- And elimination: from P ∧ Q, derive P or derive Q
syntax (name := ndAndElim) "and_elim" term : tactic

elab_rules (kind := ndAndElim) : tactic
  | `(tactic| and_elim $h) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let hExpr ← Term.elabTerm h none
        let hType ← inferType hExpr
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

-- Or introduction: from P, derive P ∨ Q (or from Q, derive P ∨ Q)
syntax (name := ndOrIntro) "or_intro" term : tactic

elab_rules (kind := ndOrIntro) : tactic
  | `(tactic| or_intro $h) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
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

-- Or elimination: from P ∨ Q, P → R, Q → R, derive R
syntax (name := ndOrElim) "or_elimination" term "," term "," term : tactic

macro_rules (kind := ndOrElim)
  | `(tactic| or_elimination $hpq , $hpr , $hqr) =>
      `(tactic| exact Or.elim $hpq $hpr $hqr)

namespace pc₀ -- Propositional Calculus 0

theorem identity_principle {P : Prop}: P → P := by
  assume (h₁ : P)
  implication_intro h₁, h₁

theorem excluded_middle {P : Prop} : P ∨ ¬P := by
  have h₁: ¬(P ∨ ¬P) → False := by
    assume (h₁₁ : ¬(P ∨ ¬P))
    have h₁₂: P → False := by
      assume (h₁₂₁ : P)
      have h₁₂₂: P ∨ ¬P := by or_intro h₁₂₁
      contradiction h₁₂₂, h₁₁
    have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
    have h₁₄: ¬P → False := by
      assume (h₁₄₁ : ¬P)
      have h₁₄₂: P ∨ ¬P := by or_intro h₁₄₁
      contradiction h₁₄₂, h₁₁
    have h₁₅: ¬¬P := by reductio_ad_absurdum h₁₄
    contradiction h₁₃, h₁₅
  have h₂: ¬¬(P ∨ ¬P) := by reductio_ad_absurdum h₁
  neg_elim h₂

theorem non_contradiction {P : Prop} : ¬(P ∧ ¬P) := by
  have h₁: P ∧ ¬P → False := by
    assume (h₁₁ : P ∧ ¬P)
    have h₁₂: P := by and_elim h₁₁
    have h₁₃: ¬P := by and_elim h₁₁
    contradiction h₁₂, h₁₃
  reductio_ad_absurdum h₁

theorem hypothetical_syllogism {P Q R : Prop} (h1: P → Q) (h2: Q → R): P → R := by
  have h3: P → R := by
    assume (h3_1 : P)
    have h3_2: Q := by modus_ponens h1, h3_1
    have h3_3: R := by modus_ponens h2, h3_2
    implication_intro h3_1, h3_3
  iterate h3

theorem quodlibet_seqitur {P Q: Prop} (h₁: P) (h₂: ¬P): Q := by
  have h₃: ¬Q → False := by
    assume (h₃₁ : ¬Q)
    contradiction h₁, h₂
  have h₄: ¬¬Q := by reductio_ad_absurdum h₃
  neg_elim h₄

theorem disjunctive_syllogism {P Q : Prop} (h₁: P ∨ Q) (h₂: ¬P): Q := by
  have h₃: P → Q := by
    assume (h₃₁ : P)
    have h₃₂: Q := quodlibet_seqitur h₃₁ h₂
    implication_intro h₃₁, h₃₂
  have h₄: Q → Q := identity_principle
  or_elimination h₁, h₃, h₄

theorem modus_tollens {P Q : Prop} (h₁: P → Q) (h₂: ¬Q): ¬P := by
  have h₃: P → False := by
    assume (h₃₁ : P)
    have h₃₂: Q := by modus_ponens h₁, h₃₁
    contradiction h₃₂, h₂
  reductio_ad_absurdum h₃

theorem double_neg_intro {P : Prop} (h₁ : P) : ¬¬P := by
  have h₂: ¬P → False := by
    assume (h₂₁ : ¬P)
    contradiction h₁, h₂₁
  reductio_ad_absurdum h₂

theorem medieval_resolution {P Q R : Prop} (h₁: P → Q) (h₂: ¬P → R): Q ∨ R := by
  have h₃: P ∨ ¬P := excluded_middle
  have h₄: P → Q ∨ R := by
    assume (h₄₁ : P)
    have h₄₂: Q := by modus_ponens h₁, h₄₁
    have h₄₃: Q ∨ R := by or_intro h₄₂
    iterate h₄₃
  have h₅: ¬P → Q ∨ R := by
    assume (h₅₁ : ¬P)
    have h₅₂: R := by modus_ponens h₂, h₅₁
    have h₅₃: Q ∨ R := by or_intro h₅₂
    iterate h₅₃
  or_elimination h₃, h₄, h₅

theorem resolution_non_constructive {P Q R : Prop} (h₁: ¬P ∨ Q) (h₂: P ∨ R): Q ∨ R := by
  have h₃: P ∨ ¬P := excluded_middle
  have h₄: P → Q ∨ R := by
    assume (h₄₁ : P)
    have h₄₂: ¬P → Q := by
      assume (h₄₂₁ : ¬P)
      have h₄₃: Q := quodlibet_seqitur h₄₁ h₄₂₁
      iterate h₄₃
    have h₄₃: Q → Q := identity_principle
    have h₄₄: Q := by or_elimination h₁, h₄₂, h₄₃
    have h₄₅: Q ∨ R := by or_intro h₄₄
    iterate h₄₅
  have h₅: ¬P → Q ∨ R := by
    assume (h₅₁ : ¬P)
    have h₅₂: P → R := by
      assume (h₅₂₁ : P)
      have h₅₃: R := quodlibet_seqitur h₅₂₁ h₅₁
      iterate h₅₃
    have h₅₃: R → R := identity_principle
    have h₅₄: R := by or_elimination h₂, h₅₂, h₅₃
    have h₅₅: Q ∨ R := by or_intro h₅₄
    iterate h₅₅
  or_elimination h₃, h₄, h₅

theorem resolution_constructive {P Q R : Prop} (h₁: ¬P ∨ Q) (h₂: P ∨ R): Q ∨ R := by
  have h₃: ¬P → Q ∨ R := by
    assume (h₃₁ : ¬P)
    have h₃₂: P → Q ∨ R := by
      assume (h₃₂₁ : P)
      have h₃₂₂: Q := quodlibet_seqitur h₃₂₁ h₃₁
      have h₃₂₃: Q ∨ R := by or_intro h₃₂₂
      iterate h₃₂₃
    have h₃₃: R → Q ∨ R := by
      assume (h₃₃₁ : R)
      have h₃₃₂: Q ∨ R := by or_intro h₃₃₁
      iterate h₃₃₂
    or_elimination h₂, h₃₂, h₃₃
  have h₄: Q → Q ∨ R := by
    assume (h₄₁ : Q)
    have h₄₂: Q ∨ R := by or_intro h₄₁
    iterate h₄₂
  or_elimination h₁, h₃, h₄

theorem incompatbility {P Q : Prop} (h₁: ¬(P ∧ Q)) (h₂: P): ¬Q := by
  have h₃: Q → False := by
    assume (h₃₁: Q)
    have h₃₂: P ∧ Q := by and_intro h₂, h₃₁
    contradiction h₃₂, h₁
  reductio_ad_absurdum h₃

theorem positive_paradox {P Q : Prop}: P → (Q → P) := by
  assume (h₁ : P)
  assume (h₂ : Q)
  have h₃: P := by iterate h₁
  implication_intro h₂, h₃

theorem material_implication {P Q : Prop}: P → Q ↔ ¬P ∨ Q := by
  have h₁: (P → Q) → (¬P ∨ Q) := by
    assume (h₁₁ : P → Q)
    have h₁₂: P ∨ ¬P := excluded_middle
    have h₁₃: P → (¬P ∨ Q) := by
      assume (h₁₃₁ : P)
      have h₁₃₂: Q := by modus_ponens h₁₁, h₁₃₁
      have h₁₃₃: ¬P ∨ Q := by or_intro h₁₃₂
      iterate h₁₃₃
    have h₁₄: ¬P → (¬P ∨ Q) := by
      assume (h₁₄₁ : ¬P)
      have h₁₄₂: ¬P ∨ Q := by or_intro h₁₄₁
      iterate h₁₄₂
    or_elimination h₁₂, h₁₃, h₁₄
  have h₂: (¬P ∨ Q) → (P → Q) := by
    assume (h₂₁ : ¬P ∨ Q)
    have h₂₂: ¬P → (P → Q) := by
      assume (h₂₂₁ : ¬P)
      assume (h₂₂₂ : P)
      have h₂₃: Q := quodlibet_seqitur h₂₂₂ h₂₂₁
      iterate h₂₃
    have h₂₃: Q → (P → Q) := positive_paradox
    or_elimination h₂₁, h₂₂, h₂₃
  iff_intro h₁, h₂

theorem de_morgan_disjunction {P Q : Prop}: ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  have h₁: ¬(P ∨ Q) →  (¬P ∧ ¬Q) := by
    assume (h₁₁ : ¬(P ∨ Q))
    have h₁₂: P → False := by
      assume (h₁₂₁ : P)
      have h₁₂₂: P ∨ Q := by or_intro h₁₂₁
      contradiction h₁₂₂, h₁₁
    have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
    have h₁₄: Q → False := by
      assume (h₁₄₁ : Q)
      have h₁₄₂: P ∨ Q := by or_intro h₁₄₁
      contradiction h₁₄₂, h₁₁
    have h₁₅: ¬Q := by reductio_ad_absurdum h₁₄
    and_intro h₁₃, h₁₅
  have h₂: (¬P ∧ ¬Q) → ¬(P ∨ Q) := by
    assume (h₂₁ : ¬P ∧ ¬Q)
    have h₂₂: (P ∨ Q) → False := by
      assume (h₂₂₁ : P ∨ Q)
      have h₂₂₂: ¬P := by and_elim h₂₁
      have h₂₂₃: Q := disjunctive_syllogism h₂₂₁ h₂₂₂
      have h₂₂₄: ¬Q := by and_elim h₂₁
      contradiction h₂₂₃, h₂₂₄
    reductio_ad_absurdum h₂₂
  iff_intro h₁, h₂

theorem de_morgan_conjunction {P Q : Prop}: ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  have h₁: ¬(¬P ∨ ¬Q) ↔ (¬¬P ∧ ¬¬Q) := de_morgan_disjunction
  have h₂: ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
    assume (h₂₁ : ¬(P ∧ Q))
    have h₂₂: P → ¬Q := by
      assume (h₂₂₁ : P)
      have h₂₂₂: Q → False := by
        assume (h₂₂₂₁ : Q)
        have h₂₂₂₂: P ∧ Q := by and_intro h₂₂₁, h₂₂₂₁
        contradiction h₂₂₂₂, h₂₁
      reductio_ad_absurdum h₂₂₂
    have h₂₃: (P → ¬Q) ↔ (¬P ∨ ¬Q) := material_implication
    have h₂₃: ((P → ¬Q) → (¬P ∨ ¬Q)) ∧ ((¬P ∨ ¬Q) → (P → ¬Q)) := by iff_elim h₂₃
    have h₂₄: (P → ¬Q) → (¬P ∨ ¬Q) := by and_elim h₂₃
    modus_ponens h₂₄, h₂₂
  have h₃: (¬P ∨ ¬Q) → ¬(P ∧ Q) := by
    assume (h₃₁ : ¬P ∨ ¬Q)
    have h₃₂: (P ∧ Q) → False := by
      assume (h₃₂₁ : P ∧ Q)
      have h₃₂₂: P := by and_elim h₃₂₁
      have h₃₂₃: ¬¬P := double_neg_intro h₃₂₂
      have h₃₂₄: ¬Q := disjunctive_syllogism h₃₁ h₃₂₃
      have h₃₂₅: Q := by and_elim h₃₂₁
      contradiction h₃₂₅, h₃₂₄
    reductio_ad_absurdum h₃₂
  iff_intro h₂, h₃

  theorem implication_reversibility {P Q : Prop}: (P → Q) ↔ (¬Q → ¬P) := by
    have h₁: (P → Q) → (¬Q → ¬P) := by
      assume( h₁: P → Q)
      assume (h₁₁ : ¬Q)
      have h₁₂: P → False := by
        assume (h₁₂₁ : P)
        have h₁₂₂: Q := by modus_ponens h₁, h₁₂₁
        contradiction h₁₂₂, h₁₁
      have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
      implication_intro h₁₁, h₁₃
    have h₂: (¬Q → ¬P) → (P → Q) := by
      assume (h₂₁ : ¬Q → ¬P)
      assume (h₂₂ : P)
      have h₂₃: ¬Q → False := by
        assume (h₂₃₁ : ¬Q)
        have h₂₃₂: ¬P := by modus_ponens h₂₁, h₂₃₁
        contradiction h₂₂, h₂₃₂
      have h₂₄: ¬¬Q := by reductio_ad_absurdum h₂₃
      have h₂₅: Q := by neg_elim h₂₄
      implication_intro h₂₂, h₂₅
    iff_intro h₁, h₂

theorem currying {P Q R : Prop}: (P → (Q → R)) ↔ (P ∧ Q → R) := by
  have h₁: (P → (Q → R)) → (P ∧ Q → R) := by
    assume (h₁₁ : P → (Q → R))
    assume (h₁₂ : P ∧ Q)
    have h₁₃: P := by and_elim h₁₂
    have h₁₄: Q → R := by modus_ponens h₁₁, h₁₃
    have h₁₅: Q := by and_elim h₁₂
    have h₁₆: R := by modus_ponens h₁₄, h₁₅
    implication_intro h₁₂, h₁₆
  have h₂: (P ∧ Q → R) → (P → (Q → R)) := by
    assume (h₂₁ : P ∧ Q → R)
    assume (h₂₂ : P)
    have h₂₆: Q → R := by
      assume (h₂₃ : Q)
      have h₂₄: P ∧ Q := by and_intro h₂₂, h₂₃
      modus_ponens h₂₁, h₂₄
    implication_intro h₂₂, h₂₆
  iff_intro h₁, h₂

example {P Q R S : Prop} (h₁: P ∧ Q → R) (h₂: (¬P ∧ ¬Q) → S) (h₃: P ↔ Q): R ∨ S := by
  have h₄: P ∨ ¬P := excluded_middle
  have h₅: (P → Q) ∧ (Q → P) := by iff_elim h₃
  have h₆: P → R ∨ S := by
    assume (h₆₁ : P)
    have h₆₂: P → Q := by and_elim h₅
    have h₆₃: Q := by modus_ponens h₆₂, h₆₁
    have h₆₄: P ∧ Q := by and_intro h₆₁, h₆₃
    have h₆₅: R := by modus_ponens h₁, h₆₄
    have h₆₆: R ∨ S := by or_intro h₆₅
    iterate h₆₆
  have h₇ : ¬P → R ∨ S := by
    assume (h₇₁ : ¬P)
    have h₇₂: Q → P := by and_elim h₅
    have h₇₃: (Q → P) ↔ (¬P → ¬Q) := implication_reversibility
    have h₇₄: ((Q → P) → (¬P → ¬Q)) ∧ ((¬P → ¬Q) → (Q → P)) := by iff_elim h₇₃
    have h₇₅: (Q → P) → (¬P → ¬Q) := by and_elim h₇₄
    have h₇₆: ¬P → ¬Q := by modus_ponens h₇₅, h₇₂
    have h₇₇: ¬Q := by modus_ponens h₇₆, h₇₁
    have h₇₈: ¬P ∧ ¬Q := by and_intro h₇₁, h₇₇
    have h₇₉: S := by modus_ponens h₂, h₇₈
    have h₇₁₀: R ∨ S := by or_intro h₇₉
    iterate h₇₁₀
  or_elimination h₄, h₆, h₇

end pc₀

namespace pc₁ -- Propositional Calculus 1

theorem forall_comm {α: Type} {P: α → α → Prop}: (∀ x, ∀ y, P x y) ↔  (∀ y, ∀ x, P x y) := by
  have h₁: (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
    assume (h₁₁ : ∀ x, ∀ y, P x y)
    have h₁₁: ∀ y, ∀ x, P x y := by forall_intro
        variable (u : α)
        variable (v : α)
        have h₁₁₂: ∀ y, P v y := by forall_elim h₁₁, v
        have h₁₁₃: P v u := by forall_elim h₁₁₂, u
    iterate h₁₁
  have h₂: (∀ y, ∀ x, P x y) → (∀ x, ∀ y, P x y) := by
    assume (h₂₁ : ∀ y, ∀ x, P x y)
    have h₂₁: ∀ x, ∀ y, P x y := by forall_intro
        variable (u : α)
        variable (v : α)
        have h₂₁₂: ∀ x, P x v := by forall_elim h₂₁, v
        have h₂₁₃: P u v := by forall_elim h₂₁₂, u
    iterate h₂₁
  iff_intro h₁, h₂

theorem exists_comm {α: Type} {P: α → α → Prop}: (∃ x, ∃ y, P x y) ↔ (∃ y, ∃ x, P x y) := by
  have h₁: (∃ x, ∃ y, P x y) →  (∃ y, ∃ x, P x y) := by
    assume (h₁₁: ∃ x, ∃ y, P x y)
    have ⟨(a: α), (h₁₂: ∃ y, P a y)⟩ := exists_elim h₁₁
    have ⟨(b: α), (h₁₃: P a b)⟩ := exists_elim h₁₂
    have h₁₄: ∃ x, P x b := by exists_intro h₁₃, a
    have h₁₅: ∃ y, ∃ x, P x y := by exists_intro h₁₄, b
    iterate h₁₅
  have h₂: (∃ y, ∃ x, P x y) →  (∃ x, ∃ y, P x y) := by
    assume (h₂₁: ∃ y, ∃ x, P x y)
    have ⟨(a: α), (h₂₂: ∃ x, P x a)⟩ := exists_elim h₂₁
    have ⟨(b: α), (h₂₃: P b a)⟩ := exists_elim h₂₂
    have h₂₄: ∃ y, P b y := by exists_intro h₂₃, a
    have h₂₅: ∃ x, ∃ y, P x y := by exists_intro h₂₄, b
    iterate h₂₅
  iff_intro h₁, h₂

theorem diagonal_specialization {α: Type} {P: α → α → Prop}: (∀ x, ∀ y, P x y) → (∀ x, P x x) := by
  assume (h₁: ∀ x, ∀ y, P x y)
  have h₂: ∀ x, P x x := by forall_intro
    variable (u : α)
    have h₂₁: ∀ y, P u y := by forall_elim h₁, u
    have h₂₂: P u u := by forall_elim h₂₁, u
    iterate h₂₂
  iterate h₂

theorem diagonal_generalization {α: Type} {P: α → α → Prop}: (∃ x, P x x) → (∃ x, ∃ y, P x y) := by
  assume (h₁: ∃ x, P x x)
  have ⟨(a: α), (h₁₁: P a a)⟩ := exists_elim h₁
  have h₁₂: ∃ y, P a y := by exists_intro h₁₁, a
  have h₁₃: ∃ x, ∃ y, P x y := by exists_intro h₁₂, a
  iterate h₁₃

theorem fol {α: Type} [Nonempty α] {P: α → Prop}: (∀ x, P x) → (∃ x, P x) := by
  assume (h₁: ∀ x, P x)
  constant (a : α)
  have h₂: P a := by forall_elim h₁, a
  have h₃: ∃ x, P x := by exists_intro h₂, a
  iterate h₃

theorem exists_forall_imp_forall_exists {α: Type} {P: α → α → Prop}: (∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y) := by
  assume( h₁: ∃ x, ∀ y, P x y)
  have h₂: ∀ y, ∃ x, P x y := by forall_intro
    variable (u : α)
    have ⟨(a: α), (h₂₂: ∀ y, P a y)⟩ := exists_elim h₁
    have h₂₃: P a u := by forall_elim h₂₂, u
    have h₂₄: ∃ x, P x u := by exists_intro h₂₃, a
    iterate h₂₄
  iterate h₂

theorem de_morgan_forall {α: Type} [Nonempty α] {P Q: α → Prop}: (¬(∀ x, P x)) ↔ (∃ x, ¬P x) := by
  have h₁: (¬(∀ x, P x)) → (∃ x, ¬P x) := by
    assume (h₁₁: ¬(∀ x, P x))
    sorry
  have h₂: (∃ x, ¬P x) → (¬(∀ x, P x)) := by
    assume (h₂₁: ∃ x, ¬P x)
    have ⟨(a: α), (h₂₂₁: ¬P a)⟩ := exists_elim h₂₁
    have h₂₃: (∀ x, P x) -> False := by
      assume (h₂₃₁: ∀ x, P x)
      have h₂₃₂: P a := by forall_elim h₂₃₁, a
      contradiction h₂₃₂, h₂₂₁
    have h₂₄: ¬(∀ x, P x) := by reductio_ad_absurdum h₂₃
    iterate h₂₃
  iff_intro h₁, h₂

example {α : Type} {P Q R S: α → Prop} (h1: ∀ x, P x → Q x) (h2: ∃ x, R x ∧ S x) (h3: ∀ x, S x → P x): ∃ x, P x ∧ Q x := by
  have ⟨(a: α), (h4: R a ∧ S a)⟩ :=  exists_elim h2
  have h5: ∃ y, R y ∧ S y := by exists_intro h4, a
  sorry

end pc₁
