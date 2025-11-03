-- NATURAL DEDUCTION TACTICS - READABLE STYLE
-- Explicit, self-documenting tactics that make proofs read like natural deduction

import Lean

open Lean Elab Tactic Meta

/-!
# Readable Natural Deduction Tactics

These tactics are designed to make proofs read like traditional natural deduction:
- Explicit about what is being introduced or eliminated
- Clear rule names that match standard notation
- Self-documenting proof steps
-/

/-!
## Conjunction (∧)
-/

/-- Introduce a conjunction: from proofs of P and Q, conclude P ∧ Q -/
syntax "and_intro" term "," term : tactic
macro_rules
  | `(tactic| and_intro $hp, $hq) => `(tactic| exact ⟨$hp, $hq⟩)

/-- Eliminate conjunction (left): from P ∧ Q, extract P -/
syntax "and_elim_left" term : tactic
macro_rules
  | `(tactic| and_elim_left $h) => `(tactic| exact ($h).left)

/-- Eliminate conjunction (right): from P ∧ Q, extract Q -/
syntax "and_elim_right" term : tactic
macro_rules
  | `(tactic| and_elim_right $h) => `(tactic| exact ($h).right)

/-!
## Disjunction (∨)
-/

/-- Introduce disjunction (left): from P, conclude P ∨ Q -/
syntax "or_intro_left" term : tactic
macro_rules
  | `(tactic| or_intro_left $hp) => `(tactic| exact Or.inl $hp)

/-- Introduce disjunction (right): from Q, conclude P ∨ Q -/
syntax "or_intro_right" term : tactic
macro_rules
  | `(tactic| or_intro_right $hq) => `(tactic| exact Or.inr $hq)

/-- Eliminate disjunction: case analysis on P ∨ Q -/
syntax "or_elim" ident "with" ppLine "| " "left " ident " => " tacticSeq ppLine "| " "right " ident " => " tacticSeq : tactic
macro_rules
  | `(tactic| or_elim $h:ident with
      | left $n1:ident => $t1:tacticSeq
      | right $n2:ident => $t2:tacticSeq) =>
    `(tactic| cases $h:ident with
      | inl $n1 => $t1
      | inr $n2 => $t2)

/-!
## Implication (→)
-/

/-- Assume antecedent: introduce assumption for implication -/
syntax "assume" "(" ident ":" term ")" : tactic
macro_rules
  | `(tactic| assume ($n:ident : $t:term)) => `(tactic| intro $n:ident)

/-- Eliminate implication (modus ponens): from P → Q and P, conclude Q -/
syntax "modus_ponens" term "by" term : tactic
macro_rules
  | `(tactic| modus_ponens $hpq by $hp) => `(tactic| exact $hpq $hp)

/-!
## Negation (¬)
-/

/-- Prove by negation: assume P and derive contradiction to prove ¬P -/
macro "prove_by_negation" "(" n:ident ":" _t:term ")" " { " body:tacticSeq " } " : tactic =>
  `(tactic| intro $n:ident <;> ($body))

/-- Introduce negation: assume P to derive contradiction -/
syntax "assume_neg" "(" ident ":" term ")" : tactic
macro_rules
  | `(tactic| assume_neg ($n:ident : $t:term)) => `(tactic| intro $n:ident)

/-- Eliminate negation: from ¬P and P, derive contradiction -/
syntax "contradiction" term "," term : tactic
macro_rules
  | `(tactic| contradiction $hnp, $hp) => `(tactic| exact $hnp $hp)

/-- Ex falso quodlibet: from False, prove anything -/
syntax "ex_falso" term : tactic
macro_rules
  | `(tactic| ex_falso $h) => `(tactic| exact False.elim $h)
/-!

## Universal Quantification (∀)
-/

/-- Collect variables that should be generalized (both free in proof and parameters) -/
private def getTrueFreeVars (proof : Expr) (lctx : LocalContext) : List FVarId :=
  let step := fun acc (optDecl : Option LocalDecl) =>
    match optDecl with
    | some decl =>
      -- Include if: appears in proof OR is a parameter that needs generalization
      if proof.containsFVar decl.fvarId then
        decl.fvarId :: acc
      else acc
    | none => acc
  lctx.decls.foldl step []

private def getTrueFreeVars2 (proof : Expr) (lctx : LocalContext) : List FVarId :=
  let step := fun (acc : List FVarId) (optDecl : Option LocalDecl) =>
    match optDecl with
    | some decl =>
      if proof.containsFVar decl.fvarId && decl.value?.isNone &&
         decl.userName.toString.startsWith "_fv_" then
        decl.fvarId :: acc
      else
        acc  -- Return accumulator unchanged instead of none
    | none => acc
  lctx.decls.foldl step []

/-- Introduce universal quantifier: generalize from proof with free variables -/
syntax "forall_intro" term : tactic

elab "forall_intro" proofTerm:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let proof ← elabTerm proofTerm none
    let goalType ← goal.getType
    let lctx ← getLCtx
    let freeVars := getTrueFreeVars proof lctx

    for fvarId in freeVars do
      let decl ← fvarId.getDecl
      let fvar := mkFVar fvarId
      -- Create new variable with same name
      let newVar ← mkFreshExprMVar decl.type (userName := decl.userName)
      -- Replace all occurrences
      let newProof := proof.replaceFVar fvar newVar
      -- Create lambda abstraction
      let abstracted ← mkLambdaFVars #[newVar] newProof

      if ← isDefEq (← inferType abstracted) goalType then
        goal.assign abstracted
        return
      else
        throwError m!"Cannot generalize {fvar}. Expected {goalType}, got {← inferType abstracted}"

    throwError "forall_intro: no variables could be generalized"

private def getIntroVars (proof : Expr) (lctx : LocalContext) : Array Expr :=
  let vars := lctx.decls.toList.filterMap fun optDecl =>
    match optDecl with
    | some decl =>
      if decl.isAuxDecl && decl.value?.isNone && !decl.type.isForall &&
          proof.containsFVar decl.fvarId then
        some (mkFVar decl.fvarId)
      else
        none
    | none => none
  vars.reverse.toArray

elab "forall_intro2" proofTerm:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let proofExpr ← elabTerm proofTerm none
    let proof ← match proofExpr with
      | .fvar fvarId => do
        let decl ← fvarId.getDecl
        match decl.value? with
        | some v => pure v
        | none => pure proofExpr
      | e => pure e

    let introVars := getIntroVars proof (← getLCtx)
    let mut abstracted := proof

    for var in introVars do
      abstracted ← mkLambdaFVars #[var] abstracted

    if (← inferType abstracted).isForall then
      goal.assign abstracted
    else
      throwError "Cannot generalize - no intro variables found"

/-- Eliminate universal quantifier: instantiate with a term -/
syntax "forall_elim" term "," term : tactic
macro_rules
  | `(tactic| forall_elim $h, $t) => `(tactic| exact $h $t)

syntax "forall_elim2" term : tactic

elab "forall_elim2" h:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let hExpr ← elabTerm h none
    let (newVar, prf) ←
      withLocalDecl `z .default (← inferType hExpr).bindingDomain! fun z => do
        let inst := mkApp hExpr z
        pure (z, inst)

    -- Create a Sigma type (Σ z : Nat, ∀ y, P z y)
    let sigmaType ← mkAppM ``Sigma #[← inferType newVar, ← inferType prf]
    let sigma ← mkAppM ``Sigma.mk #[newVar, prf]
    goal.assign sigma
    replaceMainGoal []

/-- Introduce existential quantifier: provide witness and proof -/
syntax "exists_intro" term "," term : tactic
macro_rules
  | `(tactic| exists_intro $t, $h) => `(tactic| exact ⟨$t, $h⟩)

/-- Eliminate existential quantifier: extract witness and proof -/
syntax "exists_elim" term : tactic
macro_rules
  | `(tactic| exists_elim $h) =>
    `(tactic| exact ⟨($h).choose, ($h).choose_spec⟩)

/-!
## Equality
-/

/-- Reflexivity: prove t = t -/
syntax (name := eq_refl) "eq_refl" : tactic
macro_rules (kind := eq_refl)
  | `(tactic| eq_refl) => `(tactic| rfl)

/-- Substitution: rewrite using an equality in a term -/
syntax (name := eq_subst) "eq_subst" term "in" term : tactic
macro_rules (kind := eq_subst)
  | `(tactic| eq_subst $h_eq:term in $h_target:term) =>
    `(tactic| simp only [$h_eq:term, $h_target:term])

/-!
## Examples
-/

-- Conjunction is commutative
example (p q : Prop) : p ∧ q → q ∧ p := by
  assume (h : p ∧ q)
  have hq : q := by and_elim_right h
  have hp : p := by and_elim_left h
  and_intro hq, hp

-- Disjunction elimination
example (p q r : Prop) : (p ∨ q) → (p → r) → (q → r) → r := by
  assume (h_or : p ∨ q)
  assume (h_pr : p → r)
  assume (h_qr : q → r)
  or_elim h_or with
  | left hp => modus_ponens h_pr by hp
  | right hq => modus_ponens h_qr by hq

-- Law of non-contradiction
example (p : Prop) : ¬(p ∧ ¬p) := by
  prove_by_negation (h : p ∧ ¬p) {
    have hp : p := by and_elim_left h
    have hnp : ¬p := by and_elim_right h
    contradiction hnp, hp
  }

-- Universal quantifier elimination
example (α : Type) (P : α → Prop) (a : α) : (∀ x, P x) → P a := by
  assume (h : ∀ x, P x)
  have h_pa : P a := by forall_elim h, a  -- ∀-Elimination: instantiate with a
  exact h_pa

-- Existential quantifier introduction
example (α : Type) (P : α → Prop) (a : α) : P a → ∃ x, P x := by
  assume (h : P a)
  exists_intro a, h

-- Existential to existential
example (α : Type) (P Q : α → Prop) :
    (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  assume (h_ex : ∃ x, P x)
  assume (h_all : ∀ x, P x → Q x)
  have ⟨(a: α), (h_pa: P a)⟩ : ∃ x, P x := by exists_elim h_ex
  have h_impl : P a → Q a := by forall_elim h_all, a  -- ∀-Elimination: instantiate with a
  have h_qa : Q a := by modus_ponens h_impl by h_pa
  have h_result : ∃ x, Q x := by exists_intro a, h_qa
  exact h_result

-- Double negation introduction
example (p : Prop) : p → ¬¬p := by
  assume (hp : p)
  prove_by_negation (hnp : ¬p) {
    contradiction hnp, hp
  }

-- Equality symmetry
example (α : Type) (a b : α) : a = b → b = a := by
  assume (h : a = b)
  have h_refl : a = a := by eq_refl
  have h_result : b = a := by eq_subst h in h_refl
  exact h_result

-- Equality transitivity
example (α : Type) (a b c : α) : a = b → b = c → a = c := by
  assume (h1 : a = b)
  assume (h2 : b = c)
  have h_bc : b = c := h2
  have h_ac : a = c := by eq_subst h1 in h_bc
  exact h_ac

-- Universal quantifier introduction and elimination
-- This is just alpha-equivalence (renaming), trivial
example (α : Type) (P : α → Prop) : (∀ x, P x) → (∀ y, P y) := by
  assume (h : ∀ x, P x)
  exact h  -- Same proposition, just different variable name

-- Universal quantifier: ∀-Introduction with free variable
example (P : Nat → Nat → Prop) : (∀ x y, P x y) → (∀ x y, P x y) := by
  assume (h : ∀ x y, P x y)
  intro z
  have h1 : ∀ x, P x z := λ x => h x z
  have h2 : ∀ x y, P x y := by forall_intro2 h1
  exact h2 z

-- Universal quantifier: ∀-Elimination
example (a b : Nat) (P : Nat → Nat → Prop) : (∀ x y, P x y) → P a b := by
  assume (h : ∀ x y, P x y)
  have h1 : ∀ y, P a y := by forall_elim h, a  -- ∀-Elimination: instantiate first ∀ with a
  have h2 : P a b := by forall_elim h1, b      -- ∀-Elimination: instantiate second ∀ with b
  exact h2

-- Universal quantifier: nested ∀-Introduction (alpha-equivalence)
example (α β : Type) (P : α → β → Prop) : (∀ x y, P x y) → (∀ (a : α), ∀ (b : β), P a b) := by
  assume (h : ∀ x y, P x y)
  exact h  -- Just renaming, same proposition

-- Combining ∀-Elimination with ∃-Introduction
example (α β : Type) (P : α → β → Prop) (a : α) (b : β) : (∀ x y, P x y) → (∃ x y, P x y) := by
  assume (h : ∀ x y, P x y)
  have h1 : ∀ y, P a y := by forall_elim h, a  -- ∀-Elimination: instantiate with a
  have h2 : P a b := by forall_elim h1, b      -- ∀-Elimination: instantiate with b
  have h3 : ∃ y, P a y := by exists_intro b, h2  -- ∃-Introduction: witness b
  have h4 : ∃ x y, P x y := by exists_intro a, h3  -- ∃-Introduction: witness a
  exact h4

-- INVALID: Cannot use witness from ∃-Elimination for ∀-Introduction
-- This example shows that witnesses from existentials are specific, not arbitrary
example (α : Type) (P : α → Prop) : (∃ x, P x) → (∀ x, P x) := by
  assume (h_ex : ∃ x, P x)
  have ⟨(a : α), (h_pa : P a)⟩ : ∃ x, P x := by exists_elim h_ex
  -- Cannot apply forall_intro to h_pa because 'a' is a specific witness, not arbitrary
  -- This proof is invalid in Natural Deduction
  -- have (h_all : ∀ x, P x) := by forall_intro h_pa
  sorry  -- Unprovable!
