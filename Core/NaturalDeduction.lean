import Lean
import Core.Equality

/-!
# Mathematics derives from Logic...

We propose a logical framework to derive mathematics from it only using the primitive notion of predicate within that framework.
The framework's goal is to provide the "right notion of predicate" from which mathematics can be derived.

**Core Philosophy**: This framework aims to demonstrate that mathematics can be derived directly from logic itself, vindicating
the logicist program. The key is identifying the right notion of predicate. Standard FOL predicates are too weak—they
cannot be typed, cannot be recursive, and cannot govern term formation. By enriching predicates with precisely these
three capabilities, logic becomes sufficient to derive all of mathematics. Unlike set-theoretic foundations (which take
"set" as primitive) or type-theoretic foundations (which take "type" as primitive), this approach shows that the logical
notion of predicate—properly understood—is enough. Functions, types, and all mathematical structures emerge as predicates,
rather than requiring separate foundational primitives beyond logic itself.

The framework is First-Order Logic (FOL) with the following extensions:

  1. Terms are typed. A type determines the valid syntactic structure of a term of the type, as follows:
    1.1 Term formation is governed by axioms:
      1.1.1 We introduce explicit `Type Judgments`, i.e. `t : T`, is a binary predicate meaning "term `t` has type `T`."
      1.1.2 We write axioms defining what are the valid terms of a type.
        `zero : Nat` (zero is a valid term of type `Nat`)
        `∀x, (x : Nat) → (succ x : Nat)` (if `x` is a valid term of type `Nat`, then `succ x` is a valid term of type `Nat`).
    1.2 Quantification is type-restricted: ∀x:T. P(x) is syntactic sugar for ∀x, (x:T) → P(x)
    1.3 Free variables in predicates are typed, and can only be replaced by terms of the specified type.
        For example, `P(x : Nat, y : Bool)` as opposed to `P(x, y)` where the types of x and y are not specified.

  2. To support the above, we allow `Recursive Predicate Definitions`, i.e. we allow predicate definitions where the predicate
  appears in its own definition. Formally, we allow axioms of the form: `∀x₁...xₙ, P(x₁,...,xₙ) ↔ φ(x₁,...,xₙ)` even when `φ`
  contains occurrences of `P`.

  We use `Natural Deduction` as our proof system.

  **Note 1**: The framework ensures well-typed reasoning through its construction. There's no external type checking needed, beyond
  substitution of free variables, because the only terms that can be constructed are those explicitly permitted by the introduced judgment
  axioms like `zero : Nat` and `∀x, (x : Nat) → (succ x : Nat)`, therefore ill-typed terms cannot appear in valid proofs because the
  corresponding type judgments (e.g., `true : Nat`) would not be derivable from the axioms.

  **Note 2**: Predicates with free variables are not considered functions, e.g. propositional functions, as that would introduce a circularity.
  Functions will be derived from the notion of predicate itself, so we cannot use functions to define what a predicate with free variables is.
  A predicate with free variables must be interpreted as a template for a statement that contains placeholders, which becomes
  a statement when these placeholders are filled with terms. Types impose restrictions on the allowed substitutions for the
  placeholders. Moreover, Symbols like `zero` or `succ` are syntactic tokens, not function symbols with pre-existing semantics.
  Their meaning derives entirely from predicate axioms.

  **Note 3**: the framework itself does not enforce well-foundedness or consistency checks on recursive definitions. Users are
  responsible for ensuring their axioms are consistent. If recursivity does not end, they will not be able to
  successfully use such definitions in proofs. Similarly, when defining a type T in the framework, users may want to make
  sure that all axioms that introduce terms of type T don't contain T in contravariant positions inside the definitions.

  **Note 4**: This framework is inspired on Abstract Data Types (ADTs), and can express them, in fact, to define types and terms of formulas
  we will follow exactly the ADT approach. In the framework, this translates into defining axioms that specify which terms belong
  to each type, axioms that define the signature of operations on those types, and axioms that define the semantics of those operations.
  These semantic axioms will be universally quantified and expressed only using equality, exactly as in standard ADTs.

-/

open Lean Meta Elab Tactic

-- Syntax for `Predicates`with free variables
-- Allows writing: x: T ↦ body instead of fun x: T => body
macro "(" x:ident ":" t:term " ↦ " y:term ")" : term => do
    `(fun $x : $t => $y)

-- Notation to define `Sets` from `Predicates` with free variables
-- Allows writing: { x : T | body } instead of fun x: T => body
macro "{" x:ident ":" t:term "|" y:term "}" : term => do
    `(fun $x : $t => $y)

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

-- Introduce a variable
syntax (name := ndVariable) "variable" "(" ident ":" term ")": tactic

macro_rules (kind := ndVariable)
  | `(tactic| variable ($x:ident: $_ty)) => `(tactic| intro $x:ident)

-- Introduce a constant from an inhabited type
syntax (name := ndConstant) "constant" "(" ident ":" term ")": tactic

macro_rules (kind := ndConstant)
  | `(tactic| constant ($x:ident: $ty)) =>
      `(tactic|
        classical
        obtain ⟨$x⟩ := (inferInstance: Nonempty $ty)
      )

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

-- Introduce existential quantifier: provide witness and proof
syntax "exists_intro" term "," term: tactic
macro_rules
  | `(tactic| exists_intro $h, $t) => `(tactic| exact ⟨$t, $h⟩)

-- Eliminate existential quantifier
def exists_elim {α: Type} {P: α → Prop} (h: ∃ x, P x): ∃ x, P x := h

-- Eliminate universal quantifier: instantiate with a term
syntax "forall_elim" term "," term: tactic
macro_rules
  | `(tactic| forall_elim $h, $t) => `(tactic| exact $h $t)


-- Modus Ponens
def modusPonensFn {P Q: Prop} (hpq: P → Q) (hp: P): Q :=
  hpq hp

syntax (name := ndModusPonens) "modus_ponens" term "," term: tactic

macro_rules (kind := ndModusPonens)
  | `(tactic| modus_ponens $hpq , $hp) =>
      `(tactic| exact modusPonensFn $hpq $hp)

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

-- Double Implication introduction
syntax (name := ndIffIntro) "iff_intro" term "," term: tactic

macro_rules (kind := ndIffIntro)
  | `(tactic| iff_intro $hForward , $hBackward) =>
      `(tactic| exact Iff.intro $hForward $hBackward)

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

-- Deductive Equivalence substitution rule
syntax (name := ndDeductiveEq) "deductive_eq" term "," term: tactic

macro_rules (kind := ndDeductiveEq)
  | `(tactic| deductive_eq $hIff , $h) =>
      `(tactic|
        first
          | exact Iff.mp $hIff $h
          | exact Iff.mpr $hIff $h
      )

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

-- Negation elimination: from ¬¬P, derive P
syntax (name := ndNegElim) "neg_elim" term: tactic

macro_rules (kind := ndNegElim)
  | `(tactic| neg_elim $h) => `(tactic| exact Classical.byContradiction $h)

-- Iterate an existing premise somwhere else in the proof
syntax (name := ndIterate) "iterate" term: tactic

macro_rules (kind := ndIterate)
  | `(tactic| iterate $h) => `(tactic| exact $h)

-- Truth introduction: allows introducing a prop that reduces/is equivalent to True
syntax (name := ndTrueIntro) "true_intro": tactic

macro_rules (kind := ndTrueIntro)
  | `(tactic| true_intro) => `(tactic| exact True.intro)

-- And introduction: from P, Q, derive P ∧ Q
syntax (name := ndAndIntro) "and_intro" term "," term: tactic

macro_rules (kind := ndAndIntro)
  | `(tactic| and_intro $hLeft , $hRight) =>
      `(tactic| exact And.intro $hLeft $hRight)

-- And elimination: from P ∧ Q, derive P or derive Q
syntax (name := ndAndElim) "and_elim" term: tactic

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
syntax (name := ndOrIntro) "or_intro" term: tactic

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
syntax (name := ndOrElim) "or_elimination" term "," term "," term: tactic

macro_rules (kind := ndOrElim)
  | `(tactic| or_elimination $hpq , $hpr , $hqr) =>
      `(tactic| exact Or.elim $hpq $hpr $hqr)

/-! WE DON?T NEED THIS BECAUSE WE USE PURE FOL, LEAN'S BUILT-IN EQUALITY REASONING NOT ALLOWED
## Equality


/-- Reflexivity: prove t = t -/
syntax (name := eq_refl) "eq_refl" : tactic
macro_rules (kind := eq_refl)
  | `(tactic| eq_refl) => `(tactic| rfl)

/-- Substitution: rewrite using an equality in a term -/
def eqSubstFn {α: Sort u} {a b: α} (P: α → Prop) (h_eq: a = b) (h_target: P a): P b :=
  h_eq ▸ h_target

syntax (name := eq_subst) "eq_subst" term "in" term: tactic

macro_rules (kind := eq_subst)
  | `(tactic| eq_subst $h_eq in $h_target) =>
    `(tactic| exact eqSubstFn _ $h_eq $h_target)

syntax (name := eq_subst_with) "eq_subst_with" term "in" term "with" term: tactic

macro_rules (kind := eq_subst_with)
  | `(tactic| eq_subst_with $h_eq in $h_target with $pred) =>
    `(tactic| exact eqSubstFn $pred $h_eq $h_target)

-/

namespace pc₀ -- Propositional Calculus 0

theorem identity_principle {P: Prop}: P → P := by
  assume (h₁ : P)
  implication_intro h₁, h₁

theorem deductive_eq_l2r {P Q: Prop} (h₁: P ↔ Q) (h₂: P) : Q := by
  have h₃: P → Q := by iff_elim_l2r h₁
  modus_ponens h₃, h₂

theorem deductive_eq_r2l {P Q: Prop} (h₁: P ↔ Q) (h₂: Q) : P := by
  have h₃: Q → P := by iff_elim_r2l h₁
  modus_ponens h₃, h₂

theorem excluded_middle {P: Prop} : P ∨ ¬P := by
  have h₁: ¬(P ∨ ¬P) → False := by
    assume (h₁₁: ¬(P ∨ ¬P))
    have h₁₂: P → False := by
      assume (h₁₂₁: P)
      have h₁₂₂: P ∨ ¬P := by or_intro h₁₂₁
      contradiction h₁₂₂, h₁₁
    have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
    have h₁₄: ¬P → False := by
      assume (h₁₄₁: ¬P)
      have h₁₄₂: P ∨ ¬P := by or_intro h₁₄₁
      contradiction h₁₄₂, h₁₁
    have h₁₅: ¬¬P := by reductio_ad_absurdum h₁₄
    contradiction h₁₃, h₁₅
  have h₂: ¬¬(P ∨ ¬P) := by reductio_ad_absurdum h₁
  neg_elim h₂

theorem non_contradiction {P: Prop} : ¬(P ∧ ¬P) := by
  have h₁: P ∧ ¬P → False := by
    assume (h₁₁: P ∧ ¬P)
    have h₁₂: P := by and_elim h₁₁
    have h₁₃: ¬P := by and_elim h₁₁
    contradiction h₁₂, h₁₃
  reductio_ad_absurdum h₁

theorem hypothetical_syllogism {P Q R: Prop} (h1: P → Q) (h2: Q → R): P → R := by
  have h3: P → R := by
    assume (h3_1: P)
    have h3_2: Q := by modus_ponens h1, h3_1
    have h3_3: R := by modus_ponens h2, h3_2
    implication_intro h3_1, h3_3
  iterate h3

theorem quodlibet_seqitur {P Q: Prop} (h₁: P) (h₂: ¬P): Q := by
  have h₃: ¬Q → False := by
    assume (h₃₁: ¬Q)
    contradiction h₁, h₂
  have h₄: ¬¬Q := by reductio_ad_absurdum h₃
  neg_elim h₄

theorem disjunctive_syllogism {P Q: Prop} (h₁: P ∨ Q) (h₂: ¬P): Q := by
  have h₃: P → Q := by
    assume (h₃₁: P)
    have h₃₂: Q := quodlibet_seqitur h₃₁ h₂
    implication_intro h₃₁, h₃₂
  have h₄: Q → Q := identity_principle
  or_elimination h₁, h₃, h₄

theorem modus_tollens {P Q: Prop} (h₁: P → Q) (h₂: ¬Q): ¬P := by
  have h₃: P → False := by
    assume (h₃₁: P)
    have h₃₂: Q := by modus_ponens h₁, h₃₁
    contradiction h₃₂, h₂
  reductio_ad_absurdum h₃

theorem double_neg_intro {P: Prop} (h₁: P) : ¬¬P := by
  have h₂: ¬P → False := by
    assume (h₂₁: ¬P)
    contradiction h₁, h₂₁
  reductio_ad_absurdum h₂

theorem medieval_resolution {P Q R: Prop} (h₁: P → Q) (h₂: ¬P → R): Q ∨ R := by
  have h₃: P ∨ ¬P := excluded_middle
  have h₄: P → Q ∨ R := by
    assume (h₄₁: P)
    have h₄₂: Q := by modus_ponens h₁, h₄₁
    have h₄₃: Q ∨ R := by or_intro h₄₂
    iterate h₄₃
  have h₅: ¬P → Q ∨ R := by
    assume (h₅₁: ¬P)
    have h₅₂: R := by modus_ponens h₂, h₅₁
    have h₅₃: Q ∨ R := by or_intro h₅₂
    iterate h₅₃
  or_elimination h₃, h₄, h₅

theorem resolution_non_constructive {P Q R: Prop} (h₁: ¬P ∨ Q) (h₂: P ∨ R): Q ∨ R := by
  have h₃: P ∨ ¬P := excluded_middle
  have h₄: P → Q ∨ R := by
    assume (h₄₁: P)
    have h₄₂: ¬P → Q := by
      assume (h₄₂₁: ¬P)
      have h₄₃: Q := quodlibet_seqitur h₄₁ h₄₂₁
      iterate h₄₃
    have h₄₃: Q → Q := identity_principle
    have h₄₄: Q := by or_elimination h₁, h₄₂, h₄₃
    have h₄₅: Q ∨ R := by or_intro h₄₄
    iterate h₄₅
  have h₅: ¬P → Q ∨ R := by
    assume (h₅₁: ¬P)
    have h₅₂: P → R := by
      assume (h₅₂₁: P)
      have h₅₃: R := quodlibet_seqitur h₅₂₁ h₅₁
      iterate h₅₃
    have h₅₃: R → R := identity_principle
    have h₅₄: R := by or_elimination h₂, h₅₂, h₅₃
    have h₅₅: Q ∨ R := by or_intro h₅₄
    iterate h₅₅
  or_elimination h₃, h₄, h₅

theorem resolution_constructive {P Q R: Prop} (h₁: ¬P ∨ Q) (h₂: P ∨ R): Q ∨ R := by
  have h₃: ¬P → Q ∨ R := by
    assume (h₃₁: ¬P)
    have h₃₂: P → Q ∨ R := by
      assume (h₃₂₁: P)
      have h₃₂₂: Q := quodlibet_seqitur h₃₂₁ h₃₁
      have h₃₂₃: Q ∨ R := by or_intro h₃₂₂
      iterate h₃₂₃
    have h₃₃: R → Q ∨ R := by
      assume (h₃₃₁: R)
      have h₃₃₂: Q ∨ R := by or_intro h₃₃₁
      iterate h₃₃₂
    or_elimination h₂, h₃₂, h₃₃
  have h₄: Q → Q ∨ R := by
    assume (h₄₁: Q)
    have h₄₂: Q ∨ R := by or_intro h₄₁
    iterate h₄₂
  or_elimination h₁, h₃, h₄

theorem incompatbility {P Q: Prop} (h₁: ¬(P ∧ Q)) (h₂: P): ¬Q := by
  have h₃: Q → False := by
    assume (h₃₁: Q)
    have h₃₂: P ∧ Q := by and_intro h₂, h₃₁
    contradiction h₃₂, h₁
  reductio_ad_absurdum h₃

theorem positive_paradox {P Q: Prop}: P → (Q → P) := by
  assume (h₁: P)
  assume (h₂: Q)
  have h₃: P := by iterate h₁
  implication_intro h₂, h₃

theorem material_implication {P Q: Prop}: P → Q ↔ ¬P ∨ Q := by
  have h₁: (P → Q) → (¬P ∨ Q) := by
    assume (h₁₁: P → Q)
    have h₁₂: P ∨ ¬P := excluded_middle
    have h₁₃: P → (¬P ∨ Q) := by
      assume (h₁₃₁: P)
      have h₁₃₂: Q := by modus_ponens h₁₁, h₁₃₁
      have h₁₃₃: ¬P ∨ Q := by or_intro h₁₃₂
      iterate h₁₃₃
    have h₁₄: ¬P → (¬P ∨ Q) := by
      assume (h₁₄₁: ¬P)
      have h₁₄₂: ¬P ∨ Q := by or_intro h₁₄₁
      iterate h₁₄₂
    or_elimination h₁₂, h₁₃, h₁₄
  have h₂: (¬P ∨ Q) → (P → Q) := by
    assume (h₂₁ : ¬P ∨ Q)
    have h₂₂: ¬P → (P → Q) := by
      assume (h₂₂₁: ¬P)
      assume (h₂₂₂: P)
      have h₂₃: Q := quodlibet_seqitur h₂₂₂ h₂₂₁
      iterate h₂₃
    have h₂₃: Q → (P → Q) := positive_paradox
    or_elimination h₂₁, h₂₂, h₂₃
  iff_intro h₁, h₂

theorem de_morgan_disjunction {P Q: Prop}: ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  have h₁: ¬(P ∨ Q) →  (¬P ∧ ¬Q) := by
    assume (h₁₁: ¬(P ∨ Q))
    have h₁₂: P → False := by
      assume (h₁₂₁: P)
      have h₁₂₂: P ∨ Q := by or_intro h₁₂₁
      contradiction h₁₂₂, h₁₁
    have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
    have h₁₄: Q → False := by
      assume (h₁₄₁: Q)
      have h₁₄₂: P ∨ Q := by or_intro h₁₄₁
      contradiction h₁₄₂, h₁₁
    have h₁₅: ¬Q := by reductio_ad_absurdum h₁₄
    and_intro h₁₃, h₁₅
  have h₂: (¬P ∧ ¬Q) → ¬(P ∨ Q) := by
    assume (h₂₁: ¬P ∧ ¬Q)
    have h₂₂: (P ∨ Q) → False := by
      assume (h₂₂₁: P ∨ Q)
      have h₂₂₂: ¬P := by and_elim h₂₁
      have h₂₂₃: Q := disjunctive_syllogism h₂₂₁ h₂₂₂
      have h₂₂₄: ¬Q := by and_elim h₂₁
      contradiction h₂₂₃, h₂₂₄
    reductio_ad_absurdum h₂₂
  iff_intro h₁, h₂

theorem de_morgan_conjunction {P Q: Prop}: ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  have h₁: ¬(¬P ∨ ¬Q) ↔ (¬¬P ∧ ¬¬Q) := de_morgan_disjunction
  have h₂: ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
    assume (h₂₁: ¬(P ∧ Q))
    have h₂₂: P → ¬Q := by
      assume (h₂₂₁: P)
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
    assume (h₃₁: ¬P ∨ ¬Q)
    have h₃₂: (P ∧ Q) → False := by
      assume (h₃₂₁: P ∧ Q)
      have h₃₂₂: P := by and_elim h₃₂₁
      have h₃₂₃: ¬¬P := double_neg_intro h₃₂₂
      have h₃₂₄: ¬Q := disjunctive_syllogism h₃₁ h₃₂₃
      have h₃₂₅: Q := by and_elim h₃₂₁
      contradiction h₃₂₅, h₃₂₄
    reductio_ad_absurdum h₃₂
  iff_intro h₂, h₃

  theorem implication_reversibility {P Q: Prop}: (P → Q) ↔ (¬Q → ¬P) := by
    have h₁: (P → Q) → (¬Q → ¬P) := by
      assume( h₁: P → Q)
      assume (h₁₁: ¬Q)
      have h₁₂: P → False := by
        assume (h₁₂₁: P)
        have h₁₂₂: Q := by modus_ponens h₁, h₁₂₁
        contradiction h₁₂₂, h₁₁
      have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
      implication_intro h₁₁, h₁₃
    have h₂: (¬Q → ¬P) → (P → Q) := by
      assume (h₂₁: ¬Q → ¬P)
      assume (h₂₂: P)
      have h₂₃: ¬Q → False := by
        assume (h₂₃₁: ¬Q)
        have h₂₃₂: ¬P := by modus_ponens h₂₁, h₂₃₁
        contradiction h₂₂, h₂₃₂
      have h₂₄: ¬¬Q := by reductio_ad_absurdum h₂₃
      have h₂₅: Q := by neg_elim h₂₄
      implication_intro h₂₂, h₂₅
    iff_intro h₁, h₂

theorem iff_contrapositiveness {P Q: Prop}: (P ↔ Q) ↔ (¬P ↔ ¬Q) := by
  have h₁: (P ↔ Q) → (¬P ↔ ¬Q) := by
    assume (h₁₁: P ↔ Q)
    have h₁₁₁: ¬Q → ¬P := by
      have h₁₁₁₁: P → Q := by iff_elim_l2r h₁₁
      have h₁₁₁₂: ¬Q →  ¬P := deductive_eq_l2r implication_reversibility h₁₁₁₁
      iterate h₁₁₁₂
    have h₁₁₂: ¬P → ¬Q := by
      have h₁₁₂₁: Q → P := by iff_elim_r2l h₁₁
      have h₁₁₂₂: ¬P →  ¬Q := deductive_eq_l2r implication_reversibility h₁₁₂₁
      iterate h₁₁₂₂
    iff_intro h₁₁₂, h₁₁₁
  have h₂: (¬P ↔ ¬Q) → (P ↔ Q) := by
    assume (h₂₁: ¬P ↔ ¬Q)
    have h₂₂: (P → Q) := by
      have h₂₂₁: ¬Q → ¬P := by iff_elim_r2l h₂₁
      have h₂₂₂: P → Q := deductive_eq_r2l implication_reversibility h₂₂₁
      iterate h₂₂₂
    have h₂₃: (Q → P) := by
      have h₂₃₁: ¬P → ¬Q := by iff_elim_l2r h₂₁
      have h₂₃₂: Q → P := deductive_eq_r2l implication_reversibility h₂₃₁
      iterate h₂₃₂
    iff_intro h₂₂, h₂₃
  iff_intro h₁, h₂

theorem currying {P Q R: Prop}: (P → (Q → R)) ↔ (P ∧ Q → R) := by
  have h₁: (P → (Q → R)) → (P ∧ Q → R) := by
    assume (h₁₁: P → (Q → R))
    assume (h₁₂: P ∧ Q)
    have h₁₃: P := by and_elim h₁₂
    have h₁₄: Q → R := by modus_ponens h₁₁, h₁₃
    have h₁₅: Q := by and_elim h₁₂
    have h₁₆: R := by modus_ponens h₁₄, h₁₅
    implication_intro h₁₂, h₁₆
  have h₂: (P ∧ Q → R) → (P → (Q → R)) := by
    assume (h₂₁: P ∧ Q → R)
    assume (h₂₂: P)
    have h₂₆: Q → R := by
      assume (h₂₃: Q)
      have h₂₄: P ∧ Q := by and_intro h₂₂, h₂₃
      modus_ponens h₂₁, h₂₄
    implication_intro h₂₂, h₂₆
  iff_intro h₁, h₂

example {P Q R S: Prop} (h₁: P ∧ Q → R) (h₂: (¬P ∧ ¬Q) → S) (h₃: P ↔ Q): R ∨ S := by
  have h₄: P ∨ ¬P := excluded_middle
  have h₅: (P → Q) ∧ (Q → P) := by iff_elim h₃
  have h₆: P → R ∨ S := by
    assume (h₆₁: P)
    have h₆₂: P → Q := by and_elim h₅
    have h₆₃: Q := by modus_ponens h₆₂, h₆₁
    have h₆₄: P ∧ Q := by and_intro h₆₁, h₆₃
    have h₆₅: R := by modus_ponens h₁, h₆₄
    have h₆₆: R ∨ S := by or_intro h₆₅
    iterate h₆₆
  have h₇ : ¬P → R ∨ S := by
    assume (h₇₁: ¬P)
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

-- Unique Existence Quantifier
axiom ExistsUnique {α: Type}: (α → Prop) → Prop

-- Syntax supporting multiple forms
syntax "∃!" ident "," term : term                              -- ∃! x , P x
syntax "∃!" ident ":" term ", " term : term                    -- ∃! x : α, P x
syntax "∃!" "(" ident ":" term ")" ", " term : term            -- ∃! (x : α), P x

macro_rules
| `(∃! $x:ident, $body) => `(ExistsUnique (fun ($x) => $body))
| `(∃! $x:ident : $t, $body) => `(ExistsUnique (fun ($x : $t) => $body))
| `(∃! ($x:ident : $t), $body) => `(ExistsUnique (fun ($x : $t) => $body))

-- Axiom defining its meaning
axiom exists_unique_def: ∀ {α: Type}, ∀ (P: α → Prop),
    ExistsUnique P ↔ (∃ x, P x ∧ (∀ y, P y → y =ₚ x))

namespace pc₁ -- Propositional Calculus 1

theorem forall_comm {α: Type} {P: α → α → Prop}: (∀ x, ∀ y, P x y) ↔ (∀ y, ∀ x, P x y) := by
  have h₁: (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
    assume (h₁₁ : ∀ x, ∀ y, P x y)
    have h₁₁: ∀ y, ∀ x, P x y := by forall_intro
        variable (u: α)
        variable (v: α)
        have h₁₁₂: ∀ y, P v y := by forall_elim h₁₁, v
        have h₁₁₃: P v u := by forall_elim h₁₁₂, u
    iterate h₁₁
  have h₂: (∀ y, ∀ x, P x y) → (∀ x, ∀ y, P x y) := by
    assume (h₂₁ : ∀ y, ∀ x, P x y)
    have h₂₁: ∀ x, ∀ y, P x y := by forall_intro
        variable (u: α)
        variable (v: α)
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
    variable (u: α)
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

theorem forall_to_exists {α: Type} [Nonempty α] {P: α → Prop}: (∀ x, P x) → (∃ x, P x) := by
  assume (h₁: ∀ x, P x)
  constant (u: α)
  have h₂: P u := by forall_elim h₁, u
  have h₃: ∃ x, P x := by exists_intro h₂, u
  iterate h₃

theorem exists_forall_imp_forall_exists {α: Type} {P: α → α → Prop}: (∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y) := by
  assume(h₁: ∃ x, ∀ y, P x y)
  have h₂: ∀ y, ∃ x, P x y := by forall_intro
    variable (u: α)
    have ⟨(a: α), (h₂₂: ∀ y, P a y)⟩ := exists_elim h₁
    have h₂₃: P a u := by forall_elim h₂₂, u
    have h₂₄: ∃ x, P x u := by exists_intro h₂₃, a
    iterate h₂₄
  iterate h₂

theorem de_morgan_exists {α: Type} {P: α → Prop}: (¬(∃ x, P x)) ↔ (∀ x, ¬P x) := by
  have h₁: (¬(∃ x, P x)) → (∀ x, ¬P x) := by
    assume (h₁₁: ¬(∃ x, P x))
    have h₁₄: ∀ x, ¬P x := by forall_intro
      variable (u: α)
      have h₁₂: P u → False := by
        assume (h₁₂₁: P u)
        have h₁₂₂: ∃ x, P x := by exists_intro h₁₂₁, u
        contradiction h₁₂₂, h₁₁
      have h₁₃: ¬P u := by reductio_ad_absurdum h₁₂
      iterate h₁₃
    iterate h₁₄
  have h₂: (∀ x, ¬P x) → (¬(∃ x, P x)) := by
    assume (h₂₁: ∀ x, ¬P x)
    have h₂₂: (∃ x, P x) → False := by
      assume (h₂₂₁: ∃ x, P x)
      have ⟨(u: α), (h₂₂₂: P u)⟩  := exists_elim h₂₂₁
      have h₂₂₃: ¬P u := by forall_elim h₂₁, u
      contradiction h₂₂₂, h₂₂₃
    have h₂₃: ¬(∃ x, P x) := by reductio_ad_absurdum h₂₂
    iterate h₂₃
  iff_intro h₁, h₂

theorem de_morgan_forall {α: Type} {P: α → Prop}: (¬(∀ x, P x)) ↔ (∃ x, ¬P x) := by
  have h₁: (¬(∀ x, P x)) → (∃ x, ¬P x) := by
    assume (h₁₁: ¬(∀ x, P x))
    have h₁₂: (¬(∃ x, ¬P x)) → False := by
      assume (h₁₂₁: ¬(∃ x, ¬P x))
      have h₁₂₂: (¬(∃ x, ¬P x)) ↔ (∀ x, ¬¬P x)  := de_morgan_exists
      have h₁₂₃: ((¬(∃ x, ¬P x)) → (∀ x, ¬¬P x)) ∧ ((∀ x, ¬¬P x) → (¬(∃ x, ¬P x)) ) := by iff_elim h₁₂₂
      have h₁₂₄: (¬(∃ x, ¬P x)) → (∀ x, ¬¬P x) := by and_elim h₁₂₃
      have h₁₂₅: ∀ x, ¬¬P x := by modus_ponens h₁₂₄, h₁₂₁
      have h₁₂₆: ∀ x, P x := by forall_intro
        variable (u: α)
        have h₁₂₇: ¬¬P u := by forall_elim h₁₂₅, u
        have h₁₂₈: P u := by neg_elim h₁₂₇
      contradiction h₁₂₆, h₁₁
    have h₁₃: ¬¬(∃ x, ¬P x) := by reductio_ad_absurdum h₁₂
    neg_elim h₁₃
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

theorem forall_and_full_dist {α: Type} {P Q: α → Prop}: (∀ x, P x) ∧ (∀ x, Q x) ↔ (∀ x, P x ∧ Q x) := by
  have h₁: (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x) := by
    assume (h₁₁: (∀ x, P x) ∧ (∀ x, Q x))
    have h₁₂: ∀ x, P x := by and_elim h₁₁
    have h₁₃: ∀ x, Q x := by and_elim h₁₁
    have h₁₄: ∀ x, P x ∧ Q x := by forall_intro
      variable (u: α)
      have h₁₅: P u := by forall_elim h₁₂, u
      have h₁₆: Q u := by forall_elim h₁₃, u
      have h₁₇: P u ∧ Q u := by and_intro h₁₅, h₁₆
      iterate h₁₇
    iterate h₁₄
  have h₂: (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x) := by
    assume (h₂₁: ∀ x, P x ∧ Q x)
    have h₂₂: ∀ x, P x := by forall_intro
      variable (u: α)
      have h₂₃: P u ∧ Q u := by forall_elim h₂₁, u
      have h₂₄: P u := by and_elim h₂₃
      iterate h₂₄
    have h₂₅: ∀ x, Q x := by forall_intro
      variable (u: α)
      have h₂₆: P u ∧ Q u := by forall_elim h₂₁, u
      have h₂₇: Q u := by and_elim h₂₆
      iterate h₂₇
    have h₂₈: (∀ x, P x) ∧ (∀ x, Q x) := by and_intro h₂₂, h₂₅
    iterate h₂₈
  iff_intro h₁, h₂

theorem forall_or_partial_dist {α: Type} {P Q: α → Prop}: (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x) := by
  assume (h₁: (∀ x, P x) ∨ (∀ x, Q x))
  have h₂: (∀ x, P x) → (∀ x, P x ∨ Q x) := by
    assume (h₂₁: ∀ x, P x)
    have h₂₂: ∀ x, P x ∨ Q x := by forall_intro
      variable (u: α)
      have h₂₃: P u := by forall_elim h₂₁, u
      have h₂₄: P u ∨ Q u := by or_intro h₂₃
      iterate h₂₄
    iterate h₂₂
  have h₃: (∀ x, Q x) → (∀ x, P x ∨ Q x) := by
    assume (h₃₁: ∀ x, Q x)
    variable (u: α)
    have h₃₂: Q u := by forall_elim h₃₁, u
    have h₃₄: P u ∨ Q u := by or_intro h₃₂
    iterate h₃₄
  have h₄: ∀ x, P x ∨ Q x := by or_elimination h₁, h₂, h₃
  iterate h₄

theorem exists_or_full_dist {α: Type} {P Q: α → Prop}: (∃ x, P x) ∨ (∃ x, Q x) ↔ (∃ x, P x ∨ Q x) := by
  have h₁: (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x) := by
    assume (h₁₁: (∃ x, P x) ∨ (∃ x, Q x))
    have h₁₂: (∃ x, P x) → (∃ x, P x ∨ Q x) := by
      assume (h₁₂₁: ∃ x, P x)
      have ⟨(a: α), (h₁₂₂: P a)⟩ := exists_elim h₁₂₁
      have h₁₂₃: P a ∨ Q a := by or_intro h₁₂₂
      have h₁₂₄: ∃ x, P x ∨ Q x := by exists_intro h₁₂₃, a
      iterate h₁₂₄
    have h₁₃: (∃ x, Q x) → (∃ x, P x ∨ Q x) := by
      assume (h₁₃₁: ∃ x, Q x)
      have ⟨(a: α), (h₁₃₂: Q a)⟩ := exists_elim h₁₃₁
      have h₁₃₃: P a ∨ Q a := by or_intro h₁₃₂
      have h₁₃₄: ∃ x, P x ∨ Q x := by exists_intro h₁₃₃, a
      iterate h₁₃₄
    have h₁₄: ∃ x, P x ∨ Q x := by or_elimination h₁₁, h₁₂, h₁₃
    iterate h₁₄
  have h₂: (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) := by
    assume (h₂₁: ∃ x, P x ∨ Q x)
    have ⟨(a: α), (h₂₂: P a ∨ Q a)⟩ := exists_elim h₂₁
    have h₂₃: P a  → ((∃ x, P x) ∨ (∃ x, Q x)) := by
      assume (h₂₃₁: P a)
      have h₂₃₂: ∃ x, P x := by exists_intro h₂₃₁, a
      have h₂₃₃: (∃ x, P x) ∨ (∃ x, Q x) := by or_intro h₂₃₂
      iterate h₂₃₃
    have h₂₄: Q a  → ((∃ x, P x) ∨ (∃ x, Q x)) := by
      assume (h₂₄₁: Q a)
      have h₂₄₂: ∃ x, Q x := by exists_intro h₂₄₁, a
      have h₂₄₃: (∃ x, P x) ∨ (∃ x, Q x) := by or_intro h₂₄₂
      iterate h₂₄₃
    have h₂₅: ((∃ x, P x) ∨ (∃ x, Q x)) := by or_elimination h₂₂, h₂₃, h₂₄
    iterate h₂₅
  iff_intro h₁, h₂

theorem exists_and_partial_dist {α: Type} {P Q: α → Prop}: (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  assume (h₁: ∃ x, P x ∧ Q x)
  have ⟨(a: α), (h₁₁: P a ∧ Q a)⟩ := exists_elim h₁
  have h₁₂: P a := by and_elim h₁₁
  have h₁₃: Q a := by and_elim h₁₁
  have h₁₄: ∃ x, P x := by exists_intro h₁₂, a
  have h₁₅: ∃ x, Q x := by exists_intro h₁₃, a
  have h₁₆: (∃ x, P x) ∧ (∃ x, Q x) := by and_intro h₁₄, h₁₅
  iterate h₁₆

example {α : Type} {P Q R S: α → Prop} (h1: ∀ x, P x → Q x) (h2: ∃ x, R x ∧ S x) (h3: ∀ x, S x → P x): ∃ x, P x ∧ Q x := by
  have ⟨(a: α), (h4: R a ∧ S a)⟩ :=  exists_elim h2
  have h5: ∃ y, R y ∧ S y := by exists_intro h4, a
  sorry

end pc₁
