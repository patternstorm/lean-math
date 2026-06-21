---
name: lean-math-proofs
description: This skill should be used when writing proofs in the lean-math project. It covers the custom natural deduction tactics, proof style, patterns for congruence proofs, and authorship conventions. Essential for any proof-writing task.
---

# Writing Proofs in Lean-Math

## Fundamental Rule

**Never use Lean's built-in automation tactics.** This project uses explicit first-order logic proofs via custom natural deduction tactics. All Lean built-in tactics are forbidden. You can only use the custom natural deduction tactics defined in `Logic/NaturalDeduction/`.

## Custom Natural Deduction Tactics

### Universal Quantifier

**Introduction** — `forall_intro`:
```lean
theorem example: ∀ (x: U.Particular), P x := by forall_intro
  variable(a: U.Particular)
  -- prove P a
  have h₁: P a := ...
  iterate h₁
```
Introduces a fresh variable and requires proving the body for that variable. Use `constant` instead of `variable` when introducing a constant (same syntax: `constant(c: T)`).

**Elimination** — `forall_elim`:
```lean
-- Eliminate one ∀:
have h₂: P specific_value := by forall_elim h₁, specific_value
-- Eliminate multiple ∀s in one call (up to 6 supported; left-to-right):
have h₃: <fully-instantiated-type> := by forall_elim h, v₁, v₂, v₃, v₄, v₅, v₆
```
Always prefer the multi-arg form over chaining several `forall_elim` lines — it collapses bookkeeping. The intermediate types are uninteresting; only the final post-instantiation proposition matters, and that's what the `have`'s type declares.

### Implication

**Introduction** — `assume`:
```lean
have h₃: P → Q := by
  assume(h₃₁: P)
  -- derive Q
  have h₃₂: Q := ...
  iterate h₃₂
```

**Alternative introduction** — `implication_intro`:
```lean
-- Direct form: given hypothesis h₁ and proof h₂ of the consequent, close the implication
have h₃: P → Q := by implication_intro h₁, h₂
```

**Elimination** — `modus_ponens`:
```lean
have h₃: Q := by modus_ponens h₁, h₂
```

### Biconditional

**Introduction** — `iff_intro`:
```lean
have h₃: P ↔ Q := by iff_intro h₁, h₂
```
Takes two implications: `P → Q` and `Q → P`.

**Elimination** — tactic forms `iff_elim`, `iff_elim_l2r`, `iff_elim_r2l`:
```lean
-- iff_elim: extracts the direction matching the goal type
have h₂: P → Q := by iff_elim h₁    -- extracts forward direction
have h₃: Q → P := by iff_elim h₁    -- extracts backward direction

-- Directional variants:
have h₂: P → Q := by iff_elim_l2r h₁
have h₃: Q → P := by iff_elim_r2l h₁
```

**Elimination** — via `PC₀` helpers (term-mode, not tactics):
```lean
-- From h₁ : P ↔ Q and h₂ : P, derive Q
have h₃: Q := PC₀.deductive_eq_l2r h₁ h₂
-- From h₁ : P ↔ Q and h₂ : Q, derive P
have h₃: P := PC₀.deductive_eq_r2l h₁ h₂
```

### Conjunction

**Introduction** — `and_intro`:
```lean
have h₃: P ∧ Q := by and_intro h₁, h₂
```

**Elimination** — `and_elim`:
```lean
have h₂: P := by and_elim h₁  -- extracts left or right conjunct
```

### Disjunction

**Introduction** — `or_intro`:
```lean
have h₂: P ∨ Q := by or_intro h₁  -- from h₁ : P (or Q), derive P ∨ Q
```

**Elimination** — `or_elimination`:
```lean
have h₄: R := by or_elimination h₁, h₂, h₃  -- h₁ : P ∨ Q, h₂ : P → R, h₃ : Q → R
```

### Existential Quantifier

**Introduction** — `exists_intro`:
```lean
-- Syntax: exists_intro proof, witness
-- The macro expands to ⟨witness, proof⟩
have h₂: ∃ (x: T), P x := by exists_intro h₁, witness
```

**Elimination** — `exists_elim` (term-mode with destructuring, NOT a tactic):
```lean
-- From h₁ : ∃ (x: T), P x, extract the witness and proof
have ⟨(a: T), (h₂: P a)⟩ := exists_elim h₁
-- Now a : T and h₂ : P a are in scope
```

### Negation

**Introduction** — `contradiction`:
```lean
-- From h₁ : P and h₂ : ¬P, derive any goal (ex falso)
have h₃: Q := by contradiction h₁, h₂
```

**Reductio** — `reductio_ad_absurdum`:
```lean
-- From h₁ : P → False, derive ¬P (just wraps the implication as negation)
have h₂: ¬P := by reductio_ad_absurdum h₁
```

**Elimination** — `neg_elim`:
```lean
-- From h₁ : ¬P → False, derive P (classical double negation elimination)
have h₂: P := by neg_elim h₁
```

### Truth

**Introduction** — `true_intro`:
```lean
have h₁: True := by true_intro
```

### Goal Completion

**`iterate`** — delivers a hypothesis as the proof:
```lean
have h₁: goal_type := ...
iterate h₁
```
This is how every sub-proof concludes. Think of it as "this hypothesis is the answer."

## Proof Structure Pattern

Every proof follows this structure:

```lean
theorem name: ∀ (x: T₁), ∀ (y: T₂), ... → conclusion := by forall_intro
  variable(a: T₁)
  variable(b: T₂)

  -- Step 1: Establish needed facts via forall_elim on axioms/theorems
  have h₁: ... := by forall_elim some_axiom, a
  have h₂: ... := by forall_elim h₁, b

  -- Step 2: Assume antecedent if proving an implication
  assume(h₃: antecedent)

  -- Step 3: Chain deductions
  have h₄: ... := PC₀.deductive_eq_l2r h₂ h₃
  have h₅: ... := by modus_ponens h₄, h₃

  -- Step 4: Deliver the conclusion
  iterate h₅
```

## Common Proof Patterns

### Congruence Proof (for Congruent Predicates/Operations)

Congruence proofs follow the ADT pattern: the predicate is declared as an axiom, its behavior specified by an axiom_def, and the congruence proof unfolds the axiom_def:

```lean
-- Axioms (declared separately)
axiom my_pred: U.Particular → Prop
axiom my_pred_def: ∀ (x: U.Particular), my_pred x ↔ ...

-- Congruent wrapper: proof unfolds my_pred_def
def my_predicate: CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ my_pred x)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (pred x ↔ pred y) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    -- Unfold axiom_def for both a and b
    have h₁: my_pred a ↔ ... := by forall_elim my_pred_def, a
    have h₂: my_pred b ↔ ... := by forall_elim my_pred_def, b
    assume(h₃: a =₍U₎ b)
    -- Prove pred a ↔ pred b by converting through the unfolded form
    have h₄: pred a → pred b := by ...
    have h₅: pred b → pred a := by ...
    have h₆: pred a ↔ pred b := by iff_intro h₄, h₅
    iterate h₆
  { pred := pred, cong := cong }
```

### Iff-Chain Pattern

Common when proving equivalences by chaining through intermediate iff steps:

```lean
-- Given h₁ : A ↔ B and h₂ : B ↔ C, prove A → C
assume(h₃: A)
have h₄: B := PC₀.deductive_eq_l2r h₁ h₃
have h₅: C := PC₀.deductive_eq_l2r h₂ h₄
iterate h₅
```

### Using eq_def for Set Equality

To work with set equality, always instantiate `eq_def` first:

```lean
have h₁: ∀ S₂: Set U, A =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), A.pred x ↔ S₂.pred x := by forall_elim eq_def, A
have h₂: A =ₛₑₜ B ↔ ∀ (x: U.Particular), A.pred x ↔ B.pred x := by forall_elim h₁, B
```

### Working with `∃!₍U₎`

`ExistsUnique` is an axiom — Lean cannot unfold it definitionally. Pick the right helper for the shape your proof needs.

**Extract a witness** — the most common case, when you have `∃!₍U₎ x, P x` and just need `∃ x, P x` (uniqueness discarded):

```lean
have h₂: ∃ (x: U.Particular), P x := unique_existence_implies_existence h₁
```

Defined at `Logic/PredicateCalculus/Definitions/ExistsUnique/Properties/UniqueExistenceImpliesExistence.lean`.

**Collapse two witnesses to the same value** — when you have `∃!₍U₎ x, P x` and need to show any two particulars satisfying `P` are equal (typical of right-determinacy proofs):

```lean
have h₂: ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), P y₁ ∧ P y₂ → y₁ =₍U₎ y₂ := unique_existence_implies_uniqueness h₁
```

Defined at `Logic/PredicateCalculus/Definitions/ExistsUnique/Properties/UniqueExistenceImpliesUniqueness.lean`.

**Pack/unpack via `exists_unique_def`** — when you need the full `∃ x, P x ∧ uniqueness` shape (cong proofs that transport `∃!` across an iff, or any work where the uniqueness clause matters). Instantiate at both `U` and the predicate in one `forall_elim` call:

```lean
-- 1. Convert ∃! ↔ ∃ ∧ uniqueness (peels both ∀s in one call)
have h₁: (∃!₍U₎ (x: U.Particular), Q x) ↔ (∃ (x: U.Particular), Q x ∧ (∀ (y: U.Particular), Q y → y =₍U₎ x))
    := by forall_elim exists_unique_def, U, (x: U.Particular ↦ Q x)
-- 2. Convert ∃! → existential via deductive_eq_l2r
-- 3. Work with the existential (exists_elim, and_elim, etc.)
-- 4. Repack via deductive_eq_r2l if needed
```

See `Universals/Sets/Predicates/Unary/Singleton/Predicate.lean` for a complete pack/unpack example (cong proof). For the simpler shortcuts, the canonical examples are `Universals/Sets/Predicates/Binary/SingletonElemGraph/Properties/LeftTotality.lean` (extract witness) and `RightDeterminacy.lean` in the same directory (collapse two witnesses).

### Using Existing Congruence Proofs

When a congruent predicate already exists, leverage its `.cong` field:

```lean
-- subsets_of derives congruence from inclusion_predicate.cong
have h₅: A₁ ⊆ₛₑₜ A ↔ A₂ ⊆ₛₑₜ A := by modus_ponens h₄, h₁
```

## Hypothesis Naming Convention

**The only legal hypothesis name is `h` followed by subscript digits**: `h₁`, `h₂`, …, `h₁₀`, `h₁₁`, …

- **Sequential at each scope level**: `h₁`, `h₂`, `h₃`, … in the order introduced. Numbering restarts inside nested sub-blocks (see below).
- **`assume(h_n: …)` participates in the sequence**: the first `assume` at a scope is `h₁`, the next is `h₂`, the first `have` after them is `h₃`, etc. (`variable(…)` and `forall_intro` introduce *terms*, not hypotheses, so they don't consume names.)
- **Nested subscripts inside sub-blocks**: inside the `by` body of `have h_n: … := by`, child hypotheses use the parent's subscript as a prefix — `h_n_1`, `h_n_2`, …. So inside `have h₈: … := by`, children are `h₈₁`, `h₈₂`, `h₈₃`, …
- **Never use letters, primes, descriptive suffixes**: `hx`, `hy`, `hxx`, `hX`, `h_forward`, `h_P`, `h_step1` are all forbidden. If a hypothesis records "x =₍U₎ x" (refl), it still gets the next sequential `h_n` name like any other.

Reason: the natural-deduction style depends on a rigid mechanical naming so the reader can scan the proof linearly without parsing semantic suffixes. Combined with the explicit-type rule below, this makes each line a self-contained assertion.

## Variable Naming Convention

Distinguish **quantified variables** (bound names in propositions) from **fresh constants** introduced by ∀-introduction:

- **Quantified variables** in `∀ (x: T), …` and `∃ (x: T), …` — use `x`, `y`, `z`, with subscripts when more than three appear (`x₁`, `x₂`, `y₁`, `y₂`, …). These are bound names belonging to the proposition.
- **Fresh constants** introduced by the `variable(c: T)` tactic — use names typically reserved for constants (`a`, `b`, `c`, `d`, …). These name specific witnesses standing in for arbitrary values in the proof body.

```lean
-- ✓ Right
theorem foo: ∀ (x: U.Particular), ∀ (y: U.Particular), P x y := by forall_intro
  variable(a: U.Particular)
  variable(b: U.Particular)
  have h₁: P a b := ...
  iterate h₁

-- ✗ Wrong — quantified names reused as constants
theorem foo: ∀ (x: U.Particular), ∀ (y: U.Particular), P x y := by forall_intro
  variable(x: U.Particular)
  variable(y: U.Particular)
```

Reason: the role of every identifier should be clear at a glance. `x`/`y`/`z` always mean "bound by a quantifier in the proposition," and `a`/`b`/`c` always mean "fresh constant standing in for an arbitrary value." A reader doesn't have to look up whether a name is bound or introduced.

## Every `have` Clause Must Declare Its Type

```lean
-- WRONG — reader has to chase backwards to discover what h₇ is:
have h₇ := by forall_elim h₆, z₂

-- RIGHT — type makes the assertion explicit; tactic confirms derivation:
have h₇: x =₍U₁₎ x → y =₍U₂₎ y → z₁ =₍U₃₎ z₂ → (R.pred x y z₁ ↔ R.pred x y z₂)
    := by forall_elim h₆, z₂
```

This applies to every step — `forall_elim`, `modus_ponens`, `and_intro`, term-mode `PC₀.deductive_eq_l2r`, everything. The proof reads as a sequence of declared propositions; tactics are justification, not exposition. The only exception is the *root* `theorem` or `def` declaration, whose type is the goal.

## Authorship Convention

When Claude writes a proof, add an authorship comment using the **current model name and current date** (look them up from the environment — don't copy a stale example):

```lean
-- Proof by Claude <Model Name> (<model-id>), YYYY-MM-DD
theorem my_theorem: ... := by forall_intro
```

## Schema Fields Are Always Eliminated Explicitly — Never in Term Mode

**Schema fields carrying `∀`-quantifiers — `U.eq.refl`, `U.eq.sym`, `U.eq.trans`, and any analogous field on any other schema — must never be applied in term mode.** Each quantifier instantiation requires an explicit `forall_elim`; each implication application requires an explicit `modus_ponens`. Term-mode application of such fields is **forbidden**, even though Lean would accept it.

```lean
-- ✗ FORBIDDEN — hides two `forall_elim`s and a `modus_ponens` in one opaque term:
have h₆: b =₍U₎ a := U.eq.sym a b h₅

-- ✓ REQUIRED — each ND step is explicit, named, and typed:
have h₆: a =₍U₎ b → b =₍U₎ a := by forall_elim U.eq.sym, a, b
have h₇: b =₍U₎ a := by modus_ponens h₆, h₅
```

Same for `U.eq.trans`:

```lean
-- ✗ FORBIDDEN:
have h₄: y =₍U₎ b := U.eq.trans y a b h₃

-- ✓ REQUIRED:
have h₄: y =₍U₎ a ∧ a =₍U₎ b → y =₍U₎ b := by forall_elim U.eq.trans, y, a, b
have h₅: y =₍U₎ b := by modus_ponens h₄, h₃
```

**Why this matters**: the framework's discipline is that every first-order reasoning step is visible. Term-mode application of a quantified schema field silently composes multiple `forall_elim`s with a `modus_ponens` into one term, hiding the structure of the proof. The longer form is the right form — every step has a name and a stated type, every elimination is a separate line.

**Boundary**: this rule targets *schema fields with `∀`-quantifiers*. Term-mode application of propositional helpers like `PC₀.deductive_eq_l2r h₁ h₂` is fine — those are closed propositional theorems, not ND eliminations, so they don't hide any first-order steps.

## Key Propositional Logic Helpers (`PC₀`)

- `PC₀.deductive_eq_l2r` — from `P ↔ Q` and `P`, derive `Q`
- `PC₀.deductive_eq_r2l` — from `P ↔ Q` and `Q`, derive `P`
- `PC₀.iff_comm` — `(P ↔ Q) ↔ (Q ↔ P)`
- `PC₀.iff_contrapositiveness` — `(P ↔ Q) ↔ (¬P ↔ ¬Q)`

## Pitfalls

- **`forall_elim` uses comma syntax**: `by forall_elim h, value` — not `by forall_elim h value`. Use the multi-arg form (up to 6) instead of chaining.
- **`iterate` is mandatory**: Every sub-proof branch must end with `iterate`. Without it, the proof won't close.
- **Don't mix Lean tactics**: Even `exact` is forbidden. Use `iterate` to deliver results.
- **Predicate-shape lambdas always use the project's statement template syntax `(x: T ↦ body)`** — never `fun x : T => body` and never untyped `fun x => body`. The project defines a dedicated notation for predicate-shape lambdas in `Logic/PredicateCalculus/Definitions/StatementTemplate/Definition.lean`, supporting unary `(x: T ↦ body)`, binary `(x: T₁, y: T₂ ↦ body)`, and ternary `(x: T₁, y: T₂, z: T₃ ↦ body)`. Standard `fun` is reserved for non-predicate functions where the statement-template syntax doesn't apply (e.g., the value of a `let pred` inside a definition body where the type is already determined). When in doubt for a predicate, use `↦`.
- **`noncomputable` keyword**: Required when a `def` bundles axioms into a structure (e.g., `noncomputable def powerset_operation`).
