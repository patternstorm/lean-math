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
have h₂: P specific_value := by forall_elim h₁, specific_value
```
Instantiates a universally quantified hypothesis with a specific value. Comma-separated: `forall_elim hypothesis, value`.

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

Note: `exists_elim` is a def (identity on existentials), not a tactic.

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
have h₁: ∀ S₂: (Set U).Particular, A =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), A.pred x ↔ S₂.pred x := by forall_elim eq_def, A
have h₂: A =ₛₑₜ B ↔ ∀ (x: U.Particular), A.pred x ↔ B.pred x := by forall_elim h₁, B
```

### ExistsUnique Pack/Unpack Pattern

When proving congruence for predicates involving `∃!₍U₎`, you must explicitly convert between `ExistsUnique` and its existential form via `exists_unique_def`:

```lean
-- 1. Instantiate the axiom schema for the current Universal
have h₃: ∀ (P: U.Particular → Prop), ExistsUnique U P ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x)) := by forall_elim exists_unique_def, U

-- 2. Unpack for specific predicates
have h₄: ExistsUnique U (x: U.Particular ↦ x ∈ₛₑₜ A) ↔ (∃ (x: U.Particular), x ∈ₛₑₜ A ∧ (∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ x)) := by forall_elim h₃, (x: U.Particular ↦ x ∈ₛₑₜ A)

-- 3. Convert: pred A (= ExistsUnique) → existential form
have h₈₂: ∃ ... := PC₀.deductive_eq_l2r h₄ h₈₁

-- 4. Work with the existential (exists_elim, and_elim, etc.)

-- 5. Repack: existential form → pred B (= ExistsUnique)
have h₈₁₁: pred B := PC₀.deductive_eq_r2l h₅ h₈₁₀
```

This pattern is necessary because `ExistsUnique` is an axiom — Lean cannot unfold it definitionally. See `Universals/Sets/Predicates/Unary/Singleton/Predicate.lean` for a complete example.

### Using Existing Congruence Proofs

When a congruent predicate already exists, leverage its `.cong` field:

```lean
-- subsets_of derives congruence from inclusion_predicate.cong
have h₅: A₁ ⊆ₛₑₜ A ↔ A₂ ⊆ₛₑₜ A := by modus_ponens h₄, h₁
```

## Hypothesis Naming Convention

- Use `h₁`, `h₂`, `h₃` for sequential steps
- Use nested numbering for sub-proofs: `h₂₁`, `h₂₂` inside a block started by `h₂`
- Always follow this convention — no descriptive names like `h_forward`, `h_P`, etc.

## Authorship Convention

When Claude writes a proof, add an authorship comment:

```lean
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
theorem my_theorem: ... := by forall_intro
```

Use the current model name and date. The user has explicitly requested this.

## Equality Schema in Term Mode

The `Equality` schema fields (`U.eq.refl`, `U.eq.sym`, `U.eq.trans`) can be applied directly in term mode — no need to multi-step `forall_elim` on them:

```lean
-- Symmetry: from h₅ : a =₍U₎ b, derive b =₍U₎ a
have h₆: b =₍U₎ a := U.eq.sym a b h₅

-- Transitivity: from h₁ : y =₍U₎ a and h₂ : a =₍U₎ b, derive y =₍U₎ b
have h₃: y =₍U₎ a ∧ a =₍U₎ b := by and_intro h₁, h₂
have h₄: y =₍U₎ b := U.eq.trans y a b h₃
```

This is much more concise than instantiating the schema step-by-step with `forall_elim`. Works for any Universal's equality.

## Key Propositional Logic Helpers (`PC₀`)

- `PC₀.deductive_eq_l2r` — from `P ↔ Q` and `P`, derive `Q`
- `PC₀.deductive_eq_r2l` — from `P ↔ Q` and `Q`, derive `P`
- `PC₀.iff_comm` — `(P ↔ Q) ↔ (Q ↔ P)`
- `PC₀.iff_contrapositiveness` — `(P ↔ Q) ↔ (¬P ↔ ¬Q)`

## Pitfalls

- **`forall_elim` uses comma syntax**: `by forall_elim h, value` — not `by forall_elim h value`.
- **`iterate` is mandatory**: Every sub-proof branch must end with `iterate`. Without it, the proof won't close.
- **Don't mix Lean tactics**: Even `exact` is forbidden. Use `iterate` to deliver results.
- **Lambda types in predicates**: Always use explicit type annotation in lambdas: `(x: U.Particular ↦ ...)`. Never rely on inference.
- **`noncomputable` keyword**: Required when a `def` bundles axioms into a structure (e.g., `noncomputable def powerset_operation`).

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
