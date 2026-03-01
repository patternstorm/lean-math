---
name: lean-math-dyads
description: This skill should be used when working with the Dyad Universal in the lean-math project. It covers co-existence, predicate curry/uncurry, predicate associativity, the ⋈ notation conventions, and the ADT specification.
---

# Dyads in Lean-Math

## Philosophy: Co-Existence

A dyad `a ⋈ b` asserts that `a` and `b` co-exist in the universe. Nothing more — no direction, no relation, no properties. Before predication, a dyad has no relational content; it only asserts that its two particulars can be relata. Predicates actualize which relations hold.

Particulars and dyads are equally primitive. Unary predicates on particulars actualize **properties**; unary predicates on dyads actualize **relations**. Since dyads are themselves particulars of their own Universal, all predicates remain unary — they just act on different structural levels.

The universe is closed under co-existential binding at all levels. Because dyads are predicate-associative, the dimension of a co-existence is the number of base particulars it involves:

- 1-dim: a single particular
- 2-dim: a dyad of two particulars (`a ⋈ b`)
- 3-dim: three particulars (`a ⋈ (b ⋈ c)`, equivalently `(a ⋈ b) ⋈ c`)
- n-dim: n base particulars, nested in any order

## Notation: The `⋈` Symbol

The `⋈` symbol is overloaded with two meanings, disambiguated by type:

| Context | Meaning | Result type |
|---------|---------|-------------|
| Between Universals | `DyadUniversal U₁ U₂` | `Universal` |
| Between Particulars | `bind a b` | `Dyad U₁ U₂` |

Both notations use precedence 35 — matching precedences lets Lean disambiguate by type.

**Getting the type of dyads**: Use `(U₁ ⋈ U₂).Particular` to refer to the type. The raw `Dyad U₁ U₂` type should only appear in `Particular.lean` and `Universal.lean` (the defining files), where the `DyadUniversal` notation isn't yet available.

**Bootstrapping constraint**: `DyadUniversal` is defined at the end of `Universal.lean`, after the equivalence proofs. So within `Particular.lean` and `Universal.lean`, `Dyad U₁ U₂` is the only option. All downstream files should use `(U₁ ⋈ U₂).Particular`.

## Naming Convention

| Concept | Name | Definition |
|---------|------|------------|
| Type of dyads | `Dyad U₁ U₂` | `axiom Dyad(U₁: Universal)(U₂: Universal): Type` |
| Dyad Universal | `U₁ ⋈ U₂` | `notation:35 U₁:36 " ⋈ " U₂:36 => DyadUniversal U₁ U₂` |
| Dyad equality | `=ₗₓₗ` | `notation:50 a:51 " =ₗₓₗ " b:51 => eq a b` |
| Dyad constructor | `a ⋈ b` | `notation:35 x:36 " ⋈ " y:36 => bind x y` |

## ADT Specification

The Dyad is postulated as an abstract data type in `Particular.lean`:

```lean
-- Type
axiom Dyad(U₁: Universal)(U₂: Universal) : Type

-- Equality
axiom eq: Dyad U₁ U₂ → Dyad U₁ U₂ → Prop

-- Generative Constructor
axiom bind{U₁: Universal}{U₂: Universal}: U₁.Particular → U₂.Particular → Dyad U₁ U₂

-- Impurifier Equations (relatum-wise equality)
axiom eq_def: ∀ (a₁: U₁.Particular), ∀ (b₁: U₂.Particular),
  ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
  (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂

-- Exhaustiveness (single non-recursive constructor, no induction needed)
axiom exhaustiveness: ∀ d: Dyad U₁ U₂,
  ∃ a: U₁.Particular, ∃ b: U₂.Particular, d 🟰 (a ⋈ b)
```

The equivalence proofs (refl, sym, trans) are in `Universal.lean`, derived from exhaustiveness and relatum-wise equality.

## Predicate Curry and Uncurry

Axiom schemes that transport between binary predicates and unary predicates on dyads. They operate on **statement templates** (placeholders), not functions.

```lean
-- Uncurry: binds two independent placeholders into a single dyad placeholder
axiom uncurry {U₁: Universal}{U₂: Universal}
  (R: U₁.Particular → U₂.Particular → Prop): (U₁ ⋈ U₂).Particular → Prop
axiom uncurry_def {U₁: Universal}{U₂: Universal}
  (R: U₁.Particular → U₂.Particular → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), uncurry R (a ⋈ b) ↔ R a b

-- Curry: splits a dyad placeholder into two independent placeholders
axiom curry {U₁: Universal} {U₂: Universal}
  (P: (U₁ ⋈ U₂).Particular → Prop): U₁.Particular → U₂.Particular → Prop
axiom curry_def {U₁: Universal} {U₂: Universal}
  (P: (U₁ ⋈ U₂).Particular → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), curry P a b ↔ P (a ⋈ b)
```

**Why axiom schemes**: Lambda abstraction would treat predicates as functions, creating a circularity — `Functions` are derived from predicates in this framework. See README.md "Variable-Arity Predicates".

**Explicit Universal bindings are required** on curry/uncurry axioms (`{U₁: Universal} {U₂: Universal}`) to resolve `⋈` notation ambiguity.

**Higher arities compose**: A ternary predicate `R(x,y,z)` becomes a unary predicate on `(U₁ ⋈ (U₂ ⋈ U₃)).Particular` by applying uncurry twice. The same two axiom schemes handle any arity.

## Predicate Associativity

Different nestings of n base particulars are predicate-equivalent. This justifies the dimensional classification: dimension depends only on the count of base particulars, not on nesting order.

**Status**: Proved in `Test/PredicateAssociativity.lean` (not yet promoted to production). The proof uses nested uncurry to construct a reassociated predicate, then chains two applications of `uncurry_def` to show propositional equivalence.

## File Organization

```
Universals/Dyads/
├── Particular.lean                          # Dyad ADT: type, eq, bind, eq_def, exhaustiveness
├── Universal.lean                           # Equivalence proofs + DyadUniversal + ⋈ notation
├── Definitions.lean                         # Barrel file
├── Definitions/
│   ├── Curry/Definition.lean                # Predicate curry axiom scheme
│   └── Uncurry/Definition.lean              # Predicate uncurry axiom scheme
```

## Pitfalls

- **`⋈` ambiguity**: Both `bind` and `DyadUniversal` use `⋈`. Explicit `{U₁: Universal}` bindings are needed on axioms that use `(U₁ ⋈ U₂).Particular` so Lean can disambiguate.
- **Precedence must match**: Both `⋈` notations use precedence 35. Different precedences cause ambiguity errors.
- **`Dyad U₁ U₂` only in defining files**: Use `(U₁ ⋈ U₂).Particular` in all downstream code.
- **`noncomputable` for axiom bundles**: Definitions wrapping curry/uncurry axioms need this keyword.

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
