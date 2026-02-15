---
name: lean-math-overview
description: This skill should be used when starting work on the lean-math project, when needing to understand the project's architecture, philosophy, or file structure. It provides the foundational context for all work in this Lean 4 formalization of Neo-Logicism.
---

# Lean-Math Project Overview

## Core Philosophy: Mathpunk Neo-Logicism

This project formalizes mathematics from first-order logic (FOL) using Lean 4 as a proof assistant. The approach is called **Mathpunk**: DIY foundations, radical explicitness, and power over safety.

**Key principle**: Some structures are **derived** from logic — sets, for example, are derived from predicates. Others — like natural numbers — are **postulated** as initial objects, ADT-style, within typed first-order logic. The project shows that set theory, traditionally built on ZFC axioms, can be derived from predicate logic, while other mathematical objects can be introduced axiomatically without leaving FOL.

**Critical constraint**: All proofs must be explicit FOL proofs using custom natural deduction tactics. Do NOT use Lean's built-in `simp`, `omega`, `decide`, `rfl`, or automation tactics. The project defines its own proof infrastructure.

## Architecture: The Three-Layer Stack

### Layer 1: Logic (`Logic/`)

The foundational layer implementing propositional and predicate calculus.

- **`Logic/PropositionalCalculus/`** — PC0: propositional logic definitions and theorems
- **`Logic/NaturalDeduction/`** — Custom natural deduction tactics (22 tactics across 16 files). Examples:
  - `forall_intro` / `forall_elim`, `assume` / `modus_ponens`, `iff_intro` / `iff_elim`
  - `and_intro` / `and_elim`, `or_intro` / `or_elimination`, `exists_intro`
  - `contradiction` / `reductio_ad_absurdum`, `neg_elim`, `true_intro`
  - `iterate` — goal completion, `variable` / `constant` — introduce bound variables
  - See the **lean-math-proofs** skill for full syntax and proof patterns.
- **`Logic/PredicateCalculus/Schemas/`** — Core type schemas (see below)

### Layer 2: Schemas (`Logic/PredicateCalculus/Schemas/`)

Schemas are Lean `structure`s that enforce recurring organizational patterns. On pen and paper, you'd manually track that every equality has reflexivity/symmetry/transitivity, every universal has its equality, every predicate has its congruence proof. Schemas automate this bookkeeping. Current schemas (check `Logic/PredicateCalculus/Schemas/` for the definitive set):

| Schema | Purpose |
|--------|---------|
| `Equality` | `pred`, `refl`, `sym`, `trans` over a type |
| `Universal` | Pairs a `Particular` type with an `Equality` |
| `CongruentUnaryPredicate` | Predicate + proof it respects equality |
| `CongruentBinaryPredicate` | Binary relation + congruence proof |
| `CongruentTernaryPredicate` | Ternary relation + congruence proof |
| `CongruentUnaryOperation` | Operation + proof it preserves equality |
| `SubUniversal` | Refined type of a Universal via a congruent predicate |

**The Universal is the central concept**: a type (`Particular`) paired with its own custom equality (NOT Leibniz equality). Everything is parameterized on Universals.

**Equality notation**: `a =₍U₎ b` means `U.eq.pred a b` — equality in Universal U.

### Sub-Universals and the `↑` Notation

A `SubUniversal` refines a Universal U by a congruent predicate P, producing a new Universal whose particulars are elements of U satisfying P. This is syntactic sugar over FOL — not a departure:

```
∀ x : (sub_universal U P).Particular, Q(x)  ≡  ∀ x : U.Particular, P.pred x → Q(x)
```

Given `x : (sub_universal U P).Particular`:

- `x` — the subtype element (value + proof bundled)
- `↑x` (or `x.val`) — the underlying `U.Particular` element
- `x.property` — proof that `↑x` satisfies the predicate

The `↑` notation is defined as `scoped prefix:max "↑" => Subtype.val` in `SubUniversal/Schema.lean`.

**When to use `↑` vs `x` directly:**

| Context | Use | Example |
|---------|-----|---------|
| Predicates on the sub-universal | `x` directly | `x =₍sub_universal U P₎ y` |
| Predicates on parent universal U | `↑x` | `Q.pred ↑x` |
| Sub-universal's equality | `x` directly | `x =₍SU₎ y` |
| Parent universal's equality | `↑x` | `↑x =₍U₎ ↑y` |

**Pitfall**: Coercion from sub-universals to parent doesn't work automatically. Lean's type class inference cannot determine P from `(sub_universal U P).Particular`. Always use `↑x` explicitly.

### Layer 3: Universals (`Universals/`)

Concrete mathematical structures built on the schemas. Current universals (check `Universals/` for the definitive set):

- **`Universals/Sets/`** — Set theory derived from predicates
- **`Universals/NaturalNumbers/`** — Natural number formalization
- **`Universals/Relations/`** — Relation structures
- **`Universals/Categories/`** — Category theory

## File Organization: ADT Barrel Pattern

See the **lean-math-conventions** skill for full naming conventions, placement rules, namespace conventions, and and notation standards.

Files follow an ADT (Abstract Data Type) barrel pattern:

```
Universals/Sets/
├── Universal.lean              # Set Universal definition
├── Definitions/
│   ├── SetComprehension/Definition.lean
│   └── SetsAsTypes/Definition.lean
├── Predicates/
│   ├── Binary/
│   │   ├── Membership/Predicate.lean
│   │   └── Inclusion/Predicate.lean
│   └── Unary/
│       └── Singleton/Predicate.lean
├── Operations/
│   ├── Constants/
│   │   ├── EmptySet/Operation.lean
│   │   └── UniversalSet/Operation.lean
│   └── Unary/
│       └── Powerset/Operation.lean
├── Universals/                 # Sub-universals of Set
│   └── Singleton/Universal.lean
├── Properties/
│   ├── SetExtensionality.lean
│   ├── EmptySetExistence.lean
│   └── UniversalSetExistence.lean
├── Definitions.lean            # Barrel import
├── Predicates.lean             # Barrel import
├── Operations.lean             # Barrel import
├── Universals.lean             # Barrel import
└── Properties.lean             # Barrel import
```

Each concept has its own directory. Barrel files re-export all contents.

## Namespace Convention

Each Universal X has its own namespace under `Universe`. Logic schemas live under `Logic.PC₁`. Example for Sets:

```lean
namespace Universe
namespace Sets
open Logic
open Logic.PC₁
-- ... definitions ...
end Sets
end Universe
```

For another Universal (e.g., NaturalNumbers), replace `Sets` accordingly.

## Pitfalls

- **Never use Lean automation** (`simp`, `omega`, `decide`, `rfl`, `exact`). Only use the custom natural deduction tactics.
- **Never create files without understanding the barrel pattern**. New concepts get their own directory and must be imported in the barrel file.
- **U is a free variable** that Lean auto-binds as an implicit parameter. This is NOT a fixed constant — it's polymorphic over any Universal.
- **`noncomputable`** may be needed for definitions that bundle axioms (like `powerset_operation`).
- **Don't over-engineer**. The user values minimalism and explicit foundations.

## Keeping Skills Updated

Skills are the knowledge base for future sessions. When making architectural decisions, adding new concepts, or establishing new patterns, update the relevant skills:

- **Per-universal skills** (like `lean-math-sets`): Update when adding new operations, predicates, or properties. Keep it as an overview pointing to the code — not an exact mirror.
- **Overview**: Update when adding new schemas or universals.
- **Conventions**: Update when establishing new naming patterns, file organization rules, or notation.
- **Proofs**: Update when adding new tactics or proof patterns.

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
