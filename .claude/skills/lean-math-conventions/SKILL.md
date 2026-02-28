---
name: lean-math-conventions
description: This skill should be used when creating new files, naming definitions, defining notation, or organizing code in the lean-math project. It covers naming conventions, file organization patterns, notation standards, and user preferences for code style.
---

# Lean-Math Conventions

## File Organization

### ADT Barrel Pattern

Every concept gets its own directory with a descriptive file. Each concept category has an associated barrel file that re-exports all its contents:

```
Universals/Sets/
├── Universal.lean                          # Set Universal definition
├── Definitions.lean                        # ← barrel file for Definitions/
├── Definitions/
│   ├── SetComprehension/Definition.lean
│   └── SetsAsTypes/Definition.lean
├── Predicates.lean                         # ← barrel file for Predicates/
├── Predicates/
│   ├── Binary/
│   │   ├── Membership/Predicate.lean
│   │   └── Inclusion/Predicate.lean
│   └── Unary/
│       └── Singleton/Predicate.lean
├── Operations.lean                         # ← barrel file for Operations/
├── Operations/
│   ├── Constants/
│   │   ├── EmptySet/Operation.lean
│   │   └── UniversalSet/Operation.lean
│   ├── Binary/
│   │   └── Union/Operation.lean
│   └── Unary/
│       └── Powerset/Operation.lean
├── Universals.lean                         # ← barrel file for Universals/
├── Universals/
│   └── Singleton/Universal.lean            # Sub-universal: singleton sets
└── Properties.lean                         # ← barrel file for Properties/
    └── Properties/
        ├── SetExtensionality.lean
        └── EmptySetExistence.lean
```

When adding a new file, always update the corresponding barrel file.

### Category Naming

| Category | File Name | Purpose |
|----------|-----------|---------|
| Schemas | `Schema.lean` | Core type schemas (Equality, Universal, etc.) |
| Universals | `Universal.lean` | Universal definitions (type + equality) |
| Sub-universals | `Universals/Name/Universal.lean` | Sub-universals defined by a congruent predicate |
| Definitions | `Definition.lean` | Type definitions, constructors |
| Predicates | `Predicate.lean` | Congruent predicates (unary, binary) |
| Operations | `Operation.lean` | Congruent operations, constants |
| Properties | Named by property | Theorems about the structure |

### Where to Place New Concepts

For any Universal X (Sets, NaturalNumbers, Relations, Categories, etc.):

- **New universal** → `Universals/X/Universal.lean`
- **New sub-universal** → `Universals/X/Universals/Name/Universal.lean`
- **New predicate** → `Universals/X/Predicates/Binary/` or `Unary/`
- **New operation** → `Universals/X/Operations/Unary/`, `Binary/`, or `Constants/`
- **New property/theorem** → `Universals/X/Properties/`
- **New definition** → `Universals/X/Definitions/`
- **New schema** → `Logic/PredicateCalculus/Schemas/`
- **Always update the barrel file** when adding a new file

## Statement Template Syntax (`↦`)

**Always use `↦` syntax, never `fun ... =>`.** Predicates are statement templates — propositions with free variables — not computational functions. Using `fun` conflates the two. The `↦` notation (defined in `StatementTemplate/Definition.lean`) conveys the right concept.

```lean
-- CORRECT: statement template syntax
let pred: U.Particular → Prop := (x: U.Particular ↦ P x)
by forall_elim h₁, (x: U.Particular ↦ x ∈ₛₑₜ A)

-- WRONG: Lean's function syntax
let pred: U.Particular → Prop := fun (x: U.Particular) => P x
by forall_elim h₁, (fun (x: U.Particular) => x ∈ₛₑₜ A)
```

The `↦` syntax works everywhere: `let` bindings, type annotations, tactic arguments.

## Explicit Typing

**Every variable, definition, axiom, and `let` binding must have an explicit type annotation.** Never rely on Lean's type inference to omit types. This is a core style principle — radical explicitness.

```lean
-- CORRECT: explicit types everywhere
variable(a: U.Particular)
have h₁: A =ₛₑₜ B := ...
let pred: U.Particular → Prop := (x: U.Particular ↦ ...)
let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (pred x ↔ pred y) := ...
axiom mem: U.Particular → Particular U → Prop
theorem eq_refl: ∀ (S: Particular U), S =ₛₑₜ S := ...

-- WRONG: missing types
variable(a)
have h₁ := ...
let pred := (x ↦ ...)
```

## Naming Conventions

### Definitions and Functions

- **Snake_case** for all definitions: `set_as_universal`, `sub_universal`, `mem_predicate`
- **Descriptive names** that convey the mathematical meaning:
  - `supersets_of A` — predicate for "sets that A is a subset of"
  - `subsets_of A` — predicate for "sets that are subsets of A"
  - `elements_of x` — predicate for "sets containing x"
  - `set_as_universal` — converting a set to a sub-universal

### Axioms and Theorems

- Axiom names describe what they define: `mem_def`, `eq_def`, `inclusion_def`, `powerset_def`
- Theorem names describe what they prove: `eq_refl`, `eq_sym`, `eq_trans`, `set_extensionality`
- Congruence theorems: `powerset_cong`

### Structures

- Structure names are PascalCase: `Universal`, `Equality`, `CongruentUnaryPredicate`
- Instances of structures use snake_case: `powerset_operation`, `mem_predicate`, `inclusion_predicate`

### Universal Naming Pattern

Each Universal has three names:

| Role | Pattern | Examples |
|------|---------|----------|
| Internal def name | `XUniversal` (PascalCase) | `SetsUniversal`, `SingletonSetUniversal` |
| Bold Unicode notation (the Universal) | `𝐗` (bold) | `𝐍𝐚𝐭`, `𝐒𝐞𝐭`, `𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭` |
| Plain text type alias (the particulars) | readable name | `ℕ`, `Set U`, `SingletonSet U` |

Use the **bold Universal** (`𝐒𝐞𝐭 U`) wherever a `Universal` argument is expected (schemas, `sub_universal`, `∃!₍...₎`). Use the **plain type** (`Set U`) for type annotations of values.

## Notation Conventions

### Subscript Style

Each Universal has its own subscript notation. For example, Sets use `ₛₑₜ`:

| Notation | Meaning |
|----------|---------|
| `=ₛₑₜ` | Set equality |
| `∈ₛₑₜ` | Set membership |
| `∉ₛₑₜ` | Set non-membership |
| `⊆ₛₑₜ` | Set inclusion |
| `{x}ₛₑₜ` | Singleton set of x |
| `⊙` | Singleton element extraction (prefix) |
| `∪ₛₑₜ` | Set union (binary infix) |

### Universal Equality

```lean
notation:50 a:51 " =₍" U:51 "₎ " b:51 => universal_eq U a b
```

Use `=₍U₎` for equality in Universal U. For set equality, prefer `=ₛₑₜ` over `=₍𝐒𝐞𝐭 U₎` — it's polymorphic across levels.

**Sub-universal equality**: `=₍sub_universal U P₎` is definitionally equal to `=₍U₎` on lifted values. Prefer `↑x =₍U₎ ↑y` over `x =₍sub_universal U P₎ y` — it's clearer and avoids verbose sub-universal names.

### Prefix Operators

```lean
prefix:max "𝒫" => powerset
scoped prefix:max "↑" => Subtype.val
```

Use `prefix:max` for prefix operators. The `scoped` keyword makes notation available only when the namespace is opened.

### Notation Precedence

All binary relation notations use `notation:50 a:51 ... b:51` — precedence 50 with arguments at 51.

## Definition Style

### Axiomatic Definitions (ADT Style)

Mathematical objects are modelled as Abstract Data Types (ADTs). An ADT is a type together with its operations and predicates, all specified axiomatically. The full pattern, from type to Universal:

#### Step 1: Particulars — the type and its constructors

Particulars can be **postulated** (like natural numbers) or **derived** (like sets).

For postulated types, declare the type and its generative constructors as axioms:

```lean
-- Type
axiom NaturalNumber : Type
notation "ℕ" => NaturalNumber

-- Generative constructors (these are operations)
axiom zero : ℕ
axiom succ : ℕ → ℕ
```

For derived types, the type is a `def` based on existing concepts:

```lean
def Set (U: Universal): Type := CongruentUnaryPredicate U
```

#### Step 2: Equality — the impurifier equations

Declare equality as an axiom, then specify it via a grid of constructor interactions:

```lean
axiom eq: ℕ → ℕ → Prop
notation:50 a:51 " =ₙₐₜ " b:51 => eq a b

-- Impurifier equations: n×n grid of constructor pairs
--              𝟬                𝚜 m
--   𝟬    𝟬 =ₙₐₜ 𝟬          ¬(𝟬 =ₙₐₜ 𝚜 m)
--   𝚜 n  ¬(𝚜 n =ₙₐₜ 𝟬)    𝚜 n =ₙₐₜ 𝚜 m ↔ n =ₙₐₜ m
axiom zero_refl: 𝟬 =ₙₐₜ 𝟬
axiom zero_is_not_succ: ∀ (n: ℕ), ¬(𝟬 =ₙₐₜ 𝚜 n)
axiom succ_is_not_zero: ∀ (n: ℕ), ¬(𝚜 n =ₙₐₜ 𝟬)
axiom succ_cong: ∀ (n: ℕ), ∀ (m: ℕ), (𝚜 n) =ₙₐₜ (𝚜 m) ↔ n =ₙₐₜ m
```

For derived types like sets, equality is specified by a single axiom_def (e.g., extensionality).

#### Step 3: Induction instances (postulated types only)

Since postulated types are opaque axioms (not Lean `inductive`), Lean provides no recursor. Provide one induction axiom instance per predicate that needs it (axiom scheme, not second-order):

```lean
axiom exhaustiveness_induction: ∀ (n: ℕ), n =ₙₐₜ 𝟬 ∨ ∃ (k: ℕ), n =ₙₐₜ 𝚜 k
axiom eq_refl_induction: ∀ (n: ℕ), n =ₙₐₜ n
```

#### Step 4: Universal — bundling type + equality

Prove that equality is reflexive, symmetric, and transitive (from the impurifier equations + induction), then bundle as a Universal:

```lean
def NaturalNumbersUniversal: Universal := {
  Particular := ℕ
  eq := { pred := eq, refl := ..., sym := ..., trans := ... }
}
```

#### Step 5: Operations and predicates on the Universal

Operations and predicates follow the same axiom + axiom_def + congruence pattern:

1. **Axiom** — declare the signature
2. **Axiom definition** — specify behavior (typically an iff, with the operation being defined on the left side)
3. **Congruence** — prove it respects equality (proof unfolds the axiom_def)
4. **Bundle** — wrap as a `CongruentPredicate` or `CongruentOperation` (any arity)

Since we use custom equality (not Leibniz), every predicate and operation must be proven congruent — without this, it is not well-defined. Use `let` bindings with explicit types for `pred` and `cong` before the structure literal.

Example (unary predicate on sets):

```lean
-- 1. Axiom
axiom is_singleton: Set U → Prop
-- 2. Axiom definition
axiom is_singleton_def: ∀ (S: Set U),
  is_singleton S ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S
-- 3 + 4. Congruence proof + bundle
def singleton_predicate: CongruentUnaryPredicate (𝐒𝐞𝐭 U) :=
  let pred: Set U → Prop := (S: Set U ↦ is_singleton S)
  let cong: ... := by forall_intro ...  -- unfolds is_singleton_def in proof
  { pred := pred, cong := cong }
```

See `Universals/NaturalNumbers/Particular.lean` for the canonical postulated type example, and `Universals/Sets/Particular.lean` for the canonical derived type example.

## Namespace and Import Conventions

### Standard Preamble

Each Universal's files follow the same preamble pattern. Example for Sets:

```lean
import Universe
import Logic
import Universals.Sets.Universal

namespace Universe
namespace Sets
open Logic
open Logic.PC₁

-- ... definitions ...

end Sets
end Universe
```

For another Universal (e.g., NaturalNumbers), replace `Sets` accordingly throughout.

### When to Import

- Import only what's needed
- Use barrel imports when you need multiple items from a category
- Direct imports for specific files when only one item is needed

## Comments

### Deviation from Established Foundations

When a construction deviates from established mathematical foundations (ZFC, type theory, category theory, etc.), add a comment explaining what the standard approach is and why ours differs. This project frequently diverges from tradition — these comments are essential for understanding the choices.

Examples:

```lean
-- In ZFC, the Powerset Axiom must be postulated: "∀A ∃P ∀B (B ∈ P ↔ B ⊆ A)".
-- Our predicate-based approach avoids this...

-- Unlike standard type theory where functions are primitive, here functions
-- are derived as congruent operations between Universals...
```

### FOL Equivalence Comments

A core goal of this project is to stay within first-order logic. Some structures (like sets) are derived from logic; others (like natural numbers) are postulated as initial objects, ADT-style, within typed FOL. In both cases, everything must be expressible in FOL. When we use Lean constructs or idioms (subtypes, type classes, polymorphism, etc.) that may appear to go beyond FOL, we must clarify that they are syntactic sugar over FOL statements.

Always add a comment showing the FOL equivalent:

```lean
-- This is syntactic sugar over FOL. We are NOT leaving FOL behind.
-- ∀ x : (set_as_universal S).Particular, Q(x)  ≡  ∀ x : U.Particular, x ∈ S → Q(x)

-- Polymorphic =ₛₑₜ at any level is syntactic sugar — Lean infers the correct
-- universal and expands to the specific first-order equality for that level.
```

### Authorship Comments

Claude-written proofs get an authorship comment:

```lean
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
theorem name: ... := by forall_intro
```

## User Preferences

- **Minimalism**: Don't add unnecessary abstractions, features, or files
- **Explicit over implicit**: Prefer clarity over cleverness
- **No Lean automation**: The whole point is explicit FOL proofs
- **Don't repeat failed edits**: If an edit is rejected, STOP and wait for guidance
- **Ask before acting**: When uncertain, ask rather than guess
- **Don't say "likely"**: If you can read the code, read it — don't speculate

## Pitfalls

- **U is auto-bound**: When `U` appears free in a definition, Lean auto-binds it as an implicit parameter. This is polymorphic, not a fixed constant.
- **`variable {U : Universal}`**: Use this when type class instances need U to be explicitly bound (rare — needed for Coe instances).
- **Barrel files must be updated**: When adding a new file, always add the import to the parent barrel file.
- **`noncomputable` for axiom bundles**: Definitions that wrap axioms into structures need this keyword.
- **Check existing patterns**: Before creating anything new, read existing similar code to match the established style.

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
