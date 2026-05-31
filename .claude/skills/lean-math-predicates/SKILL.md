---
name: lean-math-predicates
description: This skill should be used when declaring predicates, proving congruence, or working with the auto-congruence machinery in the lean-math project. It covers the macro-generated named predicates (`unary_predicate`, `binary_predicate`), their relationship with `CongruentUnaryPredicate`/`CongruentBinaryPredicate`, the `extends` chain and `CoeHead` upcast, the fiber preservation theorems, the `CongruentUnary`/`CongruentBinary` typeclass machinery, and the named-argument pattern needed at use sites where Lean can't resolve implicit arguments for coercion.
---

# Lean-Math Predicates

The project distinguishes two layers of predicate-shaped abstractions, deliberately:

1. **Congruent predicates** — `CongruentUnaryPredicate U`, `CongruentBinaryPredicate U₁ U₂` (and `CongruentTernaryPredicate ...`). These are *records carrying congruence evidence*. Used by framework machinery (e.g. `↾` refined-universal operator, fiber theorems). Transparent: any `pred + cong` can be built directly.

2. **Named predicates** — `UnaryPredicate U body`, `BinaryPredicate U₁ U₂ body`. These extend the corresponding `Congruent*Predicate` and add:
   - A `body` parameter in the *type* (records the symbol's meaning at the type level)
   - A `.def` field — the propositional bridge `pred x ↔ body x`
   - An opaque symbol `<name>_sym` (an `axiom`) so the predicate doesn't reduce to its definition

Use the named layer when introducing a mathematical concept (`mem`, `inclusion`, `is_singleton`, `is_reflexive`, etc.). Use the congruent layer when *deriving* a predicate from existing ones (fibers, restrictions, projections, etc.).

## The macros — `unary_predicate` and `binary_predicate`

Single-line declaration of a named predicate. Files:
- `Logic/PredicateCalculus/Definitions/Predicates/Unary/Definition.lean`
- `Logic/PredicateCalculus/Definitions/Predicates/Binary/Definition.lean`

```lean
-- Explicit congruence proof:
unary_predicate is_singleton : (S : (𝐒𝐞𝐭 U).Particular ↦ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S)
  with is_singleton_cong

binary_predicate mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ S.pred x)
  with mem_cong

-- Auto-inferred congruence (via [CongruentUnary] / [CongruentBinary] typeclass):
unary_predicate is_trivial : (S : (𝐒𝐞𝐭 U).Particular ↦ ∀ x, S.pred x)
```

The macro generates **three** declarations from one line:

| Generated | Kind | What it is |
|-----------|------|------------|
| `<name>_sym` | `axiom` | The opaque predicate symbol, type `T → Prop` (or `T₁ → T₂ → Prop`) |
| `<name>_def` | `axiom` | The propositional bridge: `∀ args, <name>_sym args ↔ body args` |
| `<name>` | `noncomputable def` | The `UnaryPredicate U body` / `BinaryPredicate U₁ U₂ body` value bundling `pred := <name>_sym`, `def := <name>_def`, and `cong := ...` |

After declaration, the following are available:

| Access | What you get |
|--------|--------------|
| `<name> args` | Apply the predicate (via CoeFun on the structure) |
| `<name>.pred` | The `<name>_sym` opaque symbol (as a struct field) |
| `<name>.def`  | The propositional bridge `<name>_sym args ↔ body args` (struct field) |
| `<name>.cong` | The derived combined congruence |
| `<name>_def`  | The raw axiom (same content as `.def`) |
| `<name>_sym`  | The raw opaque symbol |

**Binder order in the macro determines `<name>_def`'s argument order.** E.g., `binary_predicate mem : (x : ..., S : ... ↦ S.pred x)` produces `mem_def : ∀ x S, mem.pred x S ↔ S.pred x`. Downstream `forall_elim mem.def, ...` must respect this order — use multi-arg form `forall_elim mem.def, u, A`.

## The `<pred>_cong` convention

When using `with`, the convention is:

- **The cong theorem lives in the same file as the predicate**, named `<pred>_cong`.
- Its shape is exactly the combined cong on the *body* (not on `<name>_sym`).
- The macro adapts it to the structure's cong field via `propositional_equivalence_preserves_congruence` / `propositional_equivalence_preserves_binary_congruence`.

```lean
-- In Sets/Predicates/Binary/Membership/Predicate.lean:
theorem mem_cong:
    ∀ (x₁ x₂ : U.Particular), ∀ (S₁ S₂ : Set U),
      x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (S₁.pred x₁ ↔ S₂.pred x₂) := by ...

binary_predicate mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ S.pred x) with mem_cong
```

**For variants** (e.g. `not_mem`), import the base predicate's cong file and derive via simpler operations:

```lean
-- In NonMembership/Predicate.lean
import Universals.Sets.Predicates.Binary.Membership.Predicate

theorem not_mem_cong:
    ∀ ..., (¬S₁.pred x₁ ↔ ¬S₂.pred x₂) := by ...   -- uses mem_cong + iff_contrapositiveness

binary_predicate not_mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ ¬(S.pred x)) with not_mem_cong
```

One-way dependency: variant → base.

## The auto-cong machinery (`without with`)

The `with cong` clause is **optional**. When omitted, the macro derives the cong automatically via the `CongruentUnary` / `CongruentBinary` typeclasses:

```lean
class CongruentUnary (U: Universal) (P: U.Particular → Prop) where
  cong: ∀ x y, x =₍U₎ y → (P x ↔ P y)

class CongruentBinary (U₁: Universal) (U₂: Universal) (P: U₁.Particular → U₂.Particular → Prop) where
  inner_cong: ∀ x y₁ y₂, y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂)
  outer_cong: ∀ x₁ x₂ z, x₁ =₍U₁₎ x₂ → (P x₁ z ↔ P x₂ z)
```

When `with` is omitted, the macro calls `(inferInstance : CongruentUnary _ _).cong` (or the binary equivalent). Lean's typeclass resolution chases instances built from atomic congruence facts (conjunction, disjunction, negation, existential, universal, equality, fiber projection, etc.). If the body fits, no manual cong needed.

**When auto-derivation succeeds**: bodies built from `∧`, `∨`, `→`, `¬`, `∃`, `∀`, atomic `=₍U₎`, and applications of already-congruent predicates (via the `congruent_pred` bridge).

**When auto-derivation fails**: bodies that mention non-generic facts — typically *Universal-specific* operations. The canonical example is the "varying-a-Set" gap (see below).

## The "varying-a-Set" gap

For body `fun S => S.pred x` (fix `x`, vary the Set), no auto-cong rule fires. The fact "S₁ =ₛₑₜ S₂ ⇒ ∀ x, S₁.pred x ↔ S₂.pred x" is `Sets.eq_def` — Sets-specific knowledge that the generic auto-cong machinery doesn't (and shouldn't) know. **We do not add Universal-specific facts as auto-cong instances** — user principle: "no machinery for specific universals."

Every predicate body that varies-a-Set (`mem`, `not_mem`, `inclusion`, `is_singleton`, ...) needs explicit `with <name>_cong`, with the cong proven manually using `Sets.eq_def` + `S.cong`. Same applies to any other Universal whose equality requires unfolding to expose congruence in inner positions.

## `UnaryPredicate` extends `CongruentUnaryPredicate` — the upcast

`UnaryPredicate U body extends CongruentUnaryPredicate U where def := ...` and the binary equivalent. Lean's `extends`:

- **Generates** the projection method `UnaryPredicate.toCongruentUnaryPredicate` (data).
- **Gives** field inheritance — `is_singleton.pred`, `is_singleton.cong` work directly.
- **Does NOT install** any `Coe` instance for the upcast. We wire that up explicitly.

### The right `Coe` variant: `CoeHead`

When a structure extends another **and adds type parameters absent from the parent**, plain `Coe (Child) (Parent)` cannot be registered — Lean's `Coe α β` has `α : semiOutParam`, requiring α to be uniquely determinable from β. Our `body` parameter is in the child but not the parent, so the check fails with `instance does not provide concrete values for (semi-)out-params`.

The correct class is `CoeHead`, where the *target* is the `semiOutParam`. This is the same idiom Lean's stdlib uses for `Subtype`:

```lean
-- Lean stdlib:
@[reducible] instance : CoeHead (Subtype p) α where coe v := v.val

-- Our framework (in Schemas/Predicates/{Unary,Binary}/Schema.lean):
instance {U body} : CoeHead (UnaryPredicate U body) (CongruentUnaryPredicate U) where
  coe P := P.toCongruentUnaryPredicate

instance {U₁ U₂ body} : CoeHead (BinaryPredicate U₁ U₂ body) (CongruentBinaryPredicate U₁ U₂) where
  coe P := P.toCongruentBinaryPredicate
```

**Diagnostic rule**: if a `Coe` declaration fails the semiOutParam check, the answer is to pick the right `Coe` variant for the structural shape — *not* to redesign the type. `CoeHead` when the child carries extra type parameters; `Coe` when source/target have the same parameters.

## Use-site implicit-arg metavar problem

Even with `CoeHead` registered, coercion does **not** fire automatically when the source value has unresolved implicit arguments. Concrete example:

```lean
-- is_singleton : {U : Universal} → UnaryPredicate (𝐒𝐞𝐭 U) body₀
-- Use site:
(𝐒𝐞𝐭 U) ↾ is_singleton    -- FAILS
-- Lean sees `is_singleton : UnaryPredicate (𝐒𝐞𝐭 ?V) ?body` (with metavars).
-- The CoeHead lookup doesn't propagate the target's U back to ?V.
```

**Fix**: provide enough information at the call site to make Lean's elaborator pin the implicit args. Use **named-argument syntax** (NOT `@`-prefix unless absolutely needed):

```lean
(𝐒𝐞𝐭 U) ↾ (is_singleton (U := U))   -- pins is_singleton's implicit U
```

For framework functions that take a congruent predicate and have their own implicits, **specify all the implicits via named args**:

```lean
-- Inclusion/Predicate.lean — supersets_of fiber wrap:
cong := fiber_first_preserves_binary_congruence
          (U₁ := 𝐒𝐞𝐭 U) (U₂ := 𝐒𝐞𝐭 U)
          (inclusion (U := U)) A
```

### Why named args (not `@`)

| | `@f a b c`                         | `f (name := v) ...`        |
|---|------------------------------------|----------------------------|
| Brittleness | Breaks if implicit order changes | Survives reordering   |
| Verbosity   | One `@`, then positional         | One named binding per pin |
| Reader      | Have to remember positions       | Self-documenting       |
| Use         | Quick test / one-off             | Production code        |

In this codebase, **prefer named-arg form**. Reserve `@` for momentary tests during debugging.

## Fiber preservation theorems

When you have a `CongruentBinaryPredicate`, you can get a `CongruentUnaryPredicate` for either fiber via framework theorems. Located in:
- `Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/FiberFirstPreservesCongruence.lean`
- `Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/FiberSecondPreservesCongruence.lean`

```lean
theorem fiber_first_preserves_binary_congruence
    {U₁ U₂} (P: CongruentBinaryPredicate U₁ U₂) (x: U₁.Particular):
    ∀ y₁ y₂, y₁ =₍U₂₎ y₂ → (P.pred x y₁ ↔ P.pred x y₂)

theorem fiber_second_preserves_binary_congruence
    {U₁ U₂} (P: CongruentBinaryPredicate U₁ U₂) (y: U₂.Particular):
    ∀ x₁ x₂, x₁ =₍U₁₎ x₂ → (P.pred x₁ y ↔ P.pred x₂ y)
```

Each comes with a typeclass instance (`fiber_first_binary_congruent_unary`, `fiber_second_binary_congruent_unary`) so auto-cong picks fibers up automatically.

**Naming**: the `_binary_` suffix disambiguates from the ternary versions (`fiber_first_preserves_congruence` in Ternary properties). Convention: when the same theorem shape exists at multiple arities and lives in the same `Logic.PC₁` namespace, the binary version gets `_binary_` (matching `propositional_equivalence_preserves_congruence` vs `propositional_equivalence_preserves_binary_congruence`).

### Use case: fiber-extraction in a `def`

When a named binary predicate `inclusion` has fibers that are themselves meaningful concepts (`supersets_of A`, `subsets_of A`), declare them as thin `def`s wrapping the fiber theorem — **don't** re-prove cong:

```lean
def supersets_of (A: Set U) : CongruentUnaryPredicate (𝐒𝐞𝐭 U) :=
  { pred := (S : Set U ↦ inclusion A S)
    cong := fiber_first_preserves_binary_congruence
              (U₁ := 𝐒𝐞𝐭 U) (U₂ := 𝐒𝐞𝐭 U)
              (inclusion (U := U)) A }
```

This introduces **no new opacity** — it's pure packaging. The opaque symbol is `inclusion`; `supersets_of A` is a transparent derived CUP. Useful when the fiber concept has its own mathematical name; skip otherwise and call the fiber theorem inline at the use site.

## Common pitfalls

- **`mem.def` arg order**: macro binder order determines `<name>_def`'s arg order. `binary_predicate mem : (x, S ↦ ...)` gives `mem.def : ∀ x S, ...`, so `forall_elim mem.def, u, A` (NOT `, A, u`).

- **Don't introduce Universal-specific auto-cong instances.** Generic machinery only; Universal-specific facts (`Sets.eq_def`, `Dyads.eq_def`, etc.) are used in *manual* `<name>_cong` proofs, not registered as instances.

- **Auto-cong on `=₍U₎` bodies is currently broken.** `equal_to`/`equal_from` instances were deleted in the Equals refactor. Bodies with `a =₍U₎ x` shape need explicit `with`.

- **`noncomputable` required**: the macro generates `noncomputable def <name>` because it depends on axioms. Consumers that build something on top of a named predicate (e.g. `SingletonSetUniversal := (𝐒𝐞𝐭 U) ↾ is_singleton`) must also be marked `noncomputable`.

- **Don't write `protected pred`** on `CongruentUnaryPredicate`/`BinaryPredicate`. Lean's `protected` only blocks `open`-based unqualified access; dot notation `S.pred x` still works. Doesn't give the opacity it appears to.

## Related conventions

- For naming, file organization, and statement template syntax `(x : T ↦ body)`: see **lean-math-conventions**.
- For ND tactics used inside `<pred>_cong` proofs (`forall_intro`, `forall_elim`, `PC₀.deductive_eq_l2r`, etc.): see **lean-math-proofs**.
- For the Sets universal's equality (`=ₛₑₜ`, `eq_def`, `set_extensionality`): see **lean-math-sets**.

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
