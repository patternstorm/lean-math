---
name: lean-math-predicates
description: This skill should be used when declaring predicates, proving congruence, or working with the auto-congruence machinery in the lean-math project. It covers the three-tier congruence architecture (foundational named predicates with manual Universal-specific cong, derived named predicates with macro-auto-derived cong, and compound un-named predicates with on-demand auto-cong), the macro-generated named predicates (`unary_predicate`, `binary_predicate`), their relationship with `CongruentUnaryPredicate`/`CongruentBinaryPredicate`, the `extends` chain and `CoeHead` upcast, the fiber preservation theorems, the `CongruentUnary`/`CongruentBinary` typeclass machinery, and the named-argument pattern needed at use sites where Lean can't resolve implicit arguments for coercion.
---

# Lean-Math Predicates

The project distinguishes two layers of predicate-shaped abstractions, deliberately:

1. **Congruent predicates** — `CongruentUnaryPredicate U`, `CongruentBinaryPredicate U₁ U₂` (and `CongruentTernaryPredicate ...`). These are *records carrying congruence evidence*. Used by framework machinery (e.g. `↾` refined-universal operator, fiber theorems). Transparent: any `pred + cong` can be built directly.

2. **Named predicates** — `UnaryPredicate U body`, `BinaryPredicate U₁ U₂ body`. These extend the corresponding `Congruent*Predicate` and add:
   - A `body` parameter in the *type* (records the symbol's meaning at the type level)
   - A `.def` field — the propositional bridge `pred x ↔ body x`
   - An opaque symbol `<name>_sym` (an `axiom`) so the predicate doesn't reduce to its definition

Use the named layer when introducing a mathematical concept (`mem`, `inclusion`, `is_singleton`, `is_reflexive`, etc.). Use the congruent layer when *deriving* a predicate from existing ones (fibers, restrictions, projections, etc.).

## Where congruence work lives — the three tiers

Congruence is the framework's heaviest soundness obligation. The architecture localizes it to **exactly the layer where new opacity is introduced**, and beyond that point, makes it structural and free. There are three tiers:

**Tier 1 — Foundational named predicates** (`mem`, `inclusion`, `equals`, eventually `addition`, `succ`, etc.). Manual cong is **unavoidable**: the reasoning is Universal-specific. For example, `mem.cong` must unfold `Sets.eq_def` (the pointwise-equivalence characterization of `=ₛₑₜ`) — a Sets-specific fact the generic auto-cong machinery does not, and should not, know. This is the "varying-a-Set" gap (see the dedicated section below). Use the macro's **Form 3** (`with cong : ... := ...`) to discharge cong manually.

**Tier 2 — Derived named predicates** built compositionally from existing congruent things (e.g., `is_trivial : (S ↦ ∀ x, S.pred x)`). The macro **auto-derives cong** via the `CongruentUnary` / `CongruentBinary` typeclass machinery — no manual proof needed. Use **Form 1** (no `with` clause). The macro synthesizes cong from the body's connectives and transports it onto the opaque symbol via `propositional_equivalence_preserves_congruence`.

**Tier 3 — Compound (un-named) predicates** built from existing congruent things, used **transiently** without introducing a new symbol (e.g., the graph predicates of operations like `powerset_graph_pred`, `union_graph_pred`). Just a `@[reducible] def` — no macro, no symbol, no cong field. Cong is synthesised **on demand** at the use site via `CoeDep` to a `CongruentBinaryPredicate` / `CongruentTernaryPredicate`. See `lean-math-operations` for the canonical use case (`<Arity>OperationGraph.fromCongPred`).

**The architectural principle**: cong work is **bounded by new opacity introductions**. Tier 1 is the irreducible minimum — every primitive symbol must carry its Universal-specific congruence evidence, because primitiveness means the cong fact cannot be derived from structure. Tier 2 and Tier 3 are free, because once a predicate is congruent, composing it with the connectives the framework knows is automatic — that machinery (one file per connective in `Schemas/CongruentPredicates/Unary/Properties/`) is proven once and forever.

## The macros — `unary_predicate` and `binary_predicate`

Single-line declaration of a named predicate. Files:
- `Logic/PredicateCalculus/Definitions/Predicates/Unary/Definition.lean`
- `Logic/PredicateCalculus/Definitions/Predicates/Binary/Definition.lean`

Each macro supports **three forms**, differing only in how congruence is supplied:

```lean
-- Form 1: Auto-derived congruence (the macro infers cong via the typeclass machinery).
--         Use when the body is built from generic auto-cong-capable connectives.
unary_predicate is_trivial : (S : (𝐒𝐞𝐭 U).Particular ↦ ∀ x, S.pred x)

-- Form 2: External congruence reference. The cong theorem is declared in
--         ANOTHER file and referenced by name.
binary_predicate not_mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ ¬(S.pred x))
  with shared_neg_cong

-- Form 3: Inline congruence. The cong type and proof are attached directly
--         to the predicate via `with cong : <type> := <proof>`. This is the
--         default form when the cong proof is local to this file.
binary_predicate mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ S.pred x)
  with cong :
    ∀ (x₁ x₂ : U.Particular), ∀ (S₁ S₂ : Set U),
      x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (S₁.pred x₁ ↔ S₂.pred x₂) := by
    forall_intro
    -- ...full ND proof body...
```

The macro generates **three** declarations from one line (and a fourth in the inline form):

| Generated | Kind | What it is |
|-----------|------|------------|
| `<name>_sym` | `axiom` | The opaque predicate symbol, type `T → Prop` (or `T₁ → T₂ → Prop`) |
| `<name>_def` | `axiom` | The propositional bridge: `∀ args, <name>_sym args ↔ body args` |
| `<name>` | `noncomputable def` | The `UnaryPredicate U body` / `BinaryPredicate U₁ U₂ body` value bundling `pred := <name>_sym`, `def := <name>_def`, and `cong := ...` |
| `<name>_cong` *(inline form only)* | `theorem` | The body cong proof, declared as a public top-level theorem (accessible to other files) |

After declaration, the following are available regardless of form:

| Access | What you get |
|--------|--------------|
| `<name> args` | Apply the predicate (via CoeFun on the structure) |
| `<name>.pred` | The `<name>_sym` opaque symbol (as a struct field) |
| `<name>.def`  | The propositional bridge `<name>_sym args ↔ body args` (struct field) |
| `<name>.cong` | The derived combined congruence |
| `<name>_def`  | The raw axiom (same content as `.def`) |
| `<name>_sym`  | The raw opaque symbol |

**Binder order in the macro determines `<name>_def`'s argument order.** E.g., `binary_predicate mem : (x : ..., S : ... ↦ S.pred x)` produces `mem_def : ∀ x S, mem.pred x S ↔ S.pred x`. Downstream `forall_elim mem.def, ...` must respect this order — use multi-arg form `forall_elim mem.def, u, A`.

## Which form to use — the rule

| Situation | Tier | Form | Example |
|-----------|------|------|---------|
| Body fits generic auto-cong (no Universal-specific facts) — derived named predicate | 2 | Form 1 (no `with`) | `unary_predicate is_trivial : (S ↦ ∀ x, S.pred x)` |
| **Cong proof Universal-specific (foundational named predicate)** | **1** | **Form 3 (inline `with cong : ... := ...`)** | `binary_predicate mem : (...) with cong : ... := ...` |
| Cong proof declared in another file and reused | 1 | Form 2 (external `with <name>`) | `binary_predicate foo : (...) with shared_cong` |

**The default for non-auto-cong predicates is Form 3 (inline).** Reasons:

1. **Readability** — the predicate name and body are read first, not after 30-50 lines of proof. The cong type and proof come after, attached to the predicate they belong to.
2. **Locality** — the cong is structurally bound to the predicate it certifies; you don't have to jump elsewhere to find it.
3. **Still public** — the inline form auto-generates `<name>_cong` as a public top-level theorem, so other files can still reference it the same way they would with Form 2.

**Form 2 (external) is reserved for** genuinely reused cong proofs that live in a separate file — e.g., when one cong theorem certifies multiple predicate variants and lives in its own helper file.

### Worked example: inline form (Form 3)

```lean
-- In Sets/Predicates/Binary/Membership/Predicate.lean:
binary_predicate mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ S.pred x)
  with cong :
    ∀ (x₁: U.Particular), ∀ (x₂: U.Particular), ∀ (S₁: Set U), ∀ (S₂: Set U),
      x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (S₁.pred x₁ ↔ S₂.pred x₂) := by forall_intro
    variable(x₁: U.Particular)
    -- ...full ND proof...
    iterate h₁₂
```

The macro generates `mem_sym`, `mem_def`, `mem_cong` (public theorem), and the `mem` struct value. `mem.cong`, `mem.def`, `mem.pred` all work as expected, and `mem_cong` is accessible from other files (e.g., NonMembership reaches in via `import` to derive `not_mem_cong`).

### Worked example: variant deriving from another file's cong

`not_mem`'s cong is derived from `mem_cong` via the contrapositive. Even though the *derivation* uses an imported theorem (`mem_cong`), the `not_mem_cong` proof itself lives in the same file as `not_mem` — so it still uses Form 3:

```lean
-- In NonMembership/Predicate.lean
import Universals.Sets.Predicates.Binary.Membership.Predicate

binary_predicate not_mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ ¬(S.pred x))
  with cong :
    ∀ (x₁: U.Particular), ∀ (x₂: U.Particular), ∀ (S₁: Set U), ∀ (S₂: Set U),
      x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (¬S₁.pred x₁ ↔ ¬S₂.pred x₂) := by forall_intro
    -- ...derives by applying `mem_cong` + `PC₀.iff_contrapositiveness`...
```

One-way dependency: variant → base. The variant's proof imports and references the base's `<name>_cong` theorem; the macro still generates the variant's own public `not_mem_cong` from the inline block.

### When you would use Form 2 (external)

If `not_mem_cong` and (hypothetically) `not_subset_cong` both had identical proof bodies modulo renaming, you might extract a generic `negated_set_predicate_cong` lemma into a separate helper file and reference it from both predicate declarations via Form 2:

```lean
-- Helper file: GenericCongs.lean
theorem negated_set_predicate_cong (P : ...) : ... := ...

-- Predicate file:
import GenericCongs

binary_predicate not_mem : (...) with (negated_set_predicate_cong mem)
```

This is the kind of scenario Form 2 is reserved for.

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

Every predicate body that varies-a-Set (`mem`, `not_mem`, `inclusion`, `is_singleton`, ...) needs an explicit `with cong : ... := ...` clause (Form 3), with the cong proven manually using `Sets.eq_def` + `S.cong`. Same applies to any other Universal whose equality requires unfolding to expose congruence in inner positions.

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

- **Universal-specific equality aliases must expand through `=₍U'₎`.** The `=₍U₎` notation expands to `@equals U a b` (with `equals : CongruentBinaryPredicate U U`), so equality bodies elaborate to the `equals.pred ...` form that the standard `fiber_*_binary_congruent_unary equals` instances match — auto-cong fires uniformly, no bridge instances needed. Universal-specific aliases (`=ₛₑₜ`, `=ₙₐₜ`, ...) only work if defined to expand via `=₍U'₎` (e.g., `notation A " =ₛₑₜ " B => A =₍SetsUniversal _₎ B`). If an alias expands directly to the underlying `eq` axiom, the universe is hidden from the unifier and auto-cong cannot match — `with cong : ... := ...` is required.

- **`noncomputable` required**: the macro generates `noncomputable def <name>` because it depends on axioms. Consumers that build something on top of a named predicate (e.g. `SingletonSetUniversal := (𝐒𝐞𝐭 U) ↾ is_singleton`) must also be marked `noncomputable`.

- **Don't write `protected pred`** on `CongruentUnaryPredicate`/`BinaryPredicate`. Lean's `protected` only blocks `open`-based unqualified access; dot notation `S.pred x` still works. Doesn't give the opacity it appears to.

## Related conventions

- For naming, file organization, and statement template syntax `(x : T ↦ body)`: see **lean-math-conventions**.
- For ND tactics used inside `<pred>_cong` proofs (`forall_intro`, `forall_elim`, `PC₀.deductive_eq_l2r`, etc.): see **lean-math-proofs**.
- For the Sets universal's equality (`=ₛₑₜ`, `eq_def`, `set_extensionality`): see **lean-math-sets**.

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
