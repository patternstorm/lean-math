---
name: lean-math-operations
description: This skill should be used when defining new operations in the framework's graph-based pattern. It covers the two-layer architecture (`<Arity>OperationGraph` refining `Congruent<Arity+1>Predicate` with totality/functionality obligations, then `<Arity>Operation` introduced axiomatically by the `constant`/`unary_operation`/`binary_operation` macros on top), the `fromCongPred` smart constructor that builds the graph value without a hand-written cong proof (operation graph predicates sit in tier 3 of the three-tier congruence architecture — see `lean-math-predicates` for tiers 1 and 2), the role of the graph predicate as a `@[reducible]` def so typeclass synthesis can see through it, file organization for graph + properties + operation + derived theorems, and the curried-form rationale for binary operations (so partial application yields a framework `UnaryOperation`, not a raw Lean function).
---

# Lean-Math Operations

## The architecture and why it's shaped this way

Operations are introduced in **two layers**, with strong typing gating the axiomatic step.

**Layer 1 — the graph.** `UnaryOperationGraph U₁ U₂` extends `CongruentBinaryPredicate U₁ U₂` (and `BinaryOperationGraph U₁ U₂ U₃` extends `CongruentTernaryPredicate U₁ U₂ U₃`) with two refinement obligations:

- `ltot` — left-totality: every input has at least one output.
- `rdet` — right-determinacy: outputs are unique up to the target's equality.

The graph's `pred` and `cong` come from the parent congruent predicate; ltot and rdet certify that this predicate is **the graph of a total function**.

**Layer 2 — the operation.** `UnaryOperation U₁ U₂` (notation `U₁ ⟴ U₂`) and `BinaryOperation U₁ U₂ U₃` (notation `U₁ ⟴ U₂ ⟴ U₃`) are introduced **axiomatically** by the `unary_operation` / `binary_operation` macros on top of a graph. The macros generate:

- An opaque function symbol (axiom).
- A satisfies axiom `∀ x, graph.pred x (op x)` (arity-shaped: bare `graph.pred sym` for constants, `∀ x y, graph.pred x y (op x y)` for binary).
- A bundled value carrying the graph, the symbol, and satisfies, with `.def` (bidirectional iff `op x =₍U_target₎ y ↔ graph.pred x y`) and `.cong` as **derived** theorems in the schema namespace.

**Why this layering matters.** The satisfies axiom is consistent **only** when the graph is total and functional. By requiring an `<Arity>OperationGraph` (not a plain congruent predicate) at the macro's input, the framework forces totality and functionality to be discharged BEFORE the axiomatic symbol is introduced — no silently inconsistent operation can be declared. And by deriving `.cong` and `.def` as theorems (not assuming them as fields), both are sound by construction; a field could be supplied with the wrong proof, a derived theorem cannot.

## Auto-cong: graph predicates are auto-congruent

**Operational rule: do not write manual cong proofs for operation graph predicates.** They are auto-congruent almost always; when they aren't, the right response is to fix the framework's auto-cong machinery, not to write a per-graph cong proof.

Why this is the case: graph predicates sit in **Tier 3** of the framework's congruence architecture — they are compound, un-named, compositional. Their congruence is synthesised on demand from the body's structure over already-congruent named predicates. See `lean-math-predicates` for the three-tier story and the broader principle.

**Concretely**: the graph value construction needs no `cong` field — just the body, ltot, and rdet:

```lean
noncomputable def powerset_graph {U: Universal}: UnaryOperationGraph (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 (𝐒𝐞𝐭 U)) :=
  UnaryOperationGraph.fromCongPred
    (powerset_graph_pred (U := U) : CongruentBinaryPredicate (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 (𝐒𝐞𝐭 U)))
    (powerset_graph_left_totality (U := U))
    (powerset_graph_right_determinacy (U := U))
```

Same shape for binary via `BinaryOperationGraph.fromCongPred` with a `CongruentTernaryPredicate`.

**The mechanism**. The ascription `(<name>_graph_pred (U := U) : Congruent<Arity+1>Predicate _ _)` triggers a `CoeDep` instance that synthesizes the parent congruent predicate from the body's structure. The synthesis chain walks the connectives:

- `congruent_<n>ary_from_fibers` — derives `CongruentBinary`/`CongruentTernary` from per-arg `CongruentUnary` instances.
- `congruent_universal`, `congruent_iff`, `congruent_disjunction`, `congruent_conjunction`, `congruent_negation`, `congruent_existential`, `congruent_exists_unique`, `congruent_constant` — peel the corresponding head connective.
- `fiber_first_binary_congruent_unary`, `fiber_second_binary_congruent_unary`, `fiber_first_two_congruent_unary` — recognise a congruent predicate's fiber (e.g., `mem.pred x C` fixing `x`) as `CongruentUnary` in the remaining argument.

`UnaryOperationGraph.fromCongPred` (resp. `BinaryOperationGraph.fromCongPred`) bundles the synthesised parent with ltot and rdet into the refinement struct.

**When auto-cong fails — diagnosis path**. The body uses something the framework doesn't yet cover. Trace with `set_option trace.Meta.synthInstance true in <decl>`:

1. **Missing `@[reducible]` on the graph_pred** — trace shows synthesis attempting to match an opaque application against the connective instances.
2. **A connective lacks a `congruent_*` instance** — trace shows synthesis reaching that connective and finding no matching instance.

The fix for (2) is to **add the missing instance** to `Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/` (mirror an existing file like `DisjunctionPreservesCongruence.lean`). Do NOT work around by hand-writing a cong proof in the graph — that's a framework gap, not a per-operation problem.

**The escape hatch**. For exotic bodies that genuinely can't be auto-inferred (rare in practice), `fromCongPred` still accepts a manually-built congruent predicate value: the constructor is agnostic to how the parent congruent predicate was obtained. But you should almost never need this — graph predicates over named congruent predicates with standard connectives are auto-cong territory.

## File organization

For an operation `<name>` of arity `k` (1 for unary, 2 for binary) under Universal `<X>`:

```
Universals/<X>/
├── Predicates/<arity-k+1>/                     # the graph predicate's arity is k+1
│   ├── Definitions/<Name>GraphPredicate.lean   # the @[reducible] def for the body
│   └── <Name>Graph/
│       ├── Predicate.lean                      # `<name>_graph` (via fromCongPred)
│       └── Properties/
│           ├── LeftTotality.lean               # `<name>_graph_left_totality`
│           └── RightDeterminacy.lean           # `<name>_graph_right_determinacy`
└── Operations/<arity-k>/
    └── <Name>/
        ├── Operation.lean                      # the macro call + notation
        └── Properties/
            └── <Characterization>.lean         # old _def axiom content, now derived
```

A unary operation's graph is a **binary** predicate (the relation between input and output) → `Predicates/Binary/`. A binary operation's graph is a **ternary** predicate → `Predicates/Ternary/`. Each directory level is a Lean barrel.

**Why the graph_pred def lives in a separate `Definitions/` folder**: circular-import avoidance. The graph's `Predicate.lean` imports LeftTotality and RightDeterminacy (to populate ltot/rdet), and those import the graph_pred (their statements use it). So the graph_pred must sit above all three in the import DAG.

**Why derived-theorem files use the bare characterization name**: the path `Operations/Unary/Powerset/Properties/Membership.lean` already places it under powerset; the file is just `Membership.lean`, not `PowersetMembership.lean`. The theorem inside is `powerset_membership` (fully qualified at the term level for unambiguous downstream reference).

## Step-by-step: defining an operation

The steps are the same for unary and binary; the only differences are the arities throughout. Substitute `<n>` for the graph predicate's arity (`Binary` for unary ops, `Ternary` for binary ops) and `<m>` for the operation's own arity (`Unary` or `Binary`).

### Step 1 — define the graph predicate

`Universals/<X>/Predicates/<n>/Definitions/<Name>GraphPredicate.lean`:

```lean
@[reducible] def <name>_graph_pred {U: Universal} (...): Prop :=
  <body relating inputs to output>
```

`@[reducible]` is **mandatory**: typeclass synthesis must look INSIDE the body to dispatch on the head connective. Without it, the def stays opaque and auto-cong fails (synthesis lists candidates but none match the opaque application).

### Step 2 — prove left-totality

`Predicates/<n>/<Name>Graph/Properties/LeftTotality.lean`:

```lean
theorem <name>_graph_left_totality {U: Universal}:
    ∀ (inputs), ∃ (output), <name>_graph_pred ... := ...
```

Set-valued operations typically use a set comprehension as the witness; algebraic operations construct via existing operations or induction on the source type.

### Step 3 — prove right-determinacy

`Predicates/<n>/<Name>Graph/Properties/RightDeterminacy.lean`:

```lean
theorem <name>_graph_right_determinacy {U: Universal}:
    ∀ (inputs), ∀ (out₁ out₂),
      <name>_graph_pred ... out₁ ∧ <name>_graph_pred ... out₂ → out₁ =₍U_target₎ out₂ := ...
```

The hypothesis is **conjunctive** — this matches the structure field's shape. Set-valued operations typically route through `set_extensionality`.

### Step 4 — construct the graph value

`Predicates/<n>/<Name>Graph/Predicate.lean`:

```lean
noncomputable def <name>_graph {U: Universal}: <m>OperationGraph ... :=
  <m>OperationGraph.fromCongPred
    (<name>_graph_pred (U := U) : Congruent<n>Predicate ...)
    (<name>_graph_left_totality (U := U))
    (<name>_graph_right_determinacy (U := U))
```

**Why `(U := U)` everywhere**: Lean's elaborator does not auto-propagate the outer `U` through the constructor call into the implicit `{U: Universal}` of the theorems and the graph_pred. Each occurrence needs explicit `(U := U)`. Without it, you see errors like `Set ?m.8` — those are unbound implicit `U`s, NOT a metavariable issue with the constructor itself.

**No cong proof here.** The CoeDep on the ascribed graph_pred triggers auto-cong synthesis, which produces the parent `Congruent<n>Predicate` with its cong field, which `fromCongPred` then bundles with ltot and rdet.

### Step 5 — apply the macro

`Universals/<X>/Operations/<m>/<Name>/Operation.lean`:

```lean
unary_operation <name> : <U₁> ⟴ <U₂> from <name>_graph
-- or, for binary:
binary_operation <name> : <U₁> ⟴ <U₂> ⟴ <U₃> from <name>_graph
```

The macro's source/target universes use `term:max` precedence, so **compound universes need parentheses**: `(𝐒𝐞𝐭 U)`, not `𝐒𝐞𝐭 U`. Bare identifiers like `U` work without parens.

After declaration the macro provides:
- `<name> x` (or `<name> x y` for binary, via chained `CoeFun`) — apply.
- `<name>.graph` — the underlying graph (`.pred`, `.cong`, `.ltot`, `.rdet`).
- `<name>.satisfies` (or the raw axiom `<name>_satisfies`) — `∀ inputs, graph.pred inputs (<name> inputs)`. The most direct way to extract the characterization at the operation's output.
- `<name>.«def»` — derived defining iff `∀ inputs y, (<name> inputs =₍U_target₎ y) ↔ graph.pred inputs y`. **French quotes are required because `def` is a Lean reserved word.**
- `<name>.cong` — the derived congruence theorem.

For binary, also: `<name> x` is a real `UnaryOperation U₂ U₃` (partial application is first-class — see the curried-form rationale below).

### Step 6 — derive characterization theorems

The old-style `_def` axioms become derived theorems in `Operations/<m>/<Name>/Properties/`. The standard proof shape: apply `<name>.satisfies` (with `forall_elim` at the inputs) to extract `<name>_graph.pred inputs (<name> inputs)` directly, which unfolds (via the `@[reducible]` graph_pred) to the original characterization. Use `<name>.«def»` instead when the bidirectional iff form is what the proof needs (e.g., transferring an equality to a characterization or vice versa).

```lean
theorem powerset_membership {U: Universal}:
    ∀ (S: Set U), ∀ (S': Set U), S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S := ...
```

## Binary operations: the curried-form rationale

Binary operations follow the same pattern with one critical design choice: **the `op` field is curried** as `op : U₁.Particular → UnaryOperation U₂ U₃`, not `U₁.Particular → U₂.Particular → U₃.Particular`.

**Why**. For predicates, the natural representation IS a Lean function (`pred x` partially applied is itself a predicate). For operations, the natural representation is the STRUCTURE (graph + opaque symbol + defining axiom + derived cong). If `op` were raw-Lean-curried, then `union A` would yield just a Lean function — *not* a framework `UnaryOperation`. The curried form closes this hole: `union A : Set U ⟴ Set U` directly, with its own graph (the fiber of `union_graph` at `A` via `BinaryOperationGraph.fiber`), its own opaque symbol (`union_sym A`), and its own derived cong.

**Cong hypothesis is conjunctive** (not curried): `BinaryOperation.cong` has antecedent `x₁ =₍U₁₎ x₂ ∧ y₁ =₍U₂₎ y₂ → ...`. Consumers `and_intro` the two equalities before invoking.

## Constants: the 0-arity case

A constant `c : U` is the k=0 specialisation of the same pattern. The graph is a **unary** predicate `<name>_graph_pred : U.Particular → Prop` characterising the constant (e.g., "this set has no members"). `ConstantOperationGraph U` extends `CongruentUnaryPredicate U` with `ltot` (∃ c, pred c — left-totality collapses to bare existence at 0-arity) and `rdet` (∀ c₁ c₂, pred c₁ ∧ pred c₂ → c₁ =₍U₎ c₂ — right-determinacy collapses to uniqueness). Names match unary/binary for architectural symmetry.

The `constant` macro:

```lean
constant empty_set : 𝐒𝐞𝐭 U from empty_set_graph
```

generates `empty_set_sym : (𝐒𝐞𝐭 U).Particular` (a value, not a function), `empty_set_satisfies : empty_set_graph.pred empty_set_sym`, and `noncomputable def empty_set : ConstantOperation (𝐒𝐞𝐭 U)`.

**Use via `Coe`, not `CoeFun`.** The structure carries a `Coe (ConstantOperation U) U.Particular` instance, so `empty_set` itself behaves as the underlying particular at use sites (`x ∈ₛₑₜ empty_set` works directly). There's no `empty_set arg` form — a constant takes no arguments.

**`.cong` is derived trivially** as `op =₍U₎ op` (reflexivity) — the 0-input collapse of the cong shape used at higher arities. Kept for architectural symmetry; use sites write `empty_set.cong` instead of fishing for reflexivity. Available accessors: `empty_set.graph`, `empty_set.op`, `empty_set.satisfies`, `empty_set.«def»` (derived), `empty_set.cong` (derived).

**When to use.** Constants whose existence can be **characterized** by a predicate over already-built structure — `empty_set` and `universal_set` (via set comprehension) are the canonical fits. The framework is **not** suited to bare ADT primitives like `zero : ℕ`, which have no characterization in terms of pre-existing structure; those stay as primitive axioms in the Particular file.

## Naming conventions

| Artifact | Naming |
|----------|--------|
| Graph predicate def (`@[reducible]`) | `<name>_graph_pred` |
| Graph value | `<name>_graph` |
| Left-totality theorem | `<name>_graph_left_totality` |
| Right-determinacy theorem | `<name>_graph_right_determinacy` |
| Operation (macro-generated) | `<name>` (NOT `<name>_operation`) |
| Macro-generated symbol | `<name>_sym` |
| Macro-generated satisfies axiom | `<name>_satisfies` (or `<name>.satisfies` through the struct) |
| Derived defining iff | `<name>.«def»` (theorem in the schema namespace; no `<name>_def` top-level axiom) |
| Derived congruence | `<name>.cong` |
| Old characterization (now derived) | name describing the assertion, e.g., `<name>_membership` |
| Fiber of a binary graph | `<name>_graph.fiber x` (no `_at_first` suffix — we only ever fiber the first arg under the current curried design) |

## Common pitfalls

- **The macro requires an `<m>OperationGraph`, not a plain `Congruent<n>Predicate`.** Intentional — a plain congruent predicate would allow inconsistent operations (no totality/functionality guard).

- **Cong is NEVER a struct field of the operation.** It's the derived theorem `<Arity>Operation.cong` in the schema. Don't try to set it in the macro invocation or downstream; the macro doesn't either.

- **`@[reducible]` is mandatory on `<name>_graph_pred`.** Without it, typeclass synthesis can't see through the def, and auto-cong fails.

- **`(U := U)` on every theorem call and graph_pred ascription in the `fromCongPred` invocation.** Lean does not auto-propagate the outer `U` through the constructor call into the theorems' implicit `{U: Universal}`. Errors like `Set ?m.8` are unbound implicit `U`s.

- **Compound universes in the macro need parentheses** — `term:max` precedence: `(𝐒𝐞𝐭 U) ⟴ (𝐒𝐞𝐭 (𝐒𝐞𝐭 U))`.

- **`<name>.«def»` needs French quotes** (Lean reserved word). It's now a derived theorem in the schema namespace, not a top-level axiom — there is no `<name>_def`. Use `<name>.satisfies` when you just need `graph.pred inputs (<name> inputs)` directly; reach for `<name>.«def»` only when the bidirectional iff is what the proof needs.

- **`noncomputable`** is required on `<name>_graph` (depends on noncomputable proofs) and on the operation (axioms).

- **Use `forall_elim` for `<name>.satisfies`, `<name>.«def»`, and graph's cong** — same ND discipline as elsewhere; never term-mode application.

- **Don't hand-write the graph's cong proof**, even if it looks short. If `fromCongPred` can't synthesize, the body is using a connective without a `congruent_*` instance — fix the framework, not the operation. (Hand-writing also defeats the consistency guarantee: an inline cong proof can drift from what the body actually says.)

- **Don't try to type a binary `op` as `U₁ → U₂ → U₃`** — the curried form `U₁ → UnaryOperation U₂ U₃` is non-negotiable. Partial application must yield a framework `UnaryOperation`.

## Examples in the codebase

- **`identity`** (unary) — `Logic/PredicateCalculus/Schemas/Operations/Unary/Instances/Identity/Operation.lean`. Trivial graph (equality lifted to a `UnaryOperationGraph`). Minimal worked example.
- **`powerset`** (unary) — the canonical non-trivial unary operation. Every step: predicate def, ltot, rdet, `fromCongPred` graph construction, macro, derived membership theorem.
- **`union`** (binary) — the canonical binary operation. Same shape at arity 3 (ternary graph predicate, `BinaryOperationGraph.fromCongPred`).
- **`first_projection`** (binary, in `Test/BinaryOperation.lean`) — exercises the binary pipeline end-to-end with a trivial body; useful when adding new binary operations to sanity-check the pattern.

## Framework status

| Component | Status |
|-----------|--------|
| Unary (`UnaryOperationGraph`, `UnaryOperation` with `satisfies` + derived `.def`/`.cong`, `unary_operation` macro, `UnaryOperationGraph.fromCongPred`) | ✓ Complete |
| Binary (`BinaryOperationGraph` with `.fiber`, curried `BinaryOperation` with `satisfies` + derived `.def`/`.cong`, `binary_operation` macro, `BinaryOperationGraph.fromCongPred`) | ✓ Complete |
| Auto-cong machinery | ✓ End-to-end for `¬`, `∧`, `∨`, `↔`, `∀`, `∃`, `∃!`, constants, and binary fibers. New connectives = add a file in `Schemas/CongruentPredicates/Unary/Properties/`. |
| Constant (0-ary: `ConstantOperationGraph` with `.ltot`/`.rdet`, `ConstantOperation` with `Coe` + `satisfies` + derived `.def`/`.cong`, `constant` macro, `ConstantOperationGraph.fromCongPred`) | ✓ Complete |

## Related skills

- `lean-math-predicates` — named predicate macros, congruent predicate machinery, the `CongruentUnary`/`CongruentBinary` typeclasses powering auto-cong.
- `lean-math-proofs` — ND tactics for ltot, rdet, and characterization theorem proofs.
- `lean-math-conventions` — file organization, naming, statement-template syntax.

## Report Deviations

At the end of any operation-definition work, list deviations from this skill. These are signals for where the skill needs to evolve.
