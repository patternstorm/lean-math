---
name: lean-math-sets
description: This skill should be used when working with the Set Universal in the lean-math project. It covers how sets are defined as predicates, the Set Universal, membership, inclusion, powerset, stratification, and why ZFC axioms are unnecessary.
---

# Sets in Lean-Math

## Sets as Predicates

Sets are NOT primitive — they are derived from predicates. A set over Universal U is a `CongruentUnaryPredicate U`: a predicate bundled with a proof it respects U's equality.

```lean
-- Sets are congruent unary predicates
def Particular (U: Universal): Type := CongruentUnaryPredicate U
```

This means `(Set U).Particular = CongruentUnaryPredicate U`. A set S has:
- `S.pred : U.Particular → Prop` — the predicate
- `S.cong` — proof the predicate respects equality

## The Set Universal

Sets over U form their own Universal `Set U`:

```lean
def Set (U: Universal): Universal := {
  Particular := Particular U    -- CongruentUnaryPredicate U
  eq := equality                -- set equality (extensional)
}
```

**Set equality** (`=ₛₑₜ`): Two sets are equal iff their predicates are logically equivalent.

```lean
axiom eq_def: ∀ (S₁: Particular U), ∀ (S₂: Particular U),
  S₁ =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), S₁.pred x ↔ S₂.pred x
```

**The `=ₛₑₜ` notation is polymorphic** — it works at any level: `Set U`, `Set (Set U)`, etc. Lean infers the correct universal from context. This is syntactic sugar over FOL, not a departure from it.

## Key Predicates

### Membership (`∈ₛₑₜ`)
```lean
axiom mem: U.Particular → Particular U → Prop
notation:50 x:51 " ∈ₛₑₜ " S:51 => mem x S
axiom mem_def: ∀ (S: (Set U).Particular), ∀ (x: U.Particular), x ∈ₛₑₜ S ↔ S.pred x
```

Membership is equivalent to predicate satisfaction.

### Inclusion (`⊆ₛₑₜ`)
```lean
axiom inclusion: (Set U).Particular → (Set U).Particular → Prop
notation:50 S₁:51 " ⊆ₛₑₜ " S₂:51 => inclusion S₁ S₂
axiom inclusion_def: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular),
  (S₁ ⊆ₛₑₜ S₂) ↔ ∀ (x: U.Particular), (S₁.pred x → S₂.pred x)
```

### Derived Congruent Predicates

Binary (in `Predicates/Binary/`):
- **`elements_of x`**: CongruentUnaryPredicate on Set U — "sets containing x"
- **`supersets_of A`**: CongruentUnaryPredicate on Set U — fixes first arg of inclusion, congruent in second
- **`subsets_of A`**: CongruentUnaryPredicate on Set U — fixes second arg of inclusion, congruent in first
- **`mem_predicate`**: CongruentBinaryPredicate U (Set U) — full binary membership
- **`inclusion_predicate`**: CongruentBinaryPredicate (Set U) (Set U) — full binary inclusion

Unary (in `Predicates/Unary/`):
- **`is_singleton`**: CongruentUnaryPredicate on Set U — "sets with exactly one element" (`∃!₍U₎ x, x ∈ₛₑₜ S`)

## Operations

### Powerset (`𝒫`)
```lean
axiom powerset: (Set U).Particular → (Set (Set U)).Particular
prefix:max "𝒫" => powerset
axiom powerset_def: ∀ (S: (Set U).Particular), ∀ (S': (Set U).Particular),
  S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S
```

**No Powerset Axiom needed**: In ZFC, the Powerset Axiom asserts existence. Here, we define powerset as an operation and specify its behavior. The predicate `S' ↦ S' ⊆ₛₑₜ S` is well-formed, so no existence axiom is required.

### Constants
- **Empty Set**: Defined via the always-false predicate
- **Universal Set**: Defined via the always-true predicate

## Sub-Universals of Set

Sets can induce sub-universals in two ways. See the **lean-math-overview** skill for full sub-universal and `↑` notation documentation.

### Any set as a sub-universal

A set S induces a sub-universal of U via `set_as_universal`:

```lean
def set_as_universal (S : (Set U).Particular) : Universal := sub_universal U S
```

This is syntactic sugar over FOL:
```
∀ x : (set_as_universal S).Particular, Q(x)  ≡  ∀ x : U.Particular, x ∈ S → Q(x)
```

When using `↑x` with set-specific predicates: `↑x ∈ₛₑₜ T` (membership in another set requires `↑`).

### Singleton sub-universal (`Universals/Singleton/`)

`SingletonSet U` is the sub-universal of `Set U` whose particulars are singleton sets — sets with exactly one element.

```lean
def SingletonSet (U: Universal): Universal := sub_universal (Set U) singleton_predicate
```

A particular `S : (SingletonSet U).Particular` bundles a set with a proof that `∃!₍U₎ (x : U.Particular), x ∈ₛₑₜ ↑S`. Use `↑S` to access the underlying `(Set U).Particular`.

### Singleton constructor (`{x}ₛₑₜ`)

```lean
axiom singleton_of: U.Particular → (SingletonSet U).Particular
macro "{" x:term "}ₛₑₜ" : term => `(singleton_of $x)
axiom singleton_of_def: ∀ (x: U.Particular), ∀ (y: U.Particular),
  y ∈ₛₑₜ ↑{x}ₛₑₜ ↔ y =₍U₎ x
```

Bundled as `singleton_of_operation: CongruentUnaryOperation U (SingletonSet U)`. Equality in the sub-universal uses `=ₛₑₜ` on lifted values: `↑{a}ₛₑₜ =ₛₑₜ ↑{b}ₛₑₜ`.

## Stratification

Sets create an infinite hierarchy of levels:

- **Level 0**: `U.Particular` — base particulars
- **Level 1**: `(Set U).Particular` — sets of base particulars
- **Level 2**: `(Set (Set U)).Particular` — sets of sets
- **Level N+1**: Sets of Level N

Each level's entities become the next level's particulars. This prevents Russell's Paradox: a set always exists one level above its elements, making self-membership impossible.

**Higher-order logic for free**: Quantifying over `Set U` is syntactically first-order (typed quantification) but semantically second-order (quantifying over predicates). This continues at each level.

## Why ZFC Axioms Are Unnecessary

| ZFC Axiom | Why unnecessary |
|-----------|----------------|
| Empty Set | Derived from the always-false predicate |
| Powerset | Defined as an operation, no existence claim needed |
| Infinity | Universe exists whether finite or infinite |
| Extensionality | Derived as a theorem from predicate equivalence |

## Pitfalls

- **`prefix:max` for notation**, not `notation`. Use `prefix:max "𝒫" => powerset` for prefix operators.
- **`=ₛₑₜ` is polymorphic** — use it at all levels instead of `=₍Set (Set U)₎`.
- **When defining congruent predicates**: the `cong` field must prove congruence in the "free" argument. Think carefully about which argument is fixed and which varies.
- **`supersets_of` vs `subsets_of`**: `supersets_of A` fixes A as first arg (congruent in second); `subsets_of A` fixes A as second arg (congruent in first).

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
