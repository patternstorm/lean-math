---
name: lean-math-sets
description: This skill should be used when working with the Set Universal in the lean-math project. It covers how sets are defined as predicates, the Set Universal, membership, inclusion, powerset, stratification, and why ZFC axioms are unnecessary.
---

# Sets in Lean-Math

## Naming Convention

Sets follow the Universal naming pattern: **bold Unicode** for the Universal, **plain text** for the type of particulars.

| Concept | Name | Definition |
|---------|------|------------|
| Type of sets (particulars) | `Set U` | `def Set (U: Universal): Type := Particular U` |
| Set Universal | `𝐒𝐞𝐭 U` | `notation "𝐒𝐞𝐭" => SetsUniversal` |
| Type of singleton sets | `SingletonSet U` | `def SingletonSet (U: Universal): Type := (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U).Particular` |
| Singleton Set Universal | `𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U` | `notation "𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭" => SingletonSetUniversal` |

This mirrors Nat: `ℕ` (type) / `𝐍𝐚𝐭` (Universal).

**When to use which**: Use `𝐒𝐞𝐭 U` (bold, the Universal) when a Universal is expected — as argument to `CongruentUnaryPredicate`, `CongruentUnaryOperation`, `sub_universal`, `∃!₍...₎`, etc. Use `Set U` (plain, the type) for type annotations of set values.

## Sets as Predicates

Sets are NOT primitive — they are derived from predicates. A set over Universal U is a `CongruentUnaryPredicate U`: a predicate bundled with a proof it respects U's equality.

```lean
def Particular (U: Universal): Type := CongruentUnaryPredicate U
def Set (U: Universal): Type := Particular U  -- type alias
```

A set `S : Set U` has:
- `S.pred : U.Particular → Prop` — the predicate
- `S.cong` — proof the predicate respects equality

## The Set Universal

Sets over U form their own Universal `𝐒𝐞𝐭 U`:

```lean
def SetsUniversal (U: Universal): Universal := {
  Particular := Particular U    -- CongruentUnaryPredicate U
  eq := equality                -- set equality (extensional)
}
notation "𝐒𝐞𝐭" => SetsUniversal
```

**Set equality** (`=ₛₑₜ`): Two sets are equal iff their predicates are logically equivalent.

```lean
axiom eq_def: ∀ (S₁: Set U), ∀ (S₂: Set U),
  S₁ =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), S₁.pred x ↔ S₂.pred x
```

**The `=ₛₑₜ` notation is polymorphic** — it works at any level: `Set U`, `Set (𝐒𝐞𝐭 U)`, etc. Lean infers the correct universal from context. This is syntactic sugar over FOL, not a departure from it.

## Key Predicates

### Membership (`∈ₛₑₜ`)
```lean
axiom mem: U.Particular → Set U → Prop
notation:50 x:51 " ∈ₛₑₜ " S:51 => mem x S
axiom mem_def: ∀ (S: Set U), ∀ (x: U.Particular), x ∈ₛₑₜ S ↔ S.pred x
```

Membership is equivalent to predicate satisfaction.

### Inclusion (`⊆ₛₑₜ`)
```lean
axiom inclusion: Set U → Set U → Prop
notation:50 S₁:51 " ⊆ₛₑₜ " S₂:51 => inclusion S₁ S₂
axiom inclusion_def: ∀ (S₁: Set U), ∀ (S₂: Set U),
  (S₁ ⊆ₛₑₜ S₂) ↔ ∀ (x: U.Particular), (S₁.pred x → S₂.pred x)
```

### Derived Congruent Predicates

Binary (in `Predicates/Binary/`):
- **`elements_of x`**: CongruentUnaryPredicate on `𝐒𝐞𝐭 U` — "sets containing x"
- **`supersets_of A`**: CongruentUnaryPredicate on `𝐒𝐞𝐭 U` — fixes first arg of inclusion, congruent in second
- **`subsets_of A`**: CongruentUnaryPredicate on `𝐒𝐞𝐭 U` — fixes second arg of inclusion, congruent in first
- **`mem_predicate`**: CongruentBinaryPredicate U `(𝐒𝐞𝐭 U)` — full binary membership
- **`inclusion_predicate`**: CongruentBinaryPredicate `(𝐒𝐞𝐭 U)` `(𝐒𝐞𝐭 U)` — full binary inclusion

Unary (in `Predicates/Unary/`):
- **`is_singleton`**: CongruentUnaryPredicate on `𝐒𝐞𝐭 U` — "sets with exactly one element" (`∃!₍U₎ x, x ∈ₛₑₜ S`)

## Operations

### Powerset (`𝒫`)
```lean
axiom powerset: Set U → Set (𝐒𝐞𝐭 U)
prefix:max "𝒫" => powerset
axiom powerset_def: ∀ (S: Set U), ∀ (S': Set U),
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
def set_as_universal (S : Set U) : Universal := sub_universal U S
```

This is syntactic sugar over FOL:
```
∀ x : (set_as_universal S).Particular, Q(x)  ≡  ∀ x : U.Particular, x ∈ S → Q(x)
```

When using `↑x` with set-specific predicates: `↑x ∈ₛₑₜ T` (membership in another set requires `↑`).

### Singleton sub-universal (`Universals/Singleton/`)

`𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U` is the sub-universal of `𝐒𝐞𝐭 U` whose particulars are singleton sets — sets with exactly one element.

```lean
def SingletonSetUniversal (U: Universal): Universal := sub_universal (𝐒𝐞𝐭 U) singleton_predicate
notation "𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭" => SingletonSetUniversal

def SingletonSet (U: Universal): Type := (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U).Particular
```

A particular `S : SingletonSet U` bundles a set with a proof that `∃!₍U₎ (x : U.Particular), x ∈ₛₑₜ ↑S`. Use `↑S` to access the underlying `Set U`.

### Singleton constructor (`{x}ₛₑₜ`)

```lean
axiom singleton_of: U.Particular → SingletonSet U
macro "{" x:term "}ₛₑₜ" : term => `(singleton_of $x)
axiom singleton_of_def: ∀ (x: U.Particular), ∀ (y: U.Particular),
  y ∈ₛₑₜ ↑{x}ₛₑₜ ↔ y =₍U₎ x
```

Bundled as `singleton_of_operation: CongruentUnaryOperation U (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U)`. Equality in the sub-universal uses `=ₛₑₜ` on lifted values: `↑{a}ₛₑₜ =ₛₑₜ ↑{b}ₛₑₜ`.

### Singleton element extraction (`⊙`)

```lean
axiom singleton_elem: SingletonSet U → U.Particular
prefix:max "⊙" => singleton_elem
axiom singleton_elem_def: ∀ (S: SingletonSet U), ∀ (y: U.Particular),
  y =₍U₎ (⊙ S) ↔ y ∈ₛₑₜ ↑S
```

Bundled as `singleton_elem_operation: CongruentUnaryOperation (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) U`. Inverse of `{x}ₛₑₜ`: constructs an element from a singleton.

### Union (`∪ₛₑₜ`)
```lean
axiom union: Set U → Set U → Set U
infixl:65 " ∪ₛₑₜ " => union
axiom union_def: ∀ (A: Set U), ∀ (B: Set U), ∀ (x: U.Particular),
  (A ∪ₛₑₜ B).pred x ↔ A.pred x ∨ B.pred x
```

The axiom_def is at predicate level (`.pred x`), not membership level. A derived `union_mem` theorem bridges to membership:
```lean
theorem union_mem: ∀ A B x, x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B
```

Bundled as:
- `union_with A`: `CongruentUnaryOperation (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U)` — fixes A, congruent in B
- `union_operation`: `CongruentBinaryOperation (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U) (𝐒𝐞𝐭 U)` — congruent in both A and B

**No Union Axiom needed**: Like powerset, union is defined as an operation with its behavior specified. No ZFC-style existence axiom required.

## Stratification

Sets create an infinite hierarchy of levels:

- **Level 0**: `U.Particular` — base particulars
- **Level 1**: `Set U` — sets of base particulars
- **Level 2**: `Set (𝐒𝐞𝐭 U)` — sets of sets (note: inner `𝐒𝐞𝐭 U` is the Universal)
- **Level N+1**: Sets of Level N

Each level's entities become the next level's particulars. This prevents Russell's Paradox: a set always exists one level above its elements, making self-membership impossible.

**Higher-order logic for free**: Quantifying over `Set U` is syntactically first-order (typed quantification) but semantically second-order (quantifying over predicates). This continues at each level.

## Why ZFC Axioms Are Unnecessary

| ZFC Axiom | Why unnecessary |
|-----------|----------------|
| Empty Set | Derived from the always-false predicate |
| Powerset | Defined as an operation, no existence claim needed |
| Infinity | Universe exists whether finite or infinite |
| Union | Defined as an operation, no existence claim needed |
| Extensionality | Derived as a theorem from predicate equivalence |

## Pitfalls

- **`prefix:max` for notation**, not `notation`. Use `prefix:max "𝒫" => powerset` for prefix operators.
- **`=ₛₑₜ` is polymorphic** — use it at all levels instead of `=₍𝐒𝐞𝐭 (𝐒𝐞𝐭 U)₎`.
- **When defining congruent predicates**: the `cong` field must prove congruence in the "free" argument. Think carefully about which argument is fixed and which varies.
- **`supersets_of` vs `subsets_of`**: `supersets_of A` fixes A as first arg (congruent in second); `subsets_of A` fixes A as second arg (congruent in first).

## Report Deviations

At the end of the analysis, list any deviations or workarounds made from this skill specification. This helps identify where the skill needs improvement.
