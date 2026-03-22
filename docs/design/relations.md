# Relations

## Induction Hierarchy

Unary predicates classify particulars. Those classifications are what we call **sets**.

Predicates of higher arity also classify particulars — by acknowledging that in the universe there are not only individuals but that they also stand in relation to each other. The relatedness between two individuals is what a dyad, another type of particular, represents. Therefore predicates of arity > 1 also induce sets: sets of dyads. In addition to this, predicates of arity > 1 also induce **correspondences** — classifications indexed by individuals of the universe. Where unary predicates create uni-dimensional classifications (sets), higher-arity predicates create multi-dimensional ones (correspondences).

**Correspondences stand to relations as sets stand to predicates.**

| | Unary Predicates | Higher-Arity Predicates |
|---|---|---|
| Classifies | individuals of U | dyads of U₁ and U₂ |
| Induces | a set (the extension) | correspondences (indexed classifications) |
| Induced entity | particular of `𝐒𝐞𝐭 U` | particular of `𝐂𝐨𝐫𝐫 U₁ U₂` |

The two primitive entity types in the framework are parallel in ADT structure but represent different concepts:

| | Dyad `a ⋈ b` | Arrow `a ⟶ b` |
|---|---|---|
| Represents | co-existence (undirected) | production (directed) |
| Built from | two particulars of any universals | two particulars of any universals |
| ADT | `Dyad U₁ U₂` | `Arrow U₁ U₂` |
| Used by | Relations = sets of dyads | Correspondences = sets of `Arrow U₁ (𝐒𝐞𝐭 U₂)` |

A dyad asserts the co-existence of two individuals — they stand together, with no preferred direction. An arrow asserts production — from the particular on the left, I can produce the particular on the right. Both are general: they exist between any two universals.

The natural way to select arrows is through relations, via the correspondences they induce. Those correspondences happen to select arrows between universals and sets of universals — `Arrow U₁ (𝐒𝐞𝐭 U₂)`. A correspondence selects from the Arrow Universal, just as a relation selects from the Dyad Universal.

From `R: Rel U₁ U₂`, two correspondences are induced — one for each side from which to read the relation:
- `l2r R : Corr U₁ U₂` — a particular
- `r2l R : Corr U₂ U₁` — a particular

These are not arbitrary constructions layered on top. They are the two ways the relation organizes the universe once you choose a side from which to read it. `l2r` and `r2l` are projections: they expose one directed classificatory aspect of content already present in the relation, without adding new relational content.

Then correspondences, being particulars of a Universal, have their own operations:
- `apply: Corr U₁ U₂ → U₁.Particular → Set U₂`
- `comp: Corr U₁ U₂ → Corr U₂ U₃ → Corr U₁ U₃`
- `dom: Corr U₁ U₂ → Set U₁`

`apply` is an operation of the Arrow Universal — it gets from the left of the arrow to the right. It is defined as any other Universal operation, without using Lean functions except as convenient syntax to specify signatures.

`𝐂𝐨𝐫𝐫 U₁ U₂` is a Universal with extensional equality: two correspondences are equal when they map every element to the same set.

The full induction chain:
1. Predicate → **Set** (entity)
2. Relation → **Correspondences** (entities)
3. Functional correspondence → **Function** (SubUniversal of Corr)

Each level induces the next. Functions are a SubUniversal of correspondences, not of relations. A function IS a correspondence that happens to always return singletons.

## Directionality

A relation is **undirected** — it is a set of dyads, with no preferred direction. The two correspondences it induces are the directed views: each correspondence goes left-to-right (from source to target), with no ambiguity.

Correspondences are recipes to produce the particular on the right from the particular on the left. They fix the left-to-right direction at extraction time. To go the other way, extract `r2l` instead of `l2r` — there is no need for an `inv` operation on relations.

**Composition only makes sense between correspondences.** In standard mathematics, "composing two relations" implicitly assumes one correspondence direction from each relation. This is a hidden choice. In the framework, composition operates on correspondences, where the direction is explicit and unambiguous. Relation-level composition, if needed, is derived by extracting correspondences first.

## Motivation

Binary predicates express properties that may hold between particulars of two Universals. In the framework, a binary predicate on U₁ and U₂ — via uncurry — is the same as a unary predicate on U₁ ⋈ U₂. A relation, being the extension of a binary predicate, is therefore a set of dyads.

Relations are a Universal. They happen to be represented as sets of dyads — the Relation Universal is `𝐒𝐞𝐭 (U₁ ⋈ U₂)` — and so they inherit all set operations for free.

What IS new is the multi-arity construction interface: the ability to declare relations from fully curried predicates (`relation_from P`) rather than constructing sets of dyads directly. For application, `(a ⋈ b) ∈ₛₑₜ R` already provides multi-arity syntax — you see `a` and `b` separately — while making the set-of-dyads nature transparent.

## Definition

| | Sets | Relations | Correspondences |
|---|---|---|---|
| Primitive entity | — | Dyad `a ⋈ b` | Arrow `a ⟶ S` (instantiation `Arrow U₁ (𝐒𝐞𝐭 U₂)`) |
| Particular type | `Set U` | `Rel U₁ U₂` | `Corr U₁ U₂` |
| Universal | `𝐒𝐞𝐭 U` | `𝐑𝐞𝐥 U₁ U₂` | `𝐂𝐨𝐫𝐫 U₁ U₂` |
| Defined as | unary predicate on `U` => set of `U` | higher arity predicate => unary predicate on of dyads => set of dyads | set of arrows |
| Constructor | `set_from P` | `relation_from P` | `l2r R`, `r2l R` |

```
Rel U₁ U₂ := Set (U₁ ⋈ U₂)
```

A type alias, not a new type. The Relation Universal is:

```
𝐑𝐞𝐥 U₁ U₂ := 𝐒𝐞𝐭 (U₁ ⋈ U₂)
```

Everything from the Set Universal applies: extensional equality, membership, inclusion, powerset, union, etc.

## Canonical Nesting: Left-Association

Higher-arity relations use left-associated dyad nesting:

```
Binary:     Rel U₁ U₂                           = Set (U₁ ⋈ U₂)
Ternary:    Rel (U₁ ⋈ U₂) U₃                    = Set ((U₁ ⋈ U₂) ⋈ U₃)
Quaternary: Rel ((U₁ ⋈ U₂) ⋈ U₃) U₄             = Set (((U₁ ⋈ U₂) ⋈ U₃) ⋈ U₄)
```

This is the canonical form. Predicate associativity guarantees that all nestings are predicatively equivalent, so the choice is a convention. Left-association is natural because:

1. It matches uncurried binary operations — each step takes a dyad and a new argument.
2. Making `⋈` left-associative in Lean (by adjusting notation precedences) would let `a ⋈ b ⋈ c` parse as `(a ⋈ b) ⋈ c` without parentheses.

**Note**: Currently `⋈` is non-associative (`notation:35 x:36 " ⋈ " y:36`). Making it left-associative requires changing the left operand to `:35` on both `bind` and `DyadUniversal`.

Application uses dyad membership with left-association:

```
(a ⋈ b) ∈ₛₑₜ R              -- binary
((a ⋈ b) ⋈ c) ∈ₛₑₜ R        -- ternary
(((a ⋈ b) ⋈ c) ⋈ d) ∈ₛₑₜ R  -- quaternary
```

Or, with left-associative `⋈`: `a ⋈ b ⋈ c ∈ₛₑₜ R`.

## Constructing Relations from Curried Predicates

To declare a relation using fully curried syntax — e.g. `P a b` rather than `P (a ⋈ b)` — write a congruent predicate of the appropriate arity and convert it to a set of dyads. Each arity has its own constructor, because each needs a different number of uncurry steps to flatten the curried predicate into a unary predicate on nested dyads.

### Binary: relation_from

```
noncomputable def relation_from (P: CongruentBinaryPredicate U₁ U₂): Rel U₁ U₂ :=
  let R := (a: U₁.Particular, b: U₂.Particular ↦ (P.pred a).pred b)
  let pred := uncurry R
  let cong := <derived from P's congruence + relatum-wise dyad equality>
  { pred := pred, cong := cong }
```

One uncurry step. Congruence proof: decompose dyads via exhaustiveness, transfer to constructor form via Leibniz substitution, unfold uncurry_def, chain P.cong (first argument) and (P.pred a₂).cong (second argument). **Status: implemented and compiles.**

Membership follows from existing axioms:

- `(a ⋈ b) ∈ₛₑₜ (relation_from P)` ↔ (mem_def) `(relation_from P).pred (a ⋈ b)` ↔ (uncurry_def) `(P.pred a).pred b`

### Ternary: relation_from₃

A ternary relation on U₁, U₂, U₃ is `Rel (U₁ ⋈ U₂) U₃ = Set ((U₁ ⋈ U₂) ⋈ U₃)`. To construct one from a fully curried ternary predicate `P a b c`:

```
noncomputable def relation_from₃ (P: CongruentTernaryPredicate U₁ U₂ U₃): Rel (U₁ ⋈ U₂) U₃ :=
  { pred := uncurry (fun d c => uncurry (fun a b => ...) d)
  , cong := <derived> }
```

Two uncurry steps. Membership:

- `((a ⋈ b) ⋈ c) ∈ₛₑₜ (relation_from₃ P)` ↔ ... ↔ `P a b c`

### Higher arities

Each additional argument adds one more uncurry step and one more level of dyad nesting. The pattern is mechanical: n-ary relations need (n−1) uncurry applications. In practice, binary relations are by far the most common case; ternary and higher can be added when needed.

## Correspondences

### What a Relation Is

A relation is not merely a set of tuples — it is the thing that **induces correspondences** between its components. A binary predicate Pxy introduces two roles (left and right). The relation, being undirected, contains both perspectives. Extracting correspondences gives each perspective its own directed entity:

- `l2r R : Corr U₁ U₂` — for each left particular, the set of associated right particulars
- `r2l R : Corr U₂ U₁` — for each right particular, the set of associated left particulars

These correspondences are real entities (particulars of their respective `𝐂𝐨𝐫𝐫` universals), induced by the relation. They are entangled — they describe the same underlying property from each role's perspective — but once extracted, each has a single unambiguous direction: source → target.

### Arrows: The Primitive Entity

An arrow `a ⟶ b` represents production: from the particular on the left, I can produce the particular on the right. Arrows are a general ADT between any two universals, following the same pattern as dyads:

```
axiom Arrow (U₁: Universal) (U₂: Universal): Type

-- Equality
axiom arrow_eq: Arrow U₁ U₂ → Arrow U₁ U₂ → Prop

-- Constructor: from left, produce right
axiom arrow: U₁.Particular → U₂.Particular → Arrow U₁ U₂

-- Equality definition: componentwise
axiom arrow_eq_def: ∀ (a₁: U₁.Particular), ∀ (b₁: U₂.Particular),
  ∀ (a₂: U₁.Particular), ∀ (b₂: U₂.Particular),
  (arrow a₁ b₁) =_arrow (arrow a₂ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂

-- Exhaustiveness
axiom arrow_exhaustiveness: ∀ (f: Arrow U₁ U₂),
  ∃ (a: U₁.Particular), ∃ (b: U₂.Particular), f 🟰 (arrow a b)
```

Structurally identical to the Dyad ADT. The difference is philosophical: dyads represent co-existence (undirected), arrows represent production (directed).

### Correspondences as Sets of Arrows

Correspondences use the specific instantiation `Arrow U₁ (𝐒𝐞𝐭 U₂)` — arrows from individuals to sets. A correspondence is a set of such arrows:

```
Corr U₁ U₂ := Set (𝐀𝐫𝐫𝐨𝐰 U₁ (𝐒𝐞𝐭 U₂))
```

`apply` is the Arrow Universal's right-projection, giving a set when the target universal is `𝐒𝐞𝐭 U₂`:

```
apply C a := the (𝐒𝐞𝐭 U₂).Particular S such that (arrow a S) ∈ₛₑₜ C
```

The extraction operations `l2r` and `r2l` construct correspondences (sets of individual-to-set arrows) from relations (sets of dyads):

```
l2r R : Corr U₁ U₂   -- for each a, the arrow a ⟶ {b | (a ⋈ b) ∈ₛₑₜ R}
r2l R : Corr U₂ U₁   -- for each b, the arrow b ⟶ {a | (a ⋈ b) ∈ₛₑₜ R}
```

### Correspondence Operations

`apply` maps a particular to a set — it is the fundamental operation on a correspondence:

```
axiom apply: Corr U₁ U₂ → U₁.Particular → Set U₂
axiom apply_def: ∀ C, ∀ a, ∀ b, b ∈ₛₑₜ (apply C a) ↔ ...
```

`dom` is the set of elements whose image under the correspondence is non-empty:

```
axiom dom: Corr U₁ U₂ → Set U₁
axiom dom_def: ∀ C, ∀ a, a ∈ₛₑₜ (dom C) ↔ ∃ b: U₂.Particular, b ∈ₛₑₜ (apply C a)
```

`comp` composes two correspondences (always left-to-right, no ambiguity):

```
axiom comp: Corr U₁ U₂ → Corr U₂ U₃ → Corr U₁ U₃
axiom comp_def: ∀ C₁, ∀ C₂, ∀ a, ∀ c,
  c ∈ₛₑₜ (apply (comp C₁ C₂) a) ↔ ∃ b: U₂.Particular, b ∈ₛₑₜ (apply C₁ a) ∧ c ∈ₛₑₜ (apply C₂ b)
```

### Relation Operations (Derived)

All relation-level operations are derived from correspondences:

```
dom R      := dom (l2r R)       -- domain of the relation
codom R    := dom (r2l R)       -- codomain = domain of the reverse correspondence
comp R₁ R₂ := ...               -- compose l2r correspondences, package back as relation
```

`inv` is not a primitive — to access the other direction, extract `r2l` instead of `l2r`.

### Correspondences of Higher-Arity Relations

An n-ary relation defines a correspondence for every way to split its n components into "fixed" and "free":

| Arity | Fix k, get (n−k) | Count | Total |
|-------|-------------------|-------|-------|
| Binary (n=2) | Fix 1 → Set | C(2,1) = 2 | **2** |
| Ternary (n=3) | Fix 1 → Rel, Fix 2 → Set | 3 + 3 | **6** |
| Quaternary (n=4) | Fix 1 → Ternary Rel, Fix 2 → Rel, Fix 3 → Set | 4 + 6 + 4 | **14** |

Key observation: fixing one component of a ternary relation yields a **binary relation** (not just a set), which itself induces correspondences. This is recursive — each arity's correspondences build on the previous arity's.

### Correspondences Build on Each Other

For a ternary relation `R: Rel (U₁ ⋈ U₂) U₃`:

**Fix two, get a set** (3 correspondences — compose extracted correspondences):

```
fix (x,y), get z:  apply (l2r R) (a ⋈ b)
fix (y,z), get x:  apply (r2l (apply (r2l R) c)) b
fix (x,z), get y:  apply (l2r (apply (r2l R) c)) a
```

The pattern: `r2l R` gives a correspondence from U₃ to `Set (U₁ ⋈ U₂)`. Applying it at `c` returns a `Set (U₁ ⋈ U₂) = Rel U₁ U₂` — a binary relation. Then extract `l2r` or `r2l` from that binary relation and apply again.

**Fix one, get a relation** (3 correspondences):

```
fix z, get Rel U₁ U₂:  apply (r2l R) c                 -- direct (result is Set (U₁ ⋈ U₂) = Rel)
fix x, get Rel U₂ U₃:  curry twice, fix x₀, uncurry    -- curry/uncurry (non-adjacent free vars)
fix y, get Rel U₁ U₃:  curry twice, fix y₀, uncurry    -- curry/uncurry (non-adjacent free vars)
```

For **quaternary** `R: Rel ((U₁ ⋈ U₂) ⋈ U₃) U₄`, `apply (r2l R) d` yields a ternary relation — and all 6 ternary correspondences are already defined. The pattern continues recursively.

### Two Operations Suffice

All correspondences of any arity can be reached from just two operations — `l2r`/`r2l` extraction and `apply` — by composition. The key insight is that `Set (U₁ ⋈ U₂) = Rel U₁ U₂`: when `apply` returns a set of dyads, that set **is** a relation, from which new correspondences can be extracted and applied again.

For a ternary relation `R: Rel (U₁ ⋈ U₂) U₃`:

| Correspondence | Construction | Steps |
|---|---|---|
| fix z, get Rel U₁ U₂ | `apply (r2l R) c` | 1 |
| fix (x,y), get Set U₃ | `apply (l2r R) (a ⋈ b)` | 1 |
| fix x, get Rel U₂ U₃ | curry twice, fix x₀, uncurry | curry + uncurry |
| fix (y,z), get Set U₁ | `apply (r2l (apply (r2l R) c)) b` | 2 |
| fix (x,z), get Set U₂ | `apply (l2r (apply (r2l R) c)) a` | 2 |
| fix y, get Rel U₁ U₃ | curry twice, fix y₀, uncurry | curry + uncurry |

Four of six ternary correspondences are reached by extract + apply composition. The remaining two — "fix x" and "fix y" — require curry (to decompose into individual variables), fixing the target, and uncurry (to reassemble the remaining two into a new relation). Both work the same way: curry R.pred twice to get `P: U₁ → U₂ → U₃ → Prop`, fix one argument, uncurry the remaining two. No isomorphism or reassociation needed — just the curry/uncurry axiom schemes.

For **quaternary**, `apply (r2l R)` reduces to ternary, and all ternary correspondences are already defined. The pattern continues: each arity's correspondences build on the previous arity's, with curry/uncurry needed only for non-adjacent reassembly.

In practice, the most common correspondences (fixing the rightmost component, fixing all-but-one, fixing a contiguous prefix) are all reachable by extract + apply composition alone.

### Worked Example: Middle Fix of a Ternary Relation

Given `R: Rel (U₁ ⋈ U₂) U₃` and `y₀: U₂.Particular`, construct `Rel U₁ U₃`:

**Step 1** — Extract r2l and apply at c (for each c, get a binary relation on x and y):
```
apply (r2l R) c : Set (U₁ ⋈ U₂) = Rel U₁ U₂
(a ⋈ b) ∈ₛₑₜ (apply (r2l R) c) ↔ ((a ⋈ b) ⋈ c) ∈ₛₑₜ R
```

**Step 2** — Extract r2l from that inner relation and apply at y₀ (for each c, get a set of x):
```
apply (r2l (apply (r2l R) c)) y₀ : Set U₁
a ∈ₛₑₜ apply (r2l (apply (r2l R) c)) y₀ ↔ ((a ⋈ y₀) ⋈ c) ∈ₛₑₜ R
```

**Step 3** — This defines a binary predicate on a and c:
```
Q(a, c) := a ∈ₛₑₜ apply (r2l (apply (r2l R) c)) y₀
```

**Step 4** — Uncurry to get a relation on U₁ ⋈ U₃:
```
uncurry Q : (U₁ ⋈ U₃).Particular → Prop
(uncurry Q) (a ⋈ c) ↔ ((a ⋈ y₀) ⋈ c) ∈ₛₑₜ R ✓
```

Two extract-and-apply steps + one uncurry. No isomorphisms or reassociation needed.

### Alternative via Curry/Uncurry Only (Predicate Level)

The same middle-fix correspondence can be constructed purely at the predicate level:

1. `curry R.pred : (U₁ ⋈ U₂).Particular → U₃.Particular → Prop` — split outer dyad
2. For each c, `curry (d ↦ (curry R.pred) d c) : U₁.Particular → U₂.Particular → Prop` — split inner dyad
3. Fix y₀: `(a, c ↦ curry (d ↦ (curry R.pred) d c) a y₀) : U₁ → U₃ → Prop`
4. `uncurry (step 3) : (U₁ ⋈ U₃).Particular → Prop` — reassemble

Two curries to fully decompose, fix the target, one uncurry to reassemble.

## From Correspondences to Functions

### Functional Correspondences

A correspondence is **functional** when it always maps to a singleton set. For `C: Corr U₁ U₂`:

- C is functional if: `∀ a, apply C a` is a singleton set.
- Equivalently: totality + uniqueness:
  1. **Totality**: `∀ a: U₁.Particular, ∃ b: U₂.Particular, b ∈ₛₑₜ (apply C a)`
  2. **Uniqueness**: `∀ a, ∀ b₁, ∀ b₂, b₁ ∈ₛₑₜ (apply C a) ∧ b₂ ∈ₛₑₜ (apply C a) → b₁ =₍U₂₎ b₂`

### Functions

A **function** from U₁ to U₂ is a functional correspondence — a SubUniversal of `𝐂𝐨𝐫𝐫 U₁ U₂`, following the pattern of SingletonSet as a SubUniversal of `𝐒𝐞𝐭 U`.

**Function application** — mapping a particular to a particular — is a derived concept, not a primitive. It extracts the unique element from the singleton set returned by `apply`:

```
Correspondence apply:  x ↦ Set          (always exists, for any correspondence)
Function application:  x ↦ Particular   (only when the correspondence is functional)
```

### Functions as Direct Arrows

A correspondence selects arrows of type `Arrow U₁ (𝐒𝐞𝐭 U₂)` — from an individual, produce a set. When the correspondence is functional (all images are singletons), these individual-to-set arrows are isomorphic to arrows of type `Arrow U₁ U₂` — from an individual, produce an individual directly.

This connects the general Arrow ADT back to its simplest form: a function IS a collection of direct `Arrow U₁ U₂` arrows, without the detour through sets.

```
General correspondence:     selects from Arrow U₁ (𝐒𝐞𝐭 U₂)    -- individual ⟶ set
Functional correspondence:  isomorphic to Arrow U₁ U₂           -- individual ⟶ individual
```

To be detailed in a separate design doc.

## Relationship to Existing Code

### Existing Relations Module

`Universals/Relations/Relations.lean` predates the Universals architecture. It works within a single universe (`BinRel := Universe.BinaryPredicate` on type X) and defines correspondences, domain, codomain, correspondences (`R⟨x⟩`, `R⟨·,y⟩`), and functional characterization. The new cross-universal design supersedes this module, but the conceptual structure — correspondences as the central concept, functions as functional correspondences — carries forward directly.

### CongruentBinaryPredicate

The existing `CongruentBinaryPredicate U₁ U₂` schema (curried: `pred` maps `U₁.Particular` to `CongruentUnaryPredicate U₂`, with congruence in the first argument) is the multi-arity declaration mechanism. `relation_from` converts it into a `Rel`. This makes `CongruentBinaryPredicate` the interface for expressing "what the relation says" and `Rel` the set-theoretic representation of "what the relation contains."

## Implementation Status

- [x] `Rel U₁ U₂` type alias — `Universals/Relations/Particular.lean`
- [x] `relation_from` binary constructor with congruence proof — `Universals/Relations/Particular.lean`
- [ ] `𝐑𝐞𝐥 U₁ U₂` Universal alias
- [ ] `𝐀𝐫𝐫𝐨𝐰 U₁ U₂` Arrow ADT — general between any two universals (type, eq, arrow, eq_def, exhaustiveness)
- [ ] `𝐂𝐨𝐫𝐫 U₁ U₂` Correspondence Universal (as `Set (𝐀𝐫𝐫𝐨𝐰 U₁ (𝐒𝐞𝐭 U₂))`)
- [ ] `l2r` and `r2l` extraction (relation induces correspondences)
- [ ] `apply` on correspondences
- [ ] `dom` on correspondences
- [ ] `comp` on correspondences
- [ ] Make `⋈` left-associative (change `:36` to `:35` on left operand of both `bind` and `DyadUniversal`)
- [ ] Ternary correspondences (built from binary via extract + apply)
- [ ] `relation_from₃` ternary constructor
- [ ] Function SubUniversal of `𝐂𝐨𝐫𝐫` (separate design doc)
