# This is a Mathpunk project.

> "The deep reasons for the regularities that we may observe in concrete contexts actually live at the syntactic level... We need to teach learning systems to lift from the phenomenological level... to the ontological one."
>
> — **Olivia Caramello**, *Syntactic Learning via Topos Theory*

## The Mathpunk Manifesto

Mathpunk is a philosophy of formal mathematics **enabled by** proof assistants and proof checkers.

These tools revolutionize mathematics by **physicalizing the mathematical universe**— allowing it to be explored by anyone as if it was a physical reality, thus **democratizing mathematics**.

**Mathpunk builds on this foundation with a single, foundational principle:**

We use these tools to **explore the mathematical universe** free of all baggage, and we categorically reject their use for proof automation.

- **We are hardcore about this:** proofs must be explicit, contain all steps and be readable.
- **Why?** Because proofs reveal understanding. Automated proofs obscure it.

In Mathpunk, the machine renders the mathematical universe, **the foundations are explicit, and the proofs are written out in full detail**. Lean verifies correctness; the proofs reveal the reasoning.

A Mathpunk project is defined by its method, not its subject. It adheres to the foundational principle, and has three core characteristics:

### 1. DIY Foundations
A Mathpunk project does not treat its foundations as invisible background. It makes explicit which foundations it is using, and it keeps a sharp distinction between mathematical ideas and their concrete encoding. It may build new foundations or work within existing ones, but in either case it must show how the mathematics unfolds from them with explicit, complete, readable proofs.

### 2. Power Over Safety
Modern proof assistants are designed to prevent paradox and guarantee termination. We appreciate the safety this brings, but Mathpunk prioritizes expressive power over safety, embracing "unsafe" features like unrestricted recursion. The responsibility for ensuring consistency and termination rests on the explicit proofs, not the tool — every derivation is visible and auditable.

### 3. Radical Explicitness
There is no hidden magic. Every step of a proof must be explicitly derived — no automated tactics that hide the reasoning. Verbosity is accepted as the price of clarity. The goal is not just to prove that a theorem is true, but to show *why* it is true in the most granular way possible.

**Note on LLMs**: Large language models can assist in writing these explicit proofs. This does not violate Mathpunk principles — the objection to automation is about *opacity*, not about who types the characters. An LLM writing explicit FOL proofs produces the same artifact a human would: every step visible, every inference auditable. Lean verifies correctness; the proofs remain fully transparent. The burden of verbosity is reduced while maintaining complete auditability.

This is an unexpected benefit of Mathpunk: the explicitness that reveals understanding to humans also makes proofs *writable* by LLMs. The same property — no hidden steps, systematic structure — serves both purposes.

---

## About This Project

This repository is a **Mathpunk take on Neo-Logicism**.

It applies the Mathpunk philosophy to a specific foundational thesis: that **mathematics is the structure that arises from making verifiable statements about well-defined things**, which is what logic is for at its core. Therefore, we postulate that **mathematics is logical structure, not extra ontology**.

We do not claim that the "things" themselves arise from logic. Instead, we use First-Order Logic (FOL) to specify a `Theory` that:

1) Precisely specifies the "things" we talk about, without taking `Type` as a primitive.
2) Derives mathematical objects like `Sets` and `Functions` from predicates about those things, rather than postulating them as primitives.
3) Supports higher-order reasoning, because some derived objects (like `Sets`) become new things we can quantify over and make predicates about.

**We postulate that this `Theory` is able to express all of mathematics.**

**To show this thesis, this project implements this `Theory` in the Lean 4 virtual reality engine.**

---

## The Theory

The `Theory` is many-sorted first-order logic with the following characteristics:

  1. Terms are typed. Here, "types" are predicates inside the theory, not meta-level sorts. A type determines which terms are admissible, as follows:
    1.1 Term formation is governed by axioms:
      1.1.1 We introduce explicit `Type Judgments`, i.e. `t : T`, is a binary predicate meaning "term `t` has type `T`."
      1.1.2 We write axioms defining what are the valid terms of a type.
        `zero : Nat` (zero is a valid term of type `Nat`)
        `∀x, (x : Nat) → (succ x : Nat)` (if `x` is a valid term of type `Nat`, then `succ x` is a valid term of type `Nat`).
    1.2 Quantification is type-restricted: ∀ x:T, P(x) is syntactic sugar for ∀x,(x:T) → P(x).
    1.3 Free variables in predicates are typed, and can only be replaced by terms of the specified type.
        For example, `P(x : Nat, y : Bool)` as opposed to `P(x, y)` where the types of x and y are not specified.

  2. To support the above, we allow `Recursive Predicate Definitions`, i.e. we allow predicate definitions where the predicate
  appears in its own definition. Formally, we allow axioms of the form: `∀x₁...xₙ, P(x₁,...,xₙ) ↔ φ(x₁,...,xₙ)` even when `φ`
  contains occurrences of `P`.

  We use `Natural Deduction` as our proof system.

  **Note 1**: The `Theory` enforces well-typed reasoning internally: a term is treated as having type `T` only when the judgment `t : T` is derivable from the axioms (e.g. `zero : Nat` and `∀x, (x : Nat) → (succ x : Nat)`). As a result, ill-typed judgments (e.g. `true : Nat`) are not derivable, and ill-typed substitutions cannot be used in valid proofs.

  **Note 2**: Predicates with free variables are not considered functions, e.g. propositional functions, as that would introduce a circularity. `Functions` will be derived from the notion of predicate itself, so we cannot use them to define what a predicate with free variables is. A predicate with free variables must be interpreted as a template for a statement that contains placeholders, which becomes a statement when these placeholders are filled with terms. Types impose restrictions on the allowed substitutions for the placeholders. Moreover, Symbols like `zero` or `succ` are syntactic tokens, not function symbols with pre-existing semantics. Their meaning derives entirely from predicate axioms.

  **Note 3**: As with any foundational theory, we postulate consistency rather than mechanically enforcing it. The payoff of the Mathpunk proof discipline is auditability: every theorem comes with an explicit derivation, so its dependence on specific axioms is visible.

  - **Consistency**: If a contradiction is later found (i.e. some axiom subset proves `False`), we can isolate the responsible axioms and track which theorems depend on them by following proof dependencies.

  - **Non-Termination**: `Recursive Predicate Definitions` are not checked for termination. If unfolding does not terminate, this does not compromise the `Theory`; it only makes that definition unusable for proofs that rely on unfolding.

  Similarly, when defining a type `T` in the `Theory`, users may want to make sure that all axioms that introduce terms of type `T` don't contain `T` in contravariant positions inside the definitions.

  **Note 4**: Refined types are types. If a "type" is a predicate `T` selecting admissible terms, and `P` is a further predicate on terms, then the refined type is the predicate `T ∧ P`. Its terms are exactly those terms satisfying both `T` and `P`.

  **Note 5**: This `Theory` is inspired by `Abstract Data Types` (ADTs). In practice, this means specifying types by axioms that govern which terms belong to each type, then introducing operations via axioms that define their behavior in terms of the type's equality.

  **Note 6**: There is a crucial distinction between **specifying the syntactic structure of terms** and **asserting that those terms exist**. Saying "`succ` takes a `Nat` and produces a `Nat`" specifies the **signature** — the shape of well-formed expressions. Saying "for every natural `n`, the term `succ(n)` exists" is an **existential commitment**. These are different claims.

  In the Lean implementation, function symbols are declared using arrow syntax: `axiom succ : ℕ → ℕ`. This conveniently specifies the signature, but Lean's type-theoretic kernel goes further — it automatically incarnates every well-typed function application as an existing term. Writing `succ n` for any `n : ℕ` does not merely form a syntactic expression; it produces a term that Lean treats as fully existing. Lean conflates signature with existence because its foundations are type-theoretic. This is a convenience it provides, but it is not the semantics of first-order logic, where the two are separate.

  Since this `Theory` is first-order logic, we do not rely on Lean's type system for existence. Instead, every function symbol declaration is paired with an explicit **existence axiom**:

  - For a constant `c : T`: `∃ x : T, x = c`
  - For a k-ary function `f : T₁ → ⋯ → Tₖ → T`: `∀ x₁ : T₁, …, ∀ xₖ : Tₖ, ∃ y : T, y = f(x₁, …, xₖ)`

  The Lean declaration specifies what you can write; the existence axiom asserts what exists.

  *Side note for Scala programmers: this parallels the distinction between a method signature and implicit evidence. `def succ(n: Nat): Nat` declares a signature, but an `implicit` is what witnesses that instances actually exist. If `zero` is `implicit`, existence propagates through the constructors via implicit resolution — `succ(zero)` can be resolved because `zero` is available. Our existence axioms play exactly this role: explicit evidence that the constructors produce existing terms.*

---

## Universals and Equality

The `Theory` described above is many-sorted first-order logic — familiar territory. However, we need to extend it because of how we treat equality. The result is a two-level architecture.

**Leibniz equality** is the fundamental equality of first-order logic — syntactic identity of terms within a type. It is axiomatized by two principles. Reflexivity is the foundation: it declares that a term is the same as itself. From this sameness follows substitutability: equal terms can replace each other in any predicate — if `x = y`, then `P(x) ↔ P(y)` for any predicate `P`. Symmetry and transitivity are derived from these two axioms alone.

But in mathematics, Leibniz equality is rarely what we want. We don't care whether two groups are literally the same object; we care whether they are isomorphic. We don't distinguish homeomorphic spaces. Mathematical reasoning works "up to" the appropriate notion of equivalence.

We extend the `Theory` to support this with **Universal equality**. A `Universal` pairs a type with an equality relation on that type. We call the terms of a `Universal` its `Particulars`. Each `Universal` defines its own `Equality` — required only to be an equivalence relation (reflexive, symmetric, transitive), not necessarily Leibniz equality. In practice, Universal equalities are defined by impurifier equations between the generative constructors of an abstract data type — for example, the natural numbers' equality is defined by how `zero` and `succ` interact.

Every Leibniz equality implies the corresponding Universal equality — if two terms are syntactically identical, they are certainly equal under any Universal's equality. But the converse need not hold: a Universal equality may identify terms that are syntactically distinct. This asymmetry is the whole point — Universal equalities capture the mathematical notion of equivalence appropriate to each domain.

Leibniz equality plays an essential role in bootstrapping Universal equalities. Our types are opaque axioms (not Lean inductive types), so Lean provides no recursor or case analysis. Exhaustiveness induction axioms fill this gap: they produce Leibniz equalities that characterize the syntactic forms each term can take (e.g. `n = zero` or `n = succ k`), enabling proof by cases in general. A particularly important application is proving that each Universal's equality is well-defined — that it is indeed an equivalence relation. These proofs use Leibniz substitution directly: it can substitute syntactically identical terms inside any predicate, including predicates involving the type's own equality, without requiring a Universal to exist yet. Once the Universal is constructed, a bridge theorem (`x 🟰 y → x =₍U₎ y`) provides a convenient shortcut for later proofs that need case analysis.

Because Universal equality is not syntactic identity, we cannot assume substitutivity. A predicate might distinguish isomorphic groups — it might depend on details not preserved by isomorphism. So we must prove, for each predicate, that it respects the `Universal`'s `Equality`. A `CongruentPredicate` is a predicate bundled with this proof. The proof — called the congruence proof — demonstrates that the predicate cannot distinguish `Particulars` that the `Equality` considers the same.

The payoff is immediate: any theorem we prove about a `Universal` applies to all `Particulars` that are equal according to that `Universal`'s `Equality`. Prove something about a group, and it transports automatically to all isomorphic groups. The congruence proofs ensure this.

This is a poor man's univalence. In Homotopy Type Theory, the univalence axiom asserts that equivalent types are equal, making transport across equivalences automatic. We achieve the same goal — properties transport across equivalences — but manually, through explicit congruence proofs. More work, but it stays within first-order logic and requires no exotic foundations.

In the implementation, Lean provides convenient packaging: structures that bundle types with equalities (`Universal`), and predicates with their congruence proofs (`CongruentPredicate`). This is pure first-order logic; Lean adds no logical power, only discipline. What would be tracked informally in a textbook — "see Lemma 3.2 for well-definedness" — is here bundled directly with the predicate.

Every predicate in this `Theory` is a `CongruentPredicate`. The congruence proofs are not bureaucratic overhead — they are the mathematical content that ensures our constructions respect the equivalence structure each `Universal` has chosen.

---

## Existence and Predication

The philosophical core of this framework rests on a single principle: **existence is the only primitive assertion; everything else comes from predicates.**

A particular `a` asserts that `a` exists in the universe, with the syntactic form given by its constructors. Its identity is constituted by the equality of the `Universal` it belongs to — the only relation a particular has out of the box, before any predication. Beyond that, it has no properties, no relations, no meaning.

Predicates are what make existence meaningful. A unary predicate `P(x)` selects from existing particulars, actualizing which properties they have. Properties and relations beyond equality are not intrinsic to particulars — they are bestowed by predication.

### Co-Existence

But what about relations? A relation is not a property of one particular — it involves two. How does the framework handle this without breaking the uniform view that all predicates select particulars?

The answer: **co-existence is equally primitive**. A `Dyad` `a ⋈ b` asserts exactly one thing: that `a` and `b` co-exist in the universe. Nothing more. No direction, no relation, no properties. Just co-presence. Before predication, a dyad has no relational content — it only asserts that its two particulars can be relata.

This achieves the following symmetry:

| | Particular `a` | Dyad `a ⋈ b` |
|---|---|---|
| **What it asserts** | `a` exists | `a` and `b` co-exist |
| **What predicates do** | Actualize which properties | Actualize which relations |

Particulars and dyads are equally primitive, equally bare. The only difference is structural — the number of terms whose co-existence is asserted. And since dyads are themselves particulars of their own `Universal`, the framework treats them uniformly.

### Recursive Co-Existential Closure

The universe is closed under co-existential binding at all levels. If `X` and `Y` exist, then `X ⋈ Y` exists. This applies recursively:

- `a ⋈ b` exists if `a` and `b` exist
- `a ⋈ (b ⋈ c)` exists if `a` and `b ⋈ c` exist
- `(a ⋈ b) ⋈ (c ⋈ d)` exists if `a ⋈ b` and `c ⋈ d` exist

This is not a process — nothing is "created later." The universe is saturated by structural closure. Because dyads are predicate-associative — different nestings of the same base particulars are predicate-equivalent — the dimension of a co-existence is simply the number of base particulars it involves:

- 1-dim: a single particular
- 2-dim: a dyad of two particulars (`a ⋈ b`)
- 3-dim: three particulars (`a ⋈ (b ⋈ c)`, equivalently `(a ⋈ b) ⋈ c`)
- n-dim: n base particulars, nested in any order

### Predicate Uniformity

Because dyads at every level are first-class `Particulars` forming their own `Universals`, all predicates remain unary — they just act on different structural levels:

- Unary predicates on particulars actualize **properties**
- Unary predicates on dyads actualize **relations**
- Unary predicates on nested dyads actualize **higher-order relational structure**

The universe is just the totality of what exists — particulars and their co-existences. Logic (predicates) is what makes that existence meaningful by selecting patterns from it. The two are perfectly separable and perfectly complementary.

---

## Variable-Arity Predicates

The philosophy above has a concrete technical realization. A predicate is a statement template with typed placeholders. A unary predicate `P(x)` has one placeholder — it selects `Particulars` from a `Universal`. A binary predicate `R(x, y)` has two independent placeholders. We want the same uniform view: all predicates select `Particulars`.

Dyads make this possible. If `a : U₁` and `b : U₂`, then `a ⋈ b : U₁ ⋈ U₂` is the dyad binding the relata `a` and `b` into a single term. Dyads form their own `Universal` with relatum-wise equality, so they can be quantified over, collected into sets, and subjected to the same predicate machinery as any other `Particulars`.

To transport between binary predicates and unary predicates on `Dyads`, we introduce two axiom schemes:

- **Predicate Uncurry**: takes two independent placeholders and binds them into a single dyad placeholder. `R(a, b)` becomes `uncurry R(d)`.
- **Predicate Curry**: splits a dyad placeholder into two independent placeholders. `P(d)` becomes `curry P(a, b)`.

These are called "curry" and "uncurry" by analogy with function theory, but they operate on statement templates, not functions. The propositional content is preserved: `uncurry R (a ⋈ b) ↔ R a b` and `curry P a b ↔ P (a ⋈ b)`.

**Why axiom schemes?** In type theory or higher-order logic, predicate uncurry is provable via lambda abstraction: given `R : A → B → Prop`, one writes `λd. R d.left d.right`. But lambda abstraction treats predicates as functions, and in this `Theory`, `Functions` are derived from predicates (see Note 2 in The Theory). Using lambda abstraction to define predicate uncurry would introduce a circularity. So we postulate predicate curry and uncurry as axiom schemes — conservative definitional extensions that add no new theorems in the old language.

**Higher arities compose via nesting.** Dyads nest: a ternary predicate `R(x, y, z)` becomes a unary predicate on `U₁ ⋈ (U₂ ⋈ U₃)` by applying uncurry twice. The same two axiom schemes handle any arity — no new machinery is needed beyond arity 2.
