import Universals.Relations.Universal
import Universals.Relations.Operations.Binary.RightRestriction.Operation
import Universals.Sets.Definitions.SetsAsUniversals.Definition
import Universals.Dyads

/-!
# Sub-Universals and the `<:` relation

## Why this infrastructure exists

The framework uses many-sorted first-order logic. In a proper many-sorted FOL
engine, sub-sorts would be primitive: you would establish that S is a sub-sort
of U by providing the injection and proving equality preservation, and then the
engine would handle everything else — propagation through composite sorts (dyads,
relations, etc.) and transparent coercions.

Lean does have subtyping infrastructure (Subtype, coercions, type classes), but
we cannot leverage it for this purpose because our framework uses its own
equalities (`=₍U₎`) — axiomatized predicates that Lean's type system knows
nothing about. Lean's `Subtype.val` handles the element-level injection, but
Lean cannot see that sub-universal equality and parent equality agree, nor
propagate this through our axiomatized composite types.

`SubUniversal` (`<:`) fills this gap. It is framework infrastructure — not
mathematics — that compensates for Lean not being a native many-sorted FOL engine.
The `op` field, the `preserves_eq` proof, the lift axioms, and the CoeDep instances
are all machinery that a proper many-sorted engine would provide for free.

## The problem that motivated this

Operations like `right_restrict R S` return types that depend on the input:

  right_restrict R S : Rel U1 (set_as_universal S)

When S varies, the output types differ. So the natural congruence statement:

  S₁ =ₛₑₜ S₂ → right_restrict R S₁ =ᵣₑₗ right_restrict R S₂

does NOT type-check — the two sides have different types
(`Rel U1 (set_as_universal S₁)` vs `Rel U1 (set_as_universal S₂)`).

## Why Lean's ↑ doesn't help directly

Lean's ↑ (Subtype.val) works at the first level: S.Particular → U2.Particular,
because `set_as_universal S` is defined via `refined_universal` which uses Lean's Subtype.

But ↑ does NOT propagate through axiomatized composite types:
- Dyad U1 S is NOT a Lean subtype of Dyad U1 U2 (Dyad is an opaque axiom type)
- Rel U1 S is NOT a Lean subtype of Rel U1 U2 (built on Dyad)

So `↑(right_restrict R S)` as `Rel U1 U2` does not work.

## The solution: three layers

### 1. SubUniversal (U' <: U)
A map from U' to U that preserves equality in both directions. Generalizes
Subtype.val — any equality-preserving map qualifies, not just refined types.
The canonical instance wraps Subtype.val for sub-universals defined via predicates.

### 2. Lift axioms for composite universals
Each composite universal (Dyads, Relations, ...) provides axioms that transport
`<:` through its components. This is standard equipment for the universal's
ADT specification, alongside constructors, equality, and exhaustiveness.

### 3. CoeDep instances
Lean coercions make the lifts invisible. Writing `(right_restrict R S : Rel U1 U2)`
silently inserts the lift. Uses CoeDep (value-dependent coercion) because Lean's
instance resolution cannot recover S from the type alone (semi-out-param limitation).

## The payoff

With coercions, the congruence theorem is just a plain theorem — no special schema:

  theorem right_restrict_cong: ∀ R S₁ S₂,
    S₁ =ₛₑₜ S₂ → (right_restrict R S₁ : Rel U1 U2) =ᵣₑₗ (right_restrict R S₂ : Rel U1 U2)

Lean inserts the lifts transparently. A DependentCongruentUnaryOperation schema was
considered but turns out to be unnecessary — coercions solve the problem at the type
level, so dependent operations need no special treatment.

## Standardizing for the framework

### What each composite universal must provide

Every composite universal built from component universals must include, as part of
its ADT specification (alongside constructors, equality, exhaustiveness):

1. **Lift axioms** — one per component position, parameterized by `<:`.
   For a binary composite like DyadUniversal U1 U2:
   - `dyad_lift_left`:  U1' <: U1 → lifts U1' ⧓ U2 to U1 ⧓ U2
   - `dyad_lift_right`: U2' <: U2 → lifts U1 ⧓ U2' to U1 ⧓ U2
   For a derived composite like RelationUniversal (built on Dyads):
   - `rel_lift_left`:  U1' <: U1 → lifts Rel U1' U2 to Rel U1 U2
   - `rel_lift_right`: U2' <: U2 → lifts Rel U1 U2' to Rel U1 U2

2. **Lift defining axioms** — behavior on constructors, e.g.:
   - `dyad_lift_right_def`: `dyad_lift_right e (a ⋈ v) =ₗₓₗ (a ⋈ e.op v)`
   - `rel_lift_right_def`:  `rel_lift_right e R' =ᵣₑₗ rel_lift_right_rel e R'`

3. **CoeDep instances** — one per concrete coercion path. For a binary composite,
   you need instances for left, right, and both components:
   - `Rel U1 (set_as_universal S) → Rel U1 U2`   (right sub-universal)
   - `Rel (set_as_universal S) U2 → Rel U1 U2`   (left sub-universal)
   - `Rel (set_as_universal S₁) (set_as_universal S₂) → Rel U1 U2`  (both)

### Why CoeDep instances must be concrete (not generic)

We tried making SubUniversal (`<:`) a type class so Lean would resolve coercions
generically for any embedding. This DOES NOT WORK: Lean's instance resolution cannot
unfold `set_as_universal S` to `U2 ↾ S` during matching. So each composite
universal needs its own concrete CoeDep instances. This is a minor inconvenience —
one instance per coercion path — but each is a one-liner.

## Why bidirectional equality preservation? When is U' <: U legitimate?

For refined types (sub-universals via predicates), the embedding maps each element
to "itself" in the parent, so preserving and reflecting equality is trivial —
sub-universal equality IS parent equality by definition.

But in general (e.g., embedding ℕ into ℤ where integers are pairs of naturals),
the embedding maps elements to a different representation. The question is: when
is it legitimate to prove congruence by lifting to the parent universal?

The answer: the embedding must preserve equality in both directions:

  x =₍U'₎ y  ↔  e(x) =₍U₎ e(y)

This bidirectional equivalence is what makes it safe to reason "upstairs" and
conclude things "downstairs."

**Why the backward direction is essential**: When we prove congruence of an
operation at the parent level:

  S₁ =ₛₑₜ S₂ → e(op S₁) =₍Parent₎ e(op S₂)

we want this to mean op S₁ =₍B'₎ op S₂. The backward direction gives us
parent equality implies original equality. Without it, the parent could identify
things that are distinct in the original, and we'd be "proving congruence" for
an operation that isn't actually congruent. That would be unsound.

**Example: ℕ ↪ ℤ** (via n ↦ (n, 0)): both directions hold — equal naturals
map to equal integers, and (n₁,0) =ℤ (n₂,0) implies n₁ =ₙₐₜ n₂.
This is a legitimate sub-universal relationship.

**Counterexample**: f(n) = n mod 2 from ℕ to ℕ. Forward direction holds, but
backward fails (f(2) = f(4) but 2 ≠ 4). If we used this as a `<:`, we could
falsely prove congruence for operations that distinguish 2 from 4.

### File organization

- `SubUniversal` schema + `<:` notation → `Logic/PredicateCalculus/Schemas/SubUniversal/`
- `refined_universal` (`↾`) construction → `Logic/PredicateCalculus/Schemas/RefinedUniversal/`
- `refined_universal_is_sub` → `Logic/PredicateCalculus/Schemas/RefinedUniversal/Properties/SubUniversal/`
- Lift axioms for Dyads → `Universals/Dyads/Definitions/SubUniversalLift/`
- Lift axioms for Relations → `Universals/Relations/Definitions/SubUniversalLift/`
- CoeDep instances → alongside the lift axioms for each composite universal
-/

namespace Universe
namespace Test

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads
open Relations

-- ============================================================
-- # 1. SubUniversal — uses the framework's SubUniversal schema
-- ============================================================

-- The framework provides SubUniversal (notation <:) in
-- Logic.PredicateCalculus.Schemas.SubUniversal.Schema.
-- It requires an embedding : UnaryOperation U' U (notation ⟴)
-- and a proof that the embedding preserves equality bidirectionally.

-- Refined universals are sub-universals of their parent.
-- U ↾ P has Particular = { x : U.Particular // P.pred x },
-- and equality is parent equality on values.
--
-- The embedding is Subtype.val with graph G(x, y) = x.val =₍U₎ y.
-- Since RU's equality is defined as x.val =₍U₎ y.val and the operation
-- is Subtype.val, the defining axiom and preserves_eq are both P ↔ P.
-- The graph congruence proofs follow from transitivity and symmetry of U.eq.
--
-- This is logic infrastructure — a many-sorted FOL engine would provide
-- this embedding automatically when creating a restricted sort.
--
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-12
noncomputable def refined_universal_is_sub {U: Universal} (P: CongruentUnaryPredicate U):
    (U ↾ P) <: U :=
  let RU := U ↾ P
  -- Graph: G(x, y) = x.val =₍U₎ y
  let graph: CongruentBinaryPredicate RU U :=
    let pred: RU.Particular → CongruentUnaryPredicate U :=
      fun (x: RU.Particular) => {
        pred := fun (y: U.Particular) => x.val =₍U₎ y,
        cong := sorry  -- inner congruence: y₁ =₍U₎ y₂ → (x.val =₍U₎ y₁ ↔ x.val =₍U₎ y₂)
      }
    { pred := pred, cong := sorry }  -- outer congruence: x₁ =₍RU₎ x₂ → (x₁.val =₍U₎ z ↔ x₂.val =₍U₎ z)
  -- Operation and defining axiom
  let op_fn: RU.Particular → U.Particular := Subtype.val
  -- op_fn x =₍U₎ y  ↔  (graph.pred x).pred y  — both sides are x.val =₍U₎ y
  let op_def: ∀ (x: RU.Particular), ∀ (y: U.Particular),
      (op_fn x =₍U₎ y) ↔ (graph.pred x).pred y := by forall_intro
    variable(x: RU.Particular)
    variable(y: U.Particular)
    have h₁: (op_fn x =₍U₎ y) → (graph.pred x).pred y := by
      assume(h: op_fn x =₍U₎ y)
      iterate h
    have h₂: (graph.pred x).pred y → (op_fn x =₍U₎ y) := by
      assume(h: (graph.pred x).pred y)
      iterate h
    have h₃: (op_fn x =₍U₎ y) ↔ (graph.pred x).pred y := by iff_intro h₁, h₂
    iterate h₃
  let embedding: RU ⟴ U := { ext := graph, op := op_fn, «def» := op_def }
  -- preserves_eq: x =₍RU₎ y ↔ embedding x =₍U₎ embedding y
  -- Both sides are x.val =₍U₎ y.val
  let preserves_eq: ∀ (x: RU.Particular), ∀ (y: RU.Particular),
      x =₍RU₎ y ↔ (embedding x =₍U₎ embedding y) := by forall_intro
    variable(x: RU.Particular)
    variable(y: RU.Particular)
    have h₁: x =₍RU₎ y → (embedding x =₍U₎ embedding y) := by
      assume(h: x =₍RU₎ y)
      iterate h
    have h₂: (embedding x =₍U₎ embedding y) → x =₍RU₎ y := by
      assume(h: embedding x =₍U₎ embedding y)
      iterate h
    have h₃: x =₍RU₎ y ↔ (embedding x =₍U₎ embedding y) := by iff_intro h₁, h₂
    iterate h₃
  { embedding := embedding, preserves_eq := preserves_eq }

-- ============================================================
-- # 2. Dyad embedding (right component)
-- ============================================================

-- An embedding U2' <: U2 induces a map on dyads: U1 ⧓ U2' → U1 ⧓ U2.
axiom dyad_lift_right {U1 U2 U2': Universal} (e: U2' <: U2):
  (U1 ⧓ U2').Particular → (U1 ⧓ U2).Particular

axiom dyad_lift_right_def {U1 U2 U2': Universal} (e: U2' <: U2):
  ∀ (a: U1.Particular), ∀ (v: U2'.Particular),
  dyad_lift_right e (a ⋈ v) =ₗₓₗ (a ⋈ e.embedding v)

-- Derivable from dyad_lift_right_def, eq_def, exhaustiveness, and e.preserves_eq.
theorem dyad_lift_right_preserves_eq {U1 U2 U2': Universal} (e: U2' <: U2):
  ∀ (d₁: (U1 ⧓ U2').Particular), ∀ (d₂: (U1 ⧓ U2').Particular),
  d₁ =ₗₓₗ d₂ ↔ (dyad_lift_right e d₁ =ₗₓₗ dyad_lift_right e d₂) := sorry

-- The induced embedding on dyads.
noncomputable def dyad_embedding_right {U1 U2 U2': Universal} (e: U2' <: U2):
    (U1 ⧓ U2') <: (U1 ⧓ U2) :=
  { embedding := { ext := sorry, op := dyad_lift_right e, «def» := sorry },
    preserves_eq := dyad_lift_right_preserves_eq e }

-- ============================================================
-- # 3. Relation embedding (right component)
-- ============================================================

-- An embedding U2' <: U2 induces a map on relations: Rel U1 U2' → Rel U1 U2.

-- The binary predicate characterizing the lifted relation:
-- (a, u) is related iff there exists v in U2' with e(v) =₍U2₎ u and R'(a, v).
noncomputable def rel_lift_right_pred {U1 U2 U2': Universal} (e: U2' <: U2)
    (R': Rel U1 U2'): CongruentBinaryPredicate U1 U2 := sorry

-- The constructed relation via relation_from.
noncomputable def rel_lift_right_rel {U1 U2 U2': Universal} (e: U2' <: U2)
    (R': Rel U1 U2'): Rel U1 U2 :=
  relation_from (rel_lift_right_pred e R')

-- Operation symbol.
axiom rel_lift_right {U1 U2 U2': Universal} (e: U2' <: U2):
  Rel U1 U2' → Rel U1 U2

-- Defining axiom: the operation equals the constructed relation.
axiom rel_lift_right_def {U1 U2 U2': Universal} (e: U2' <: U2):
  ∀ (R': Rel U1 U2'),
  rel_lift_right e R' =ᵣₑₗ rel_lift_right_rel e R'

-- Derivable from rel_lift_right_def and relation equality.
theorem rel_lift_right_preserves_eq {U1 U2 U2': Universal} (e: U2' <: U2):
  ∀ (R₁: Rel U1 U2'), ∀ (R₂: Rel U1 U2'),
  R₁ =ᵣₑₗ R₂ ↔ (rel_lift_right e R₁ =ᵣₑₗ rel_lift_right e R₂) := sorry

-- The induced embedding on relations.
noncomputable def rel_embedding_right {U1 U2 U2': Universal} (e: U2' <: U2):
    (𝐑𝐞𝐥 U1 U2') <: (𝐑𝐞𝐥 U1 U2) :=
  { embedding := { ext := sorry, op := rel_lift_right e, «def» := sorry },
    preserves_eq := rel_lift_right_preserves_eq e }

-- ============================================================
-- # 4. Concrete embedding and coercion for set sub-universals
-- ============================================================

-- The embedding from Rel U1 (set_as_universal S) into Rel U1 U2.
noncomputable def rel_right_sub_embedding {U1 U2: Universal} (S: Set U2):
    (𝐑𝐞𝐥 U1 (set_as_universal S)) <: (𝐑𝐞𝐥 U1 U2) :=
  rel_embedding_right (refined_universal_is_sub S)

-- Coercion: uses the embedding's operation.
noncomputable instance {U1 U2: Universal} (S: Set U2) (R_S: Rel U1 (set_as_universal S)):
    CoeDep (Rel U1 (set_as_universal S)) R_S (Rel U1 U2) where
  coe := (rel_right_sub_embedding S).embedding R_S

-- ============================================================
-- # 5. Note on generalized coercions
-- ============================================================

-- We tried making SubUniversal (<:) a type class so Lean would resolve
-- coercions generically. This DOES NOT WORK: Lean's instance resolution
-- cannot unfold `set_as_universal S` to `U2 ↾ S` during matching.
-- So each composite universal needs its own concrete CoeDep instance (as above).
-- This is a minor inconvenience — one instance per coercion path — but each
-- is a one-liner.

-- ============================================================
-- # 6. Tests
-- ============================================================

variable {U1 U2: Universal}
variable (R: Rel U1 U2) (S₁ S₂: Set U2)

-- Coercion works transparently
#check (right_restrict R S₁ : Rel U1 U2)

-- The congruence theorem we wanted is now well-typed
#check S₁ =ₛₑₜ S₂ → (right_restrict R S₁ : Rel U1 U2) =ᵣₑₗ (right_restrict R S₂ : Rel U1 U2)

-- State it as a plain theorem — no special schema needed
theorem right_restrict_cong: ∀ (R: Rel U1 U2), ∀ (S₁: Set U2), ∀ (S₂: Set U2),
  S₁ =ₛₑₜ S₂ → (right_restrict R S₁ : Rel U1 U2) =ᵣₑₗ (right_restrict R S₂ : Rel U1 U2) := sorry

end Test
end Universe
