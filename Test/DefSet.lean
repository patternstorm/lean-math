import Logic
import Universals.Sets

/-!
# `defset` — Enforcing the spec/impl/proof discipline for set definitions

## What this prototype demonstrates

A `defset` command that REQUIRES the user to provide three things when defining
a set: a specification (the membership characterization), an implementation (the
set comprehension predicate), and a proof connecting them. The set's body is
then made opaque to downstream proofs.

```
defset my_set <params> : Set U where
  spec  := <proposition about membership in my_set>
  impl  := <set comprehension expression>
  proof := <proof that impl satisfies spec>
```

If the user omits any field, the macro fails to elaborate. The framework
enforces the discipline at the syntactic level.

## Why we need this — the four problems it prevents

This file goes to some length to explain WHY this complication is needed,
because the design decisions are subtle and non-obvious.

### Problem 1 — Body shape coupling (the `relation_from` story)

When a set is defined as a transparent `def` and downstream proofs reach
through the body to make progress (e.g., applying `uncurry_def` on a body that
happens to be an `uncurry` application), the proofs become coupled to the
specific syntactic shape of the body. Refactoring the body to a mathematically
equivalent form — say, replacing `uncurry P` with an existential set
comprehension — breaks every proof that took the body-shape shortcut.

The mathematical content of a set is its membership characterization
(its extension, by set extensionality). The body of a comprehension is just
one of many possible predicates with that extension. Two definitions with
different bodies but the same extension are the same set. Proofs that depend
on the body have leaked **representation** into their reasoning.

The discipline: proofs must reason against the **characterization theorem**,
not the body. The characterization is the API; the body is the implementation.

### Problem 2 — Specification is silently absent

When a set is defined by `def my_set : Set U := { x | body }`, the framework
records the *implementation* but not the *specification*. The specification is
expected to live nearby (e.g., in `Properties/`), but nothing forces the user
to write one. The discipline is conventional, not enforced — so it drifts.

The framework should require the specification AT THE DEFINITION SITE, in the
same syntactic block as the implementation, so it cannot be omitted.

### Problem 3 — Congruence verification can be bypassed

A `Set U` is a `CongruentUnaryPredicate U` — it carries both a predicate and a
congruence proof. The type system requires congruence; you cannot inhabit
`Set U` without it.

When a set is defined axiomatically (`axiom my_set : Set U` + `axiom my_set_def`),
the congruence proof is POSTULATED rather than VERIFIED. The framework trusts
the postulate. If the membership characterization in `_def` is not actually
congruent, the axioms together are INCONSISTENT — but Lean doesn't catch it,
because no congruence proof is ever written down.

When a set is defined via set comprehension, congruence is mechanically
verified at the definition site (either explicitly via `with <cong proof>` or
automatically via the auto-congruence CoeDep). The framework cannot be tricked.

The discipline: derived sets must be constructed via set comprehension, not
axiomatized. The construction path is the one that performs congruence
verification.

### Problem 4 — Spec and impl have different natural shapes

A characterization (specification) is naturally written in CONSTRUCTOR-PATTERN
form, quantifying over the components of an element:

  ∀ a b, (a ⋈ b) ∈ₛₑₜ R ↔ <condition on a and b>

A set comprehension predicate is necessarily written in ELEMENT-PATTERN form,
because the comprehension binder takes one variable for the whole element:

  { d | ∃ a b, d = (a ⋈ b) ∧ <condition on a and b> }

The existential in the comprehension is forced by the shape of the binder,
not by anything mathematical. As new projection operations become available
(say, `first : a ⋈ b → a` and `second : a ⋈ b → b`), the comprehension can
be rewritten without existentials:

  { d | <condition on first d and second d> }

This is a refactor of the implementation; the SPECIFICATION is unchanged
across both formulations. They name the same set.

The discipline: keep the specification stated in its natural mathematical form
(constructor-pattern, free of construction artifacts), and let the
implementation evolve over time as the construction toolkit grows.

## How the four problems are addressed

| Macro requirement       | Problem it prevents                                            |
|-------------------------|----------------------------------------------------------------|
| `impl` via set comprehension | (3) — congruence is mechanically verified                 |
| `spec` as separate proposition | (2) — specification cannot be silently omitted          |
| `proof` connecting them | (4) — bridges the shape gap between spec and impl              |
| `@[irreducible]` on def | (1) — downstream proofs cannot reach through the body          |

Each requirement is independently load-bearing. Dropping any one re-enables
a distinct failure mode.

## Why `@[irreducible]` is applied AFTER the theorem

The membership theorem (`<name>_def`) needs to see the body during its own
proof — `iterate h` and similar tactics rely on definitional equality between
the goal and the hypothesis, which is what unfolding the body enables.

Once the theorem is proven, we apply `@[irreducible]` to the def. From that
point on, no other code can unfold the body. The theorem becomes the only
visible interface.

This is the cleanest way to get the benefits of opacity without breaking the
proof itself.

-/

namespace Test.DefSet

open Logic
open Logic.PC₁
open Logic.ND
open Universe
open Universe.Sets

-- ═════════════════════════════════════════════════════════════════════════
-- # The macro
-- ═════════════════════════════════════════════════════════════════════════

-- Syntax: `defset <name> <binders>* : <type> where spec := _ impl := _ proof := _`
--
-- The macro emits three commands:
--   1. `def <name> <binders>* : <type> := <impl>`       — the implementation
--   2. `theorem <name>_def <binders>* : <spec> := <proof>` — the characterization
--   3. `attribute [irreducible] <name>`                  — lock in opacity

-- Prototype simplification: no binders for now — every defset takes only an
-- implicit Universal U. This avoids the macro parsing complexity around
-- bracketedBinder arrays for the prototype. The production version would
-- need to accept arbitrary binders.
--
-- We use `||spec:`, `||impl:`, `||proof:` as separators instead of `where ...`
-- to avoid clashing with Lean's `where` keyword in command contexts.

syntax (name := defsetCmd) "defset " ident " : " term " ||spec: " term " ||impl: " term " ||proof: " term : command

macro_rules
  | `(defset $name:ident : $type:term ||spec: $spec:term ||impl: $impl:term ||proof: $proof:term) => do
    let defNameStr := name.getId.toString
    let theoremIdent := Lean.mkIdent (Lean.Name.mkSimple (defNameStr ++ "_def"))
    -- Use unhygienic `U` so that the same `U` is visible to def, theorem,
    -- and the user-supplied spec/impl/proof (which all reference `U` literally).
    let uIdent := Lean.mkIdent `U
    `(def $name { $uIdent : Universal} : $type := $impl
      theorem $theoremIdent { $uIdent : Universal} : $spec := $proof
      attribute [irreducible] $name)

-- ═════════════════════════════════════════════════════════════════════════
-- # Example 1 — the trivial case
-- ═════════════════════════════════════════════════════════════════════════
--
-- The empty set: a case where impl and spec match almost trivially, so the
-- proof is mechanical.
--
-- Spec: ∀ x, x ∈ₛₑₜ my_empty_set ↔ False
-- Impl: { _ | False }
-- Proof: chain through mem_def to reduce both sides to .pred x ↔ False, which
--        is False ↔ False after the body reduces.

defset my_empty_set : Set U
  ||spec: ∀ x: U.Particular, x ∈ₛₑₜ my_empty_set ↔ False
  ||impl: { _ : U.Particular | False }
  ||proof: by forall_intro
    variable(a: U.Particular)
    have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ my_empty_set ↔ my_empty_set.pred x := by forall_elim mem_def, my_empty_set
    have h₂: a ∈ₛₑₜ my_empty_set ↔ my_empty_set.pred a := by forall_elim h₁, a
    -- my_empty_set.pred a reduces to False (the body of the comprehension)
    -- so the goal a ∈ₛₑₜ my_empty_set ↔ False follows from h₂
    have h₃: a ∈ₛₑₜ my_empty_set → False := by
      assume(h: a ∈ₛₑₜ my_empty_set)
      have h_b: my_empty_set.pred a := PC₀.deductive_eq_l2r h₂ h
      iterate h_b  -- my_empty_set.pred a is definitionally False
    have h₄: False → a ∈ₛₑₜ my_empty_set := by
      assume(h: False)
      have h_b: my_empty_set.pred a := by iterate h  -- False is definitionally my_empty_set.pred a
      have h_c: a ∈ₛₑₜ my_empty_set := PC₀.deductive_eq_r2l h₂ h_b
      iterate h_c
    have h₅: a ∈ₛₑₜ my_empty_set ↔ False := by iff_intro h₃, h₄
    iterate h₅

-- ═════════════════════════════════════════════════════════════════════════
-- # Verification of the discipline
-- ═════════════════════════════════════════════════════════════════════════

-- (a) The characterization theorem exists with the auto-generated name `_def`,
--     and its type is exactly the spec we wrote:
#check @my_empty_set_def
-- @my_empty_set_def : ∀ {U : Universal} (x : U.Particular), x ∈ₛₑₜ my_empty_set ↔ False

-- (b) After elaboration, my_empty_set has been marked @[irreducible].
--     Downstream code that wants to reason about membership in my_empty_set
--     must go through my_empty_set_def. The body is no longer the API.

-- ═════════════════════════════════════════════════════════════════════════
-- # What this prototype demonstrates and what remains for production
-- ═════════════════════════════════════════════════════════════════════════
--
-- Demonstrated:
--   1. The `defset` command parses three required fields (spec/impl/proof).
--   2. A missing field is a syntax error — the user CANNOT define a set
--      without supplying all three. The discipline is structural, not
--      conventional.
--   3. The auto-generated `<name>_def` theorem encodes the spec.
--   4. The def is marked @[irreducible] automatically.
--   5. The impl path goes through set comprehension, which performs
--      auto-congruence verification (the `False` predicate's congruence
--      came for free via the CoeDep auto-congruence mechanism).
--
-- Remaining for production:
--   a) Arbitrary binders. The prototype hard-codes `{U : Universal}`. The
--      production macro needs to accept `bracketedBinder*` and thread the
--      binders through both the def and the theorem. The Lean 4 antiquotation
--      syntax for variadic binders (`$binders:bracketedBinder*`) needs more
--      investigation — straightforward patterns failed in initial attempts.
--   b) Better separator syntax. The `||spec:` / `||impl:` / `||proof:` style
--      is functional but ugly. A `where ... spec := ... impl := ... proof := ...`
--      block would be cleaner; this requires resolving an interaction with
--      Lean's `where` keyword in command contexts.
--   c) Spec validation. Currently the spec is any `Prop` — the macro does not
--      enforce that it mentions the defined set or is of the form
--      `∀ ..., x ∈ₛₑₜ <name> ↔ <condition>`. A production version could lint
--      for this pattern.
--   d) Auto-naming flexibility. Currently the theorem is always named
--      `<name>_def`. Production may want a hook for custom names.
--
-- The non-trivial example (relation_from-style with pointwise spec on a
-- comprehension that uses existentials) is deliberately omitted from this
-- prototype because (a) it requires arbitrary binders to thread the binary
-- predicate parameter, and (b) the proof connecting existential impl to
-- pointwise spec involves dyad-equality decomposition that depends on
-- exhaustiveness — a real proof, worth doing once production binders work.

end Test.DefSet
