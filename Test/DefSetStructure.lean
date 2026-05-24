import Logic
import Universals.Sets

/-!
# `DefinedSet` — Structure-based alternative to the `defset` macro

## What this prototype demonstrates

A different approach to the spec/impl/proof discipline: instead of a macro that
emits separate declarations, use a single **structure** whose fields are the
specification, the implementation, and the proof. The user defines a set by
inhabiting this structure.

```
structure DefinedSet (U : Universal) (spec : Set U → Prop) where
  set : Set U
  proof : spec set
```

The specification `spec` is part of the structure's **type parameter** — so it
shows up in every signature mentioning the set, and a definition cannot omit it.
The `proof` field discharges the obligation that the implementation satisfies
the specification. The `set` field is the implementation.

## Why this might be better than the macro

The macro prototype hit several limitations:
1. Accepting arbitrary `bracketedBinder*` was non-trivial — initial attempts
   tripped over Lean 4's antiquotation rules for variadic binders.
2. Macro hygiene required an unhygienic `U` identifier to make spec/impl/proof
   see the same universal — a small workaround that doesn't scale to multiple
   universal parameters.
3. Multi-line proof bodies interact awkwardly with multi-line command syntax.
4. Custom syntax to learn (`||spec:`, `||impl:`, `||proof:`).

The structure approach side-steps all of these:
1. Arbitrary parameters via function parameters of the enclosing `def`.
2. No macros, no hygiene, no antiquotation puzzles.
3. The proof is a regular Lean term/tactic block — no interaction with command
   syntax.
4. Pure Lean — no new syntax.

## Why this is still strong discipline

The structure has three fields. Lean's type system refuses to construct a
`DefinedSet U spec` without all three. Forgetting the proof, the spec, or
the implementation is a type error, not a convention violation.

The spec lives in the structure's **type parameter** (`spec : Set U → Prop`),
not as a regular field. This is significant:

  - Every signature `DefinedSet U spec` mentions the spec by reference. You
    can't define a `DefinedSet` whose spec is opaque to its callers — the
    callers SEE the spec in the type.
  - The spec is data the framework can *talk about*. Theorems can mention
    `DefinedSet.spec`. Two `DefinedSet U spec` values are guaranteed to
    satisfy the same spec.

The macro approach has analogous discipline (the auto-generated theorem
documents the spec), but the structure approach makes it part of the type
system rather than convention + macro.

## Tradeoffs versus the macro

| Property | Macro | Structure |
|---|---|---|
| **Returns a `Set U`** | Yes (via `def`) | Indirect (via `.set` field or coercion) |
| **Spec in signature** | No (separate `_def` theorem) | Yes (type parameter) |
| **Arbitrary parameters** | Hard (binders) | Trivial (function params) |
| **Uses Lean infrastructure** | Custom syntax + macros | Plain structures + coercions |
| **Downstream call site** | `(my_set)`, `my_set_def` | `(my_set : Set U)`, `my_set.proof` |
| **Opacity of body** | `@[irreducible]` on def | `@[irreducible]` on outer def |

The structure approach trades a small ergonomic indirection (`.set` / coercion,
`.proof`) for substantially less machinery and natural parameter handling.

## What's NOT shown here

We don't yet show:
- The relation_from-style example with existential impl / pointwise spec —
  the proof requires dyad-equality decomposition that doesn't fit in a
  prototype's scope.
- Coercion ergonomics in practice — whether `(my_set : Set U)` is clean enough
  or whether it adds friction in long proof chains.
- Interaction with `@[irreducible]` and how it propagates through field
  projections.

These are the questions to investigate next, before choosing macro vs structure
for production.
-/

namespace Test.DefSetStructure

open Logic
open Logic.PC₁
open Logic.ND
open Universe
open Universe.Sets

-- ═════════════════════════════════════════════════════════════════════════
-- # The structure
-- ═════════════════════════════════════════════════════════════════════════

-- A defined set bundles three things:
--   1. `set` — the implementation (a Set U built via set comprehension)
--   2. `proof` — the obligation that the implementation satisfies the spec
--
-- The spec itself lives in the structure's type parameter, so it is visible
-- in every signature that mentions DefinedSet.

structure DefinedSet (U : Universal) (spec : Set U → Prop) where
  set : Set U
  proof : spec set

-- Coercion attempt: a DefinedSet should ideally be usable wherever a Set is
-- expected, via implicit coercion. The straightforward Coe/CoeHead instances
-- do NOT work because `spec` is an implicit parameter that Lean cannot
-- determine from the source type alone — the instance lacks concrete
-- out-params.
--
-- Two paths to explore:
--   1. Use CoeDep, which can take the specific value into account.
--   2. Accept that the user writes `.set` explicitly. This makes the
--      structure approach less ergonomic at every use site.
--
-- For now we expose `.set` explicitly and document the issue.

instance {U : Universal} {spec : Set U → Prop} (ds : DefinedSet U spec) :
    CoeDep (DefinedSet U spec) ds (Set U) where
  coe := ds.set

-- ═════════════════════════════════════════════════════════════════════════
-- # Example 1 — the trivial case (empty set)
-- ═════════════════════════════════════════════════════════════════════════

-- The spec is a predicate over sets: "a set S is the empty set iff its
-- members are exactly those satisfying False". This is a function
-- Set U → Prop, written as a fun.
--
-- The implementation goes through set comprehension, so congruence is
-- mechanically verified.
--
-- The proof shows that for our specific implementation, the spec holds.

def my_empty_set {U : Universal} :
    DefinedSet U (fun S => ∀ x : U.Particular, x ∈ₛₑₜ S ↔ False) := {
  set := { _ : U.Particular | False }
  proof := by forall_intro
    variable(a: U.Particular)
    have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ ({ _ : U.Particular | False } : Set U) ↔ ({ _ : U.Particular | False } : Set U).pred x := by forall_elim mem_def, ({ _ : U.Particular | False } : Set U)
    have h₂: a ∈ₛₑₜ ({ _ : U.Particular | False } : Set U) ↔ ({ _ : U.Particular | False } : Set U).pred a := by forall_elim h₁, a
    have h₃: a ∈ₛₑₜ ({ _ : U.Particular | False } : Set U) → False := by
      assume(h: a ∈ₛₑₜ ({ _ : U.Particular | False } : Set U))
      have h_b: ({ _ : U.Particular | False } : Set U).pred a := PC₀.deductive_eq_l2r h₂ h
      iterate h_b
    have h₄: False → a ∈ₛₑₜ ({ _ : U.Particular | False } : Set U) := by
      assume(h: False)
      have h_b: ({ _ : U.Particular | False } : Set U).pred a := by iterate h
      have h_c: a ∈ₛₑₜ ({ _ : U.Particular | False } : Set U) := PC₀.deductive_eq_r2l h₂ h_b
      iterate h_c
    have h₅: a ∈ₛₑₜ ({ _ : U.Particular | False } : Set U) ↔ False := by iff_intro h₃, h₄
    iterate h₅
}

-- ═════════════════════════════════════════════════════════════════════════
-- # Verification of the discipline
-- ═════════════════════════════════════════════════════════════════════════

-- (a) The spec is in the TYPE — visible in any signature mentioning my_empty_set.
#check @my_empty_set
-- @my_empty_set : {U : Universal} → DefinedSet U fun S => ∀ (x : U.Particular), x ∈ₛₑₜ S ↔ False

-- (b) The proof is accessible as a field; it has the type the spec demands.
#check @my_empty_set.proof
-- @my_empty_set.proof : ∀ {U : Universal} (x : U.Particular), x ∈ₛₑₜ my_empty_set.set ↔ False

-- (c) Coercion to Set U via CoeDep — works once U is concretely applied.
example {U : Universal} : Set U := (@my_empty_set U : Set U)

-- Without explicit U, coercion fails because Lean cannot determine the
-- metavariable for the implicit universal before searching for the coercion
-- instance:
--   example {U : Universal} : Set U := my_empty_set  -- ERROR: type mismatch
--
-- This is a real ergonomic cost. Direct field access avoids it:
example {U : Universal} : Set U := my_empty_set.set

-- ═════════════════════════════════════════════════════════════════════════
-- # Comparison with the macro approach
-- ═════════════════════════════════════════════════════════════════════════
--
-- The macro version:
--   defset my_empty_set : Set U
--     ||spec: ∀ x, x ∈ₛₑₜ my_empty_set ↔ False
--     ||impl: { _ : U.Particular | False }
--     ||proof: <proof>
-- emits:
--   def my_empty_set : Set U := <impl>
--   theorem my_empty_set_def : <spec> := <proof>
--
-- The structure version:
--   def my_empty_set : DefinedSet U (fun S => ∀ x, x ∈ₛₑₜ S ↔ False) := {
--     set := <impl>
--     proof := <proof>
--   }
--   -- (the spec is in the type, no separate theorem needed)
--
-- In the structure version, downstream code that wants the characterization
-- writes `my_empty_set.proof` — this IS the characterization theorem,
-- automatically named, automatically typed by the spec parameter. No macro
-- needed to generate the name; the field projection IS the name.
--
-- The set itself is accessed via coercion (or `.set` explicitly). This is
-- the only ergonomic cost of the structure approach.
--
-- ## Open questions for production choice
--
-- 1. Does the `.set` / coercion indirection cause friction in long proofs?
--    The macro approach's `my_set` is directly a Set, with no projection.
--
-- 2. Can we make the structure approach work with `@[irreducible]` on the
--    set? Right now `my_empty_set.set` is transparent — downstream could
--    reach through `my_empty_set.set` to its body. To enforce opacity, we
--    might need `@[irreducible]` on the def itself, or use `opaque`.
--
-- 3. How does this scale to set-returning operations with many parameters
--    (like correspondences taking a relation)? Conceptually it's just
--    function parameters, so it should be fine — but worth confirming
--    with a real example.

end Test.DefSetStructure
