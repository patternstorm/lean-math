import Logic
import Universals.Sets
import Universals.Dyads

/-!
# Making `Set U` itself be the bundle — no coercion needed

## The clever insight

In `Test/DefSetStructure.lean`, we hit a coercion problem: a `DefinedSet U spec`
could not be implicitly coerced to a `Set U`, because the `spec` parameter
prevented Coe/CoeHead from identifying a unique target.

User's resolution: **stop treating `Set U` as one thing and `DefinedSet U` as
another.** What we currently call `Set U` is *not actually a set in the full
mathematical sense* — it's just the **extensional predicate**, the
"implementation" half of a set. A proper set is the bundle:

  - the extensional predicate (the implementation), AND
  - the membership specification (the characterization), AND
  - the proof connecting them.

If we redefine `Set U` to BE the bundle (renaming the current `Set U` to
something like `SetPredicate U` to acknowledge that it's not really a set yet),
then there is no coercion: any value of `Set U` is already a bundle, and `∈ₛₑₜ`
just looks through the bundle to the predicate.

## What needs to change in the framework

A full refactor would:

1. Define a new structure (the bundle) — directly over `CongruentUnaryPredicate U`,
   no intermediate alias:

       structure Sets.Defined (U : Universal) where
         extension : CongruentUnaryPredicate U          -- the predicate (= the OLD "Set U")
         spec      : CongruentUnaryPredicate U → Prop   -- the membership characterization
         proof     : spec extension                      -- proof discharges spec on extension

   The field is called `extension` because mathematically that's what it is —
   the set's extension (its members). Calling it `pred` would muddle the
   distinction between "the set's mathematical extension" and "the underlying
   predicate function" (`.pred` lives one level deeper, inside the
   `CongruentUnaryPredicate`).

2. Make `SetsUniversal U` have `Sets.Defined U` as its Particulars.

3. Redefine `∈ₛₑₜ` to project through `.extension.pred`:

       def mem (x : U.Particular) (S : Set U) : Prop := S.extension.pred x

   This is the "trick" with membership the user asked about. There are two
   projections now (`.extension` then `.pred`), versus one in the old framework
   (just `.pred`). The trick: define `mem` ONCE at the framework level and
   never let downstream code see the double indirection. Users keep writing
   `x ∈ₛₑₜ S` exactly as before — the framework absorbs the extra layer.

4. Set equality becomes extensional on `.extension` — two `Sets.Defined U`
   values are equal iff their underlying extensions (predicates) agree,
   regardless of `.spec`/`.proof`. The spec is mathematical METADATA: it
   documents how a set was characterized but does not affect identity.

5. Update `set_from`, the set comprehension macros, and `mem_def` /
   `not_mem_def` accordingly.

This file demonstrates step (1)-(3) in a small prototype to validate the idea.

## What's gained

- No coercion at use sites. `x ∈ₛₑₜ my_empty_set` works directly because
  `my_empty_set : Set U` and `Set U` already is the bundle.
- Spec/proof bundled with every set — discipline is structural, not
  bolt-on.
- The spec is visible as a field, available for inspection and use.
- Arbitrary parameters via plain function parameters — no macro complexity.

## What's lost

- Every set, even ad-hoc ones, must provide a spec and proof. There's no
  free `set_from P` that produces a "raw" set without discipline. (This may
  be a feature, not a bug — it forces every set to have a characterization.)
- Equality on sets requires care: extensional on `.pred`, ignoring `.spec`
  and `.proof`. This is mathematically correct (sets are their extensions)
  but adds a subtle invariant the framework must enforce.

## The prototype below

Implements `Sets.Defined U`, defines `mem`, and shows `my_empty_set` working
without coercion.
-/

namespace Test.DefSetUniversal

open Logic
open Logic.PC₁
open Logic.ND
open Universe
open Universe.Sets

-- ═════════════════════════════════════════════════════════════════════════
-- # The bundle
-- ═════════════════════════════════════════════════════════════════════════

-- The NEW Set U: a bundle of three pieces.
--
--   - `extension`: the extensional predicate — the set's mathematical
--     extension. This is what the old `Set U` was.
--   - `spec`: a pure `Prop` — the membership characterization. Written as a
--     universally quantified proposition with no free variables, of the form
--     `∀ x₁ ... xₙ, expr(x₁..xₙ) ∈ S ↔ P(x₁..xₙ)` (using predicate-level
--     `extension.pred` for the membership in the spec body).
--   - `proof`: a proof of the spec — its TYPE is precisely the spec field.
--
-- The spec is a real `Prop`, not a `... → Prop` function. It's a closed
-- proposition that mentions `extension` by name (Lean's structure construction
-- allows later fields to reference earlier ones). The proof's TYPE is then
-- exactly that proposition — your observation about the spec being "encoded"
-- in the proof type, realized concretely.

structure DefinedSet (U : Universal) where
  extension : CongruentUnaryPredicate U
  spec      : Prop
  proof     : spec

-- A convenience accessor that delegates `.pred` to the extension.
-- This is what lets the existing `mem_def` axiom keep working when `S` is a
-- `DefinedSet U` rather than a raw `CongruentUnaryPredicate U`: the axiom
-- says `x ∈ₛₑₜ S ↔ S.pred x`, and `S.pred` now means
-- `S.extension.pred` — the same predicate, just one projection deeper.

def DefinedSet.pred {U : Universal} (S : DefinedSet U) : U.Particular → Prop :=
  S.extension.pred

-- ═════════════════════════════════════════════════════════════════════════
-- # Membership: the existing axiom still works
-- ═════════════════════════════════════════════════════════════════════════
--
-- The framework already has:
--
--   axiom mem: U.Particular → Set U → Prop
--   axiom mem_def: ∀ S x, x ∈ₛₑₜ S ↔ S.pred x
--
-- Question: does this still work when `Set U = DefinedSet U`?
--
-- Answer: yes, as long as `S.pred x` resolves correctly for `S : DefinedSet U`.
-- Lean's dot notation will look up `.pred` on the structure type:
--   - If `pred` is a field, use that.
--   - If `pred` is a function `DefinedSet U → ...`, use that.
--
-- We've defined `DefinedSet.pred` above (a function from `DefinedSet U` to
-- `U.Particular → Prop`), so `S.pred x` works on a `DefinedSet U` and resolves
-- to `S.extension.pred x` — the underlying predicate's pred at x. The axiom
-- `mem_def : x ∈ₛₑₜ S ↔ S.pred x` continues to typecheck unchanged.
--
-- A small simulation of `mem_def` to demonstrate the relationship:

-- A "fake" mem_def for the prototype (in production, this is the real axiom):
axiom mem' {U : Universal} : U.Particular → DefinedSet U → Prop
axiom mem_def' {U : Universal} : ∀ (S : DefinedSet U), ∀ (x : U.Particular),
  mem' x S ↔ S.pred x   -- S.pred resolves via DefinedSet.pred → S.extension.pred

infix:50 " ∈ₛₑₜ' " => mem'

-- ═════════════════════════════════════════════════════════════════════════
-- # Example: my_empty_set — directly a `DefinedSet U`
-- ═════════════════════════════════════════════════════════════════════════
--
-- Spec is a closed `Prop`: ∀ x, x is in the extension ↔ False.
-- The spec references `extension` (an earlier field) directly via `.pred`.

-- We `let`-bind the extension before constructing the bundle so that the spec
-- can reference it by name. Lean's structure-construction syntax does NOT
-- bring earlier field names into scope on the right-hand side of later fields,
-- so we bind the extension as a local term first.

def my_empty_set {U : Universal} : DefinedSet U :=
  let ext : CongruentUnaryPredicate U := { _ : U.Particular | False }
  let spec: Prop := ∀ x : U.Particular, ext.pred x ↔ False
  let proof: ∀ x : U.Particular, ext.pred x ↔ False := by forall_intro
      variable(a: U.Particular)
      have h₃: ext.pred a → False := by
        assume(h: ext.pred a)
        iterate h
      have h₄: False → ext.pred a := by
        assume(h: False)
        iterate h
      have h₅: ext.pred a ↔ False := by iff_intro h₃, h₄
      iterate h₅
  {
    extension := ext
    spec      := spec
    proof     := proof
  }

-- ═════════════════════════════════════════════════════════════════════════
-- # Verifying the design
-- ═════════════════════════════════════════════════════════════════════════

-- (a) `my_empty_set.spec` is a `Prop` (the user's preference):
#check @my_empty_set.spec
-- @my_empty_set.spec : Prop

-- (b) `my_empty_set.proof` has type EXACTLY equal to `my_empty_set.spec`:
#check @my_empty_set.proof
-- @my_empty_set.proof : my_empty_set.spec

-- (c) Crucially, `.pred` resolves on `DefinedSet` (delegating to extension):
#check @my_empty_set.pred
-- @my_empty_set.pred : U.Particular → Prop

-- (d) The existing `mem_def` shape continues to work — `S.pred x` typechecks
--     on a `DefinedSet U`, so axioms phrased that way carry over unchanged:
example {U : Universal} (x : U.Particular) :
    x ∈ₛₑₜ' my_empty_set ↔ my_empty_set.pred x :=
  mem_def' my_empty_set x

-- (e) No coercion needed at any use site — `my_empty_set` IS a Set in the new
--     universe (DefinedSet is the Particular type of SetsUniversal).
example {U : Universal} (x : U.Particular) : Prop := x ∈ₛₑₜ' my_empty_set

-- ═════════════════════════════════════════════════════════════════════════
-- # Example 2: a non-trivial constructor-pattern spec (relation_from)
-- ═════════════════════════════════════════════════════════════════════════
--
-- This is the canonical case where the spec has a structurally DIFFERENT
-- shape than the implementation predicate.
--
--   - spec (constructor-pattern, mathematical):
--       ∀ a b, ext.pred (a ⋈ b) ↔ (P.pred a).pred b
--
--   - impl (element-pattern, forced by the comprehension binder):
--       fun d => ∃ a b, d =ₗₓₗ (a ⋈ b) ∧ (P.pred a).pred b
--
-- The implementation uses existentials because set comprehension takes one
-- variable (`d`) for the whole element. The spec uses constructor pattern
-- because that's the natural mathematical statement: "(a ⋈ b) is in the set
-- iff P holds of a and b."
--
-- The proof bridges the two shapes — exactly the non-trivial work that the
-- `defset` discipline forces the user to do ONCE, at the definition site.

open Universe
open Universe.Dyads
open Logic.ND
open Logic.PC₁

def my_relation_from {U₁ U₂ : Universal} (P : CongruentBinaryPredicate U₁ U₂) :
    DefinedSet (U₁ ⧓ U₂) :=
  let ext : CongruentUnaryPredicate (U₁ ⧓ U₂) :=
    { d : (U₁ ⧓ U₂).Particular | ∃ a : U₁.Particular, ∃ b : U₂.Particular,
        d =₍(U₁ ⧓ U₂)₎ (a ⋈ b) ∧ (P.pred a).pred b }
  let spec : Prop :=
    ∀ a : U₁.Particular, ∀ b : U₂.Particular,
      ext.pred (a ⋈ b) ↔ (P.pred a).pred b
  let proof : spec := by
    forall_intro
    variable(a₀ : U₁.Particular)
    variable(b₀ : U₂.Particular)
    -- Forward: ext.pred (a₀ ⋈ b₀) → (P.pred a₀).pred b₀
    have fwd : ext.pred (a₀ ⋈ b₀) → (P.pred a₀).pred b₀ := by
      assume(h : ext.pred (a₀ ⋈ b₀))
      -- h : ∃ a b, (a₀⋈b₀) =ₗₓₗ (a⋈b) ∧ (P.pred a).pred b
      have ⟨(a₁ : U₁.Particular), (h₁ : ∃ b : U₂.Particular,
              (a₀ ⋈ b₀) =ₗₓₗ (a₁ ⋈ b) ∧ (P.pred a₁).pred b)⟩ := exists_elim h
      have ⟨(b₁ : U₂.Particular), (h₂ : (a₀ ⋈ b₀) =ₗₓₗ (a₁ ⋈ b₁) ∧ (P.pred a₁).pred b₁)⟩ :=
        exists_elim h₁
      have h_eq : (a₀ ⋈ b₀) =ₗₓₗ (a₁ ⋈ b₁) := by and_elim h₂
      have h_p  : (P.pred a₁).pred b₁ := by and_elim h₂
      -- Decompose dyad equality
      have h_iff : (a₀ ⋈ b₀) =ₗₓₗ (a₁ ⋈ b₁) ↔ a₀ =₍U₁₎ a₁ ∧ b₀ =₍U₂₎ b₁ := by
        forall_elim eq_def, a₀, b₀, a₁, b₁
      have h_eqs : a₀ =₍U₁₎ a₁ ∧ b₀ =₍U₂₎ b₁ := PC₀.deductive_eq_l2r h_iff h_eq
      have h_a   : a₀ =₍U₁₎ a₁ := by and_elim h_eqs
      have h_b   : b₀ =₍U₂₎ b₁ := by and_elim h_eqs
      -- Transport via P's cong: outer (in a) then inner (in b)
      -- P.cong gives: x =₍U₁₎ y → ∀ z, (P.pred x).pred z ↔ (P.pred y).pred z
      have h_outer_iff : (P.pred a₀).pred b₁ ↔ (P.pred a₁).pred b₁ := by
        forall_elim P.cong, a₀, a₁, b₁, h_a
      have h_p' : (P.pred a₀).pred b₁ := PC₀.deductive_eq_r2l h_outer_iff h_p
      -- Now use inner cong: b₀ =₍U₂₎ b₁ → (P.pred a₀).pred b₀ ↔ (P.pred a₀).pred b₁
      have h_inner_iff : (P.pred a₀).pred b₀ ↔ (P.pred a₀).pred b₁ := by
        forall_elim (P.pred a₀).cong, b₀, b₁, h_b
      have h_p'' : (P.pred a₀).pred b₀ := PC₀.deductive_eq_r2l h_inner_iff h_p'
      iterate h_p''
    -- Backward: (P.pred a₀).pred b₀ → ext.pred (a₀ ⋈ b₀)
    have bwd : (P.pred a₀).pred b₀ → ext.pred (a₀ ⋈ b₀) := by
      assume(h : (P.pred a₀).pred b₀)
      -- Provide witnesses a₀, b₀
      have h_refl : (a₀ ⋈ b₀) =ₗₓₗ (a₀ ⋈ b₀) := by forall_elim eq_refl, (a₀ ⋈ b₀)
      have h_and  : (a₀ ⋈ b₀) =ₗₓₗ (a₀ ⋈ b₀) ∧ (P.pred a₀).pred b₀ := by and_intro h_refl, h
      have h_exb  : ∃ b : U₂.Particular, (a₀ ⋈ b₀) =ₗₓₗ (a₀ ⋈ b) ∧ (P.pred a₀).pred b := by
        exists_intro h_and, b₀
      have h_exa  : ∃ a : U₁.Particular, ∃ b : U₂.Particular,
                      (a₀ ⋈ b₀) =ₗₓₗ (a ⋈ b) ∧ (P.pred a).pred b := by
        exists_intro h_exb, a₀
      iterate h_exa
    have h_iff : ext.pred (a₀ ⋈ b₀) ↔ (P.pred a₀).pred b₀ := by iff_intro fwd, bwd
    iterate h_iff
  {
    extension := ext
    spec      := spec
    proof     := proof
  }

-- Verify the types:
#check @my_relation_from
-- @my_relation_from : ∀ {U₁ U₂ : Universal}, CongruentBinaryPredicate U₁ U₂ → DefinedSet (U₁ ⧓ U₂)

-- The .spec accessor requires an applied value, since my_relation_from is a function:
example {U₁ U₂ : Universal} (P : CongruentBinaryPredicate U₁ U₂) : Prop := (my_relation_from P).spec
-- The spec for any given P is `∀ a b, ext.pred (a ⋈ b) ↔ (P.pred a).pred b` —
-- a closed Prop with universal binders covering everything.

-- ═════════════════════════════════════════════════════════════════════════
-- # What this prototype demonstrates (and what it doesn't)
-- ═════════════════════════════════════════════════════════════════════════
--
-- Demonstrates:
--   - The structure approach works without a coercion.
--   - The spec naturally lives in the bundle as a field — no macro needed.
--   - Parameters can be threaded as plain function parameters (would be
--     shown in a relation_from example).
--   - The membership operator projects through `.pred` cleanly.
--
-- Does NOT demonstrate (requires the full framework refactor):
--   - Replacing the existing `Set U` in `Universals.Sets.Universal` —
--     this is the meat of the change.
--   - Defining `SetsUniversal U` with `DefinedSet U` as Particulars,
--     including extensional equality on `.pred`.
--   - Updating `set_from`, set comprehension macros, `mem_def`, etc.
--   - Migrating every existing set definition to the new pattern.
--
-- This is a significant refactor, but the design is now coherent: there's
-- no impedance mismatch, no coercion friction, and the discipline is
-- structural.

end Test.DefSetUniversal
