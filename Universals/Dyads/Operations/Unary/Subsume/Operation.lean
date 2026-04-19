import Universe
import Logic
import Universals.Dyads.Universal

/-!
# Subsume — the dyad lift operation

Given sub-universal embeddings `e₁: U₁' <: U₁` and `e₂: U₂' <: U₂`, the
`subsume` operation lifts a dyad `(a' ⋈ b') ∈ U₁' ⧓ U₂'` into the dyad
`(e₁ a' ⋈ e₂ b') ∈ U₁ ⧓ U₂`. It is the canonical way to propagate
sub-universal relations through the dyad constructor.

## Construction — following the new UnaryOperation pattern

1. `subsume_of e₁ e₂ d'` — the CongruentUnaryPredicate on `(U₁ ⧓ U₂)` that
   fixes the domain dyad `d'` and tests whether a given `d` is the subsume
   image of `d'`. Built per the domain-first currying rule: fixed parameter
   `d'` sits on the left of `=ₗₓₗ`, the test variable `d` sits on the left
   of its own `=ₗₓₗ` with the image dyad on the right.
2. `subsume_ext e₁ e₂` — bundles `subsume_of` into a CongruentBinaryPredicate,
   the graph (extension) of the operation.
3. `subsume_sym` / `subsume_def` — postulated function symbol and the
   defining axiom referring to `subsume_ext`.
4. `subsume e₁ e₂` — the bundled `UnaryOperation (U₁' ⧓ U₂') ⟴ (U₁ ⧓ U₂)`.
-/

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- ------------------------
-- TODO: move the extension predicate to Predicates folder
-- ------------------------

-- # Subsume — fixed-left unary predicate
-- Fix a domain dyad `d'` and test whether `d` is the subsume image of `d'`.
-- Follows the domain-first rule (docs/design/conguent-predicates.md): the
-- fixed parameter `d'` is on the left of `=ₗₓₗ (a' ⋈ b')`.
--
-- Proof by Claude Opus 4.7, 2026-04-19
-- ------------------------
-- TODO: fix (X ⧓ Y).Particular to (X ⋈ Y)
-- ------------------------
noncomputable def subsume_of {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂) (d': (U₁' ⧓ U₂').Particular): CongruentUnaryPredicate (U₁ ⧓ U₂) :=
  let pred: (U₁ ⧓ U₂).Particular → Prop := (d: (U₁ ⧓ U₂).Particular ↦ ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))
  let cong: ∀ (d₁: (U₁ ⧓ U₂).Particular), ∀ (d₂: (U₁ ⧓ U₂).Particular), d₁ =ₗₓₗ d₂ → (pred d₁ ↔ pred d₂) := by forall_intro
    variable(d₁: (U₁ ⧓ U₂).Particular)
    variable(d₂: (U₁ ⧓ U₂).Particular)
    assume(h₀: d₁ =ₗₓₗ d₂)
    -- Forward: from a witness for d₁, build a witness for d₂ by chaining d₂ =ₗₓₗ d₁ =ₗₓₗ image.
    -- ------------------------
    -- TODO: fix clauses naming and variable naming -> too many primas
    -- ------------------------
    have fwd: pred d₁ → pred d₂ := by
      assume(h₁: pred d₁)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular),
        d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃:
        d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁ =ₗₓₗ d₂ → d₂ =ₗₓₗ d₁ := by forall_elim eq_sym, d₁, d₂
      have h₇: d₂ =ₗₓₗ d₁ := by modus_ponens h₆, h₀
      have h₈: d₂ =ₗₓₗ d₁ ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₇, h₅
      have h₉: d₂ =ₗₓₗ d₁ ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') →
        d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
          forall_elim eq_trans, d₂, d₁, (e₁.embedding a' ⋈ e₂.embedding b')
      have h₁₀: d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by modus_ponens h₉, h₈
      have h₁₁: d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
        and_intro h₄, h₁₀
      have h₁₂: ∃ (b'': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b'') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by exists_intro h₁₁, b'
      have h₁₃: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular), d' =ₗₓₗ (a'' ⋈ b'') ∧ d₂ =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by exists_intro h₁₂, a'
      iterate h₁₃
    -- Backward: symmetric, using d₁ =ₗₓₗ d₂ directly with transitivity.
    have bwd: pred d₂ → pred d₁ := by
      assume(h₁: pred d₂)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃: d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁ =ₗₓₗ d₂ ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₀, h₅
      have h₇: d₁ =ₗₓₗ d₂ ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') →
        d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
          forall_elim eq_trans, d₁, d₂, (e₁.embedding a' ⋈ e₂.embedding b')
      have h₈: d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by modus_ponens h₇, h₆
      have h₉: d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
        and_intro h₄, h₈
      have h₁₀: ∃ (b'': U₂'.Particular),
        d' =ₗₓₗ (a' ⋈ b'') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by
          exists_intro h₉, b'
      have h₁₁: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular),
        d' =ₗₓₗ (a'' ⋈ b'') ∧ d₁ =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by
          exists_intro h₁₀, a'
      iterate h₁₁
    have result: pred d₁ ↔ pred d₂ := by iff_intro fwd, bwd
    iterate result
  { pred := pred, cong := cong }

-- # Subsume extension — the CongruentBinaryPredicate graph
-- Bundles `subsume_of` as a binary graph `(U₁' ⧓ U₂') → CongruentUnaryPredicate (U₁ ⧓ U₂)`.
-- Outer congruence: if two domain dyads are equal, they have the same subsume image (up to =ₗₓₗ),
-- proved by chaining =ₗₓₗ on the first existential conjunct.
--
-- Proof by Claude Opus 4.7, 2026-04-19
noncomputable def subsume_ext {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): CongruentBinaryPredicate (U₁' ⧓ U₂') (U₁ ⧓ U₂) :=
  let pred: (U₁' ⧓ U₂').Particular → CongruentUnaryPredicate (U₁ ⧓ U₂) := (d': (U₁' ⧓ U₂').Particular ↦ subsume_of e₁ e₂ d')
  let cong: ∀ (d₁': (U₁' ⧓ U₂').Particular), ∀ (d₂': (U₁' ⧓ U₂').Particular), ∀ (d: (U₁ ⧓ U₂).Particular), d₁' =ₗₓₗ d₂' → ((pred d₁').pred d ↔ (pred d₂').pred d) := by forall_intro
    variable(d₁': (U₁' ⧓ U₂').Particular)
    variable(d₂': (U₁' ⧓ U₂').Particular)
    variable(d: (U₁ ⧓ U₂).Particular)
    assume(h₀: d₁' =ₗₓₗ d₂')
    -- Forward: replace d₁' with d₂' inside the first conjunct by sym + trans.
    -- ------------------------
    -- TODO: fix clauses naming and variable naming -> too many primas
    -- ------------------------
    have fwd: (pred d₁').pred d → (pred d₂').pred d := by
      assume(h₁: (pred d₁').pred d)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d₁' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃: d₁' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d₁' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁' =ₗₓₗ d₂' → d₂' =ₗₓₗ d₁' := by forall_elim eq_sym, d₁', d₂'
      have h₇: d₂' =ₗₓₗ d₁' := by modus_ponens h₆, h₀
      have h₈: d₂' =ₗₓₗ d₁' ∧ d₁' =ₗₓₗ (a' ⋈ b') := by and_intro h₇, h₄
      have h₉: d₂' =ₗₓₗ d₁' ∧ d₁' =ₗₓₗ (a' ⋈ b') → d₂' =ₗₓₗ (a' ⋈ b') := by forall_elim eq_trans, d₂', d₁', (a' ⋈ b')
      have h₁₀: d₂' =ₗₓₗ (a' ⋈ b') := by modus_ponens h₉, h₈
      have h₁₁: d₂' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₁₀, h₅
      have h₁₂: ∃ (b'': U₂'.Particular), d₂' =ₗₓₗ (a' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by exists_intro h₁₁, b'
      have h₁₃: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular), d₂' =ₗₓₗ (a'' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by exists_intro h₁₂, a'
      iterate h₁₃
    -- Backward: use d₁' =ₗₓₗ d₂' directly with transitivity.
    have bwd: (pred d₂').pred d → (pred d₁').pred d := by
      assume(h₁: (pred d₂').pred d)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d₂' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃: d₂' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d₂' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁' =ₗₓₗ d₂' ∧ d₂' =ₗₓₗ (a' ⋈ b') := by and_intro h₀, h₄
      have h₇: d₁' =ₗₓₗ d₂' ∧ d₂' =ₗₓₗ (a' ⋈ b') → d₁' =ₗₓₗ (a' ⋈ b') := by forall_elim eq_trans, d₁', d₂', (a' ⋈ b')
      have h₈: d₁' =ₗₓₗ (a' ⋈ b') := by modus_ponens h₇, h₆
      have h₉: d₁' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₈, h₅
      have h₁₀: ∃ (b'': U₂'.Particular), d₁' =ₗₓₗ (a' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by exists_intro h₉, b'
      have h₁₁: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular), d₁' =ₗₓₗ (a'' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by exists_intro h₁₀, a'
      iterate h₁₁
    have result: (pred d₁').pred d ↔ (pred d₂').pred d := by iff_intro fwd, bwd
    iterate result
  { pred := pred, cong := cong }

-- # Subsume operation symbol
-- Parameterized by two sub-universal embeddings. Not a plain UnaryOperation axiom, but a schema of axioms —
-- we cannot use the `unary_operation` macro because the signature depends on e₁ and e₂.
-- Follows the three-step manual pattern from Logic/PredicateCalculus/Schemas/Operations/Unary/Schema.lean.
axiom subsume_sym {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): (U₁' ⧓ U₂').Particular → (U₁ ⧓ U₂).Particular

-- # Subsume defining axiom — referring to the extension
axiom subsume_def {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂):
  ∀ (x: (U₁' ⧓ U₂').Particular), ∀ (y: (U₁ ⧓ U₂).Particular), (subsume_sym e₁ e₂ x =ₗₓₗ y) ↔ ((subsume_ext e₁ e₂).pred x).pred y

-- # Subsume — the bundled UnaryOperation
noncomputable def subsume {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): (U₁' ⧓ U₂') ⟴ (U₁ ⧓ U₂) :=
  { ext := subsume_ext e₁ e₂,
    op := subsume_sym e₁ e₂,
    «def» := subsume_def e₁ e₂ }

end Dyads
end Universe
