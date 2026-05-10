import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Predicate Curry
-- Axiom scheme: for any unary predicate P on a Dyad, there exists a binary predicate
-- on its relata — called `curry P` — such that saying something about the dyad
-- (P (a ⋈ b)) is the same as saying it about a and b separately (curry P a b).
-- Whatever is true of the dyad is true of the pair, and vice versa. Curry just
-- changes the syntactic form — from one placeholder to two — without changing
-- what's being asserted.
--
-- Each concrete unary predicate P generates one instance of this axiom scheme.
-- P is a metavariable ranging over predicate symbols, not a second-order quantification.
--
-- The name "curry" is borrowed from function theory, but here it operates on
-- statement templates, not functions.
--
-- Predicate curry is the inverse of predicate uncurry: together they establish that
-- saying something about a and b separately and saying it about their dyad a ⋈ b
-- are interchangeable forms of the same assertion.
--
-- Predicate curry must be postulated as an axiom scheme rather than proved via
-- lambda abstraction — see README.md § "Variable-Arity Predicates" for why.
--
-- Higher arities compose: for a unary predicate on U₁ ⋈ (U₂ ⋈ U₃), curry once to get
-- a binary predicate on U₁ and U₂ ⋈ U₃, then curry the second argument again to get
-- a ternary predicate on U₁, U₂, U₃. The same two axiom schemes handle any arity.
--
-- This is a conservative definitional extension: it introduces a new predicate symbol
-- defined by equivalence, adding no new theorems in the old language.
--
-- P is a named parameter (not universally quantified) because this is an axiom scheme:
-- each concrete P generates one instance.
axiom curry {U₁: Universal} {U₂: Universal} (P: U₁ ⋈ U₂ → Prop): U₁.Particular → U₂.Particular → Prop
axiom curry_def {U₁: Universal} {U₂: Universal} (P: U₁ ⋈ U₂ → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), (curry P) a b ↔ P (a ⋈ b)

-- # Curry Reducible Rule
-- Reducible version of curry for type class resolution. Lean unfolds this during
-- instance search, enabling automatic congruence inference for partial application
-- of curried predicates on dyads (e.g., fun y => R.pred (a ⋈ y)).
-- The axiomatic curry above remains the canonical definition for proofs.
@[reducible] def curry_reducicle_def_left {U₁: Universal} {U₂: Universal} (P: U₁ ⋈ U₂ → Prop):
  U₁.Particular → U₂.Particular → Prop := (a: U₁.Particular, b: U₂.Particular ↦ P (a ⋈ b))

-- # Curry Fiber
-- For a congruent unary predicate R on dyads, fixing the first relatum a
-- yields a congruent unary predicate on the second universal: (b ↦ R.pred (a ⋈ b)).
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
def curry_fiber_left {U₁ U₂: Universal} (R: CongruentUnaryPredicate (U₁ ⧓ U₂)) (a: U₁.Particular): CongruentUnaryPredicate U₂ :=
  let pred: U₂.Particular → Prop := (b: U₂.Particular ↦ R.pred (a ⋈ b))
  let cong: ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
      b₁ =₍U₂₎ b₂ → (R.pred (a ⋈ b₁) ↔ R.pred (a ⋈ b₂)) := by forall_intro
    variable(b₁: U₂.Particular)
    variable(b₂: U₂.Particular)
    assume(h₁: b₁ =₍U₂₎ b₂)
    have h₂: a =₍U₁₎ a := U₁.eq.refl a
    have h₃: a =₍U₁₎ a ∧ b₁ =₍U₂₎ b₂ := by and_intro h₂, h₁
    have h₄: (a ⋈ b₁) =ₗₓₗ (a ⋈ b₂) ↔ a =₍U₁₎ a ∧ b₁ =₍U₂₎ b₂ := by forall_elim eq_def, a, b₁, a, b₂
    have h₅: (a ⋈ b₁) =ₗₓₗ (a ⋈ b₂) := PC₀.deductive_eq_r2l h₄ h₃
    have h₆: (a ⋈ b₁) =ₗₓₗ (a ⋈ b₂) → (R.pred (a ⋈ b₁) ↔ R.pred (a ⋈ b₂)) := by forall_elim R.cong, (a ⋈ b₁), (a ⋈ b₂)
    have h₇: R.pred (a ⋈ b₁) ↔ R.pred (a ⋈ b₂) := by modus_ponens h₆, h₅
    iterate h₇
  { pred := pred, cong := cong }

-- # Congruent Binary for curried predicates
-- A congruent unary predicate on dyads, when curried, is a congruent binary predicate.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
def curry_cong {U₁ U₂: Universal} (R: CongruentUnaryPredicate (U₁ ⧓ U₂)): CongruentBinaryPredicate U₁ U₂ :=
  let pred: U₁.Particular → CongruentUnaryPredicate U₂ := (a: U₁.Particular ↦ curry_fiber_left R a)
  let cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x =₍U₁₎ y → ((pred x).pred z ↔ (pred y).pred z) := by forall_intro
    variable(a₁: U₁.Particular)
    variable(a₂: U₁.Particular)
    variable(z: U₂.Particular)
    assume(h₁: a₁ =₍U₁₎ a₂)
    have h₂: z =₍U₂₎ z := U₂.eq.refl z
    have h₃: a₁ =₍U₁₎ a₂ ∧ z =₍U₂₎ z := by and_intro h₁, h₂
    have h₄: (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ z) ↔ a₁ =₍U₁₎ a₂ ∧ z =₍U₂₎ z := by forall_elim eq_def, a₁, z, a₂, z
    have h₅: (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ z) := PC₀.deductive_eq_r2l h₄ h₃
    have h₆: (a₁ ⋈ z) =ₗₓₗ (a₂ ⋈ z) → (R.pred (a₁ ⋈ z) ↔ R.pred (a₂ ⋈ z)) := by forall_elim R.cong, (a₁ ⋈ z), (a₂ ⋈ z)
    have h₇: R.pred (a₁ ⋈ z) ↔ R.pred (a₂ ⋈ z) := by modus_ponens h₆, h₅
    iterate h₇
  { pred := pred, cong := cong }

instance congruent_curry {U₁ U₂: Universal} {R: CongruentUnaryPredicate (U₁ ⧓ U₂)}:
    CongruentBinary U₁ U₂ (curry_reducicle_def_left R.pred) where
  inner_cong := by forall_intro
    variable(x: U₁.Particular)
    have h₁ := ((curry_cong R).pred x).cong
    iterate h₁
  outer_cong := (curry_cong R).cong

-- # Partial application of a curried congruent predicate (left fixed)
-- Fixing the left relatum of a congruent binary predicate yields a congruent unary predicate.
-- The instance head uses curry_reducicle_def_left, which Lean unfolds via @[reducible] to match
-- the pattern fun y => R.pred (a ⋈ y).
instance congruent_curry_partial_left {U₁ U₂: Universal} {R: CongruentUnaryPredicate (U₁ ⧓ U₂)} {a: U₁.Particular}:
    CongruentUnary U₂ (curry_reducicle_def_left R.pred a) where
  cong := (curry_fiber_left R a).cong

-- # Curry Reducible Rule (right partial application)
-- Reducible version for fixing the right relatum. Lean unfolds this during
-- instance search to match the pattern fun x => R.pred (x ⋈ b).
@[reducible] def curry_reducicle_def_right {U₁: Universal} {U₂: Universal} (P: U₁ ⋈ U₂ → Prop)
    (b: U₂.Particular): U₁.Particular → Prop := (a: U₁.Particular ↦ P (a ⋈ b))

-- # Curry Fiber (right fixed)
-- For a congruent unary predicate R on dyads, fixing the second relatum b
-- yields a congruent unary predicate on the first universal: (a ↦ R.pred (a ⋈ b)).
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
def curry_fiber_right {U₁ U₂: Universal} (R: CongruentUnaryPredicate (U₁ ⧓ U₂)) (b: U₂.Particular):
    CongruentUnaryPredicate U₁ :=
  let pred: U₁.Particular → Prop := (a: U₁.Particular ↦ R.pred (a ⋈ b))
  let cong: ∀ (a₁: U₁.Particular), ∀ (a₂: U₁.Particular),
      a₁ =₍U₁₎ a₂ → (R.pred (a₁ ⋈ b) ↔ R.pred (a₂ ⋈ b)) := by forall_intro
    variable(a₁: U₁.Particular)
    variable(a₂: U₁.Particular)
    assume(h₁: a₁ =₍U₁₎ a₂)
    have h₂: b =₍U₂₎ b := U₂.eq.refl b
    have h₃: a₁ =₍U₁₎ a₂ ∧ b =₍U₂₎ b := by and_intro h₁, h₂
    have h₄: (a₁ ⋈ b) =ₗₓₗ (a₂ ⋈ b) ↔ a₁ =₍U₁₎ a₂ ∧ b =₍U₂₎ b := by forall_elim eq_def, a₁, b, a₂, b
    have h₅: (a₁ ⋈ b) =ₗₓₗ (a₂ ⋈ b) := PC₀.deductive_eq_r2l h₄ h₃
    have h₆: (a₁ ⋈ b) =ₗₓₗ (a₂ ⋈ b) → (R.pred (a₁ ⋈ b) ↔ R.pred (a₂ ⋈ b)) := by forall_elim R.cong, (a₁ ⋈ b), (a₂ ⋈ b)
    have h₇: R.pred (a₁ ⋈ b) ↔ R.pred (a₂ ⋈ b) := by modus_ponens h₆, h₅
    iterate h₇
  { pred := pred, cong := cong }

-- # Partial application of a curried congruent predicate (right fixed)
-- Fixing the right relatum of a congruent binary predicate yields a congruent unary predicate.
-- The instance head uses curry_reducicle_def_right, which Lean unfolds via @[reducible] to match
-- the pattern fun x => R.pred (x ⋈ b).
instance congruent_curry_partial_right {U₁ U₂: Universal}
    {R: CongruentUnaryPredicate (U₁ ⧓ U₂)} {b: U₂.Particular}:
    CongruentUnary U₁ (curry_reducicle_def_right R.pred b) where
  cong := (curry_fiber_right R b).cong

end Dyads
end Universe
