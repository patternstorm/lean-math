import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

-- # Binary congruence from per-argument (fiber) congruences.
--
-- A binary predicate that is congruent in each argument separately is jointly
-- congruent. Given `inner_cong` (cong on `y` for each fixed `x`) and
-- `outer_cong` (cong on `x` for each fixed `y`), this theorem produces the
-- combined cong on both arguments simultaneously.
--
-- This is the bridge between the two representations of binary congruence:
-- - **Per-argument form** (inner + outer separately): the natural shape for
--   structural auto-derivation, since auto-cong instances build cong for each
--   argument independently as it traverses the body's connectives.
-- - **Combined form** (single proof, both args at once): the shape stored in
--   the `CongruentBinaryPredicate` structure's `cong` field.
--
-- Used internally by `congruent_binary_coercion` to convert a `[CongruentBinary]`
-- typeclass instance (per-argument form) into a `CongruentBinaryPredicate`
-- value (combined form).
--
-- Conceptually a peer to `ConjunctionPreservesCongruence` and the other
-- preservation theorems: there, an operation on predicates preserves the
-- property of being congruent; here, combining two per-argument cong proofs
-- preserves the property of being congruent (now jointly).
--
-- Proof strategy: chain through an intermediate point
-- `P a₁ b₁ ↔ P a₂ b₁ ↔ P a₂ b₂` (outer step then inner step).
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem binary_congruence_from_congruent_fibers
    {U₁ U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    (inner_cong: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular),
                   y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂))
    (outer_cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (z: U₂.Particular),
                   x₁ =₍U₁₎ x₂ → (P x₁ z ↔ P x₂ z)):
    ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular),
      x₁ =₍U₁₎ x₂ → y₁ =₍U₂₎ y₂ → (P x₁ y₁ ↔ P x₂ y₂) := by forall_intro
  variable(a₁: U₁.Particular)
  variable(a₂: U₁.Particular)
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  assume(h₁: a₁ =₍U₁₎ a₂)
  assume(h₂: b₁ =₍U₂₎ b₂)
  -- Outer step at the first arg: P a₁ b₁ ↔ P a₂ b₁
  have h₃: a₁ =₍U₁₎ a₂ → (P a₁ b₁ ↔ P a₂ b₁) := by forall_elim outer_cong, a₁, a₂, b₁
  have h₄: P a₁ b₁ ↔ P a₂ b₁ := by modus_ponens h₃, h₁
  -- Inner step at the second arg: P a₂ b₁ ↔ P a₂ b₂
  have h₅: b₁ =₍U₂₎ b₂ → (P a₂ b₁ ↔ P a₂ b₂) := by forall_elim inner_cong, a₂, b₁, b₂
  have h₆: P a₂ b₁ ↔ P a₂ b₂ := by modus_ponens h₅, h₂
  -- Chain
  have h₇: P a₁ b₁ → P a₂ b₂ := by
    assume(h₇₁: P a₁ b₁)
    have h₇₂: P a₂ b₁ := PC₀.deductive_eq_l2r h₄ h₇₁
    have h₇₃: P a₂ b₂ := PC₀.deductive_eq_l2r h₆ h₇₂
    iterate h₇₃
  have h₈: P a₂ b₂ → P a₁ b₁ := by
    assume(h₈₁: P a₂ b₂)
    have h₈₂: P a₂ b₁ := PC₀.deductive_eq_r2l h₆ h₈₁
    have h₈₃: P a₁ b₁ := PC₀.deductive_eq_r2l h₄ h₈₂
    iterate h₈₃
  have h₉: P a₁ b₁ ↔ P a₂ b₂ := by iff_intro h₇, h₈
  iterate h₉

-- Coercion: when Lean expects a `CongruentBinaryPredicate` and finds a binary
-- predicate `P` with `[CongruentBinary U₁ U₂ P]` synthesizable, it coerces
-- via the theorem above (which combines the typeclass's `inner_cong` and
-- `outer_cong` into the combined cong the structure requires).
-- Key invariant: `coe.pred = P` definitionally.
instance congruent_binary_coercion {U₁: Universal} {U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    [c: CongruentBinary U₁ U₂ P]:
    CoeDep (U₁.Particular → U₂.Particular → Prop) P (CongruentBinaryPredicate U₁ U₂) where
  coe := { pred := P, cong := binary_congruence_from_congruent_fibers c.inner_cong c.outer_cong }

end PC₁

end Logic
