import Logic.PredicateCalculus.Schemas.SubUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Schemas.Operations.Unary.Instances.Identity
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁


-- # Reflexivity of SubUniversal
--
-- Every Universal U is a sub-universal of itself, via the identity embedding.
--
-- `preserves_eq` follows from `identity_invariance` (every element is fixed
-- by identity) by chaining equalities:
--   Forward:  x =₍U₎ y, identity x =₍U₎ x, identity y =₍U₎ y
--             ⇒ identity x =₍U₎ identity y (by trans + sym).
--   Backward: identity x =₍U₎ identity y, identity x =₍U₎ x, identity y =₍U₎ y
--             ⇒ x =₍U₎ y (by trans + sym).
--
-- Proof by Claude Opus 4.7, 2026-04-19
noncomputable instance subuniversal_refl (U: Universal): U <: U :=
  let e: U ⟴ U := identity
  let preserves_eq: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y ↔ (e x =₍U₎ e y) := by forall_intro
    variable(x: U.Particular)
    variable(y: U.Particular)
    have h₁: e x =₍U₎ x := by forall_elim identity_invariance, x
    have h₂: e y =₍U₎ y := by forall_elim identity_invariance, y
    have h₃: x =₍U₎ y → e x =₍U₎ e y := by
      assume(h₃₁: x =₍U₎ y)
      have h₃₂: e x =₍U₎ x ∧ x =₍U₎ y := by and_intro h₁, h₃₁
      have h₃₃: e x =₍U₎ x ∧ x =₍U₎ y → e x =₍U₎ y := by forall_elim U.eq.trans, e x, x, y
      have h₃₄: e x =₍U₎ y := by modus_ponens h₃₃, h₃₂
      have h₃₅: e y =₍U₎ y → y =₍U₎ e y := by forall_elim U.eq.sym, e y, y
      have h₃₆: y =₍U₎ e y := by modus_ponens h₃₅, h₂
      have h₃₇: e x =₍U₎ y ∧ y =₍U₎ e y := by and_intro h₃₄, h₃₆
      have h₃₈: e x =₍U₎ y ∧ y =₍U₎ e y → e x =₍U₎ e y := by forall_elim U.eq.trans, e x, y, e y
      have h₃₉: e x =₍U₎ e y := by modus_ponens h₃₈, h₃₇
      iterate h₃₉
    have h₄: e x =₍U₎ e y → x =₍U₎ y := by
      assume(h₄₁: e x =₍U₎ e y)
      have h₄₂: e x =₍U₎ x → x =₍U₎ e x := by forall_elim U.eq.sym, e x, x
      have h₄₃: x =₍U₎ e x := by modus_ponens h₄₂, h₁
      have h₄₄: x =₍U₎ e x ∧ e x =₍U₎ e y := by and_intro h₄₃, h₄₁
      have h₄₅: x =₍U₎ e x ∧ e x =₍U₎ e y → x =₍U₎ e y := by forall_elim U.eq.trans, x, e x, e y
      have h₄₆: x =₍U₎ e y := by modus_ponens h₄₅, h₄₄
      have h₄₇: x =₍U₎ e y ∧ e y =₍U₎ y := by and_intro h₄₆, h₂
      have h₄₈: x =₍U₎ e y ∧ e y =₍U₎ y → x =₍U₎ y := by forall_elim U.eq.trans, x, e y, y
      have h₄₉: x =₍U₎ y := by modus_ponens h₄₈, h₄₇
      iterate h₄₉
    have h₅: x =₍U₎ y ↔ e x =₍U₎ e y := by iff_intro h₃, h₄
    iterate h₅
  { embedding := e, preserves_eq := preserves_eq }

end PC₁

end Logic
