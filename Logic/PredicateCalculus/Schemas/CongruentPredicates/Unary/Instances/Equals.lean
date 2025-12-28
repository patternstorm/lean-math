import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

def equals_unary(a: U.Particular): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ x =₍U₎ a)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (x =₍U₎ a ↔ y =₍U₎ a):= by forall_intro
    variable(u: U.Particular)
    variable(v: U.Particular)
    assume(h₁: u =₍U₎ v)
    have h₂: u =₍U₎ a → v =₍U₎ a := by
      assume(h₂₁: u =₍U₎ a)
      have h₂₂: ∀ (y: U.Particular), ∀  (z: U.Particular), v =₍U₎ y ∧ y =₍U₎ z → v =₍U₎ z := by forall_elim U.eq.trans, v
      have h₂₃: ∀  (z: U.Particular), v =₍U₎ u ∧ u =₍U₎ z → v =₍U₎ z := by forall_elim h₂₂, u
      have h₂₄: v =₍U₎ u ∧ u =₍U₎ a → v =₍U₎ a := by forall_elim h₂₃, a
      have h₂₅: ∀ (y: U.Particular), u =₍U₎ y → y =₍U₎ u := by forall_elim U.eq.sym, u
      have h₂₆: u =₍U₎ v → v =₍U₎ u := by forall_elim h₂₅, v
      have h₂₇: v =₍U₎ u := by modus_ponens h₂₆, h₁
      have h₂₅: v =₍U₎ u ∧ u =₍U₎ a := by and_intro h₂₇, h₂₁
      have h₃₆: v =₍U₎ a := by modus_ponens h₂₄, h₂₅
      iterate h₃₆
    have h₃: v =₍U₎ a → u =₍U₎ a := by
      assume(h₃₁: v =₍U₎ a)
      have h₃₂: ∀ (y: U.Particular), ∀  (z: U.Particular), u =₍U₎ y ∧ y =₍U₎ z → u =₍U₎ z := by forall_elim U.eq.trans, u
      have h₃₃: ∀  (z: U.Particular), u =₍U₎ v ∧ v =₍U₎ z → u =₍U₎ z := by forall_elim h₃₂, v
      have h₃₄: u =₍U₎ v ∧ v =₍U₎ a → u =₍U₎ a := by forall_elim h₃₃, a
      have h₃₅: u =₍U₎ v ∧ v =₍U₎ a := by and_intro h₁, h₃₁
      have h₃₆: u =₍U₎ a := by modus_ponens h₃₄, h₃₅
      iterate h₃₆
    have h₄: u =₍U₎ a ↔ v =₍U₎ a := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

end PC₁

end Logic
