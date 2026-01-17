import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Instances.Equals

namespace Logic

namespace PC₁

def equals: CongruentBinaryPredicate U U :=
  let pred: U.Particular → CongruentUnaryPredicate U := (x: U.Particular ↦ equal_to x)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), ∀ (z: U.Particular), x =₍U₎ y → (z =₍U₎ x ↔ z =₍U₎ y):= by forall_intro
    variable(u: U.Particular)
    variable(v: U.Particular)
    variable(w: U.Particular)
    assume(h₁: u =₍U₎ v)
    have h₂: w =₍U₎ u → w =₍U₎ v := by
      assume(h₂₁: w =₍U₎ u)
      have h₂₂: ∀ (y: U.Particular), ∀  (z: U.Particular), w =₍U₎ y ∧ y =₍U₎ z → w =₍U₎ z := by forall_elim U.eq.trans, w
      have h₂₃: ∀  (z: U.Particular), w =₍U₎ u ∧ u =₍U₎ z → w =₍U₎ z := by forall_elim h₂₂, u
      have h₂₄: w =₍U₎ u ∧ u =₍U₎ v → w =₍U₎ v := by forall_elim h₂₃, v
      have h₂₅: w =₍U₎ u ∧ u =₍U₎ v := by and_intro h₂₁, h₁
      have h₂₆: w =₍U₎ v := by modus_ponens h₂₄, h₂₅
      iterate h₂₆
    have h₃: w =₍U₎ v → w =₍U₎ u := by
      assume(h₃₁: w =₍U₎ v)
      have h₃₂: ∀ (y: U.Particular), ∀  (z: U.Particular), w =₍U₎ y ∧ y =₍U₎ z → w =₍U₎ z := by forall_elim U.eq.trans, w
      have h₃₃: ∀  (z: U.Particular), w =₍U₎ v ∧ v =₍U₎ z → w =₍U₎ z := by forall_elim h₃₂, v
      have h₃₄: w =₍U₎ v ∧ v =₍U₎ u → w =₍U₎ u := by forall_elim h₃₃, u
      have h₃₅: ∀ (y: U.Particular), u =₍U₎ y → y =₍U₎ u := by forall_elim U.eq.sym, u
      have h₃₆: u =₍U₎ v → v =₍U₎ u := by forall_elim h₃₅, v
      have h₃₇: v =₍U₎ u := by modus_ponens h₃₆, h₁
      have h₃₈: w =₍U₎ v ∧ v =₍U₎ u := by and_intro h₃₁, h₃₇
      have h₃₉: w =₍U₎ u := by modus_ponens h₃₄, h₃₈
      iterate h₃₉
    have h₄: w =₍U₎ u ↔ w =₍U₎ v := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

end PC₁

end Logic
