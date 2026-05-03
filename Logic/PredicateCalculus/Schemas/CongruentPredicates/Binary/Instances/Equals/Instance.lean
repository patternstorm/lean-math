import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

-- # Equals Predicate
private def equals_pred {U: Universal} (a: U.Particular)(b: U.Particular): Prop := a =₍U₎ b

-- # Equals Unary Predicate
-- Fixes first param

def equal_to(a: U.Particular): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := equals_pred a
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (a =₍U₎ x ↔ a =₍U₎ y):= by forall_intro
    variable(u: U.Particular)
    variable(v: U.Particular)
    assume(h₁: u =₍U₎ v)
    have h₂: a =₍U₎ u → a =₍U₎ v := by
      assume(h₂₁: a =₍U₎ u)
      have h₂₂: a =₍U₎ u ∧ u =₍U₎ v := by and_intro h₂₁, h₁
      have h₂₃: a =₍U₎ u ∧ u =₍U₎ v → a =₍U₎ v := by forall_elim U.eq.trans, a, u, v
      have h₂₄: a =₍U₎ v := by modus_ponens h₂₃, h₂₂
      iterate h₂₄
    have h₃: a =₍U₎ v → a =₍U₎ u := by
      assume(h₃₁: a =₍U₎ v)
      have h₃₂: u =₍U₎ v → v =₍U₎ u := by forall_elim U.eq.sym, u, v
      have h₃₃: v =₍U₎ u := by modus_ponens h₃₂, h₁
      have h₃₄: a =₍U₎ v ∧ v =₍U₎ u := by and_intro h₃₁, h₃₃
      have h₃₅: a =₍U₎ v ∧ v =₍U₎ u → a =₍U₎ u := by forall_elim U.eq.trans, a, v, u
      have h₃₆: a =₍U₎ u := by modus_ponens h₃₅, h₃₄
      iterate h₃₆
    have h₄: a =₍U₎ u ↔ a =₍U₎ v := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }


def equals: CongruentBinaryPredicate U U :=
  let pred: U.Particular → CongruentUnaryPredicate U := (x: U.Particular ↦ equal_to x)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), ∀ (z: U.Particular), x =₍U₎ y → (x =₍U₎ z ↔ y =₍U₎ z):= by forall_intro
    variable(u: U.Particular)
    variable(v: U.Particular)
    variable(w: U.Particular)
    assume(h₁: u =₍U₎ v)
    have h₂: u =₍U₎ w → v =₍U₎ w := by
      assume(h₂₁: u =₍U₎ w)
      have h₂₂: u =₍U₎ v → v =₍U₎ u := by forall_elim U.eq.sym, u, v
      have h₂₃: v =₍U₎ u := by modus_ponens h₂₂, h₁
      have h₂₄: v =₍U₎ u ∧ u =₍U₎ w := by and_intro h₂₃, h₂₁
      have h₂₅: v =₍U₎ u ∧ u =₍U₎ w → v =₍U₎ w := by forall_elim U.eq.trans, v, u, w
      have h₂₆: v =₍U₎ w := by modus_ponens h₂₅, h₂₄
      iterate h₂₆
    have h₃: v =₍U₎ w → u =₍U₎ w := by
      assume(h₃₁: v =₍U₎ w)
      have h₃₂: u =₍U₎ v ∧ v =₍U₎ w := by and_intro h₁, h₃₁
      have h₃₃: u =₍U₎ v ∧ v =₍U₎ w → u =₍U₎ w := by forall_elim U.eq.trans, u, v, w
      have h₃₄: u =₍U₎ w := by modus_ponens h₃₃, h₃₂
      iterate h₃₄
    have h₄: u =₍U₎ w ↔ v =₍U₎ w := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

end PC₁

end Logic
