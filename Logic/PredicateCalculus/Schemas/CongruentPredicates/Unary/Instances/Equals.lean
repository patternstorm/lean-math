import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

-- `equal_to a` is the currying of universal equality by its first argument:
-- `(equal_to a).pred x := a =₍U₎ x`. The parameter sits on the LEFT of the
-- relation and the test variable on the RIGHT. This convention is what lets
-- the binary lift `equals.pred x := equal_to x` yield the domain-first graph
-- `(equals.pred x).pred y = x =₍U₎ y` automatically. Any unary predicate built
-- by currying a binary relation should follow the same discipline.
def equal_to(a: U.Particular): CongruentUnaryPredicate U :=
  let pred: U.Particular → Prop := (x: U.Particular ↦ a =₍U₎ x)
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

end PC₁

end Logic
