import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Instances.Equals

namespace Logic

namespace PC₁

-- The equality graph `equals : CongruentBinaryPredicate U U`.
-- Unfolds to the domain-first convention:
--   (equals.pred x).pred y  =  (equal_to x).pred y  =  x =₍U₎ y.
-- Outer congruence (in the first/domain argument) is proved via symmetry +
-- transitivity of `=₍U₎`. Inner congruence (in the second/image argument) is
-- inherited from `equal_to`.
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
