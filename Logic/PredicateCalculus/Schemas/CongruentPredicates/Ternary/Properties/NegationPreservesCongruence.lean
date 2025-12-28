import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁


theorem negation_preserves_congruence3 (P: CongruentTernaryPredicate U₁ U₂ U₃):
  ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (u: U₂.Particular), ∀ (v: U₃.Particular), x =₍U₁₎ y → (¬((P.pred x).pred u).pred v ↔ ¬((P.pred y).pred u).pred v) := by forall_intro
    variable(a: U₁.Particular)
    variable(b: U₁.Particular)
    variable(c: U₂.Particular)
    variable(d: U₃.Particular)
    assume(h₁: a =₍U₁₎ b)
    have h₂: ∀ (y: U₁.Particular), ∀ (u: U₂.Particular), ∀ (v: U₃.Particular), a =₍U₁₎ y → (((P.pred a).pred u).pred v ↔ ((P.pred y).pred u).pred v) := by forall_elim P.cong, a
    have h₃: ∀ (u: U₂.Particular), ∀ (v: U₃.Particular), a =₍U₁₎ b → (((P.pred a).pred u).pred v ↔ ((P.pred b).pred u).pred v) := by forall_elim h₂, b
    have h₄: ∀ (v: U₃.Particular), a =₍U₁₎ b → (((P.pred a).pred c).pred v ↔ ((P.pred b).pred c).pred v) := by forall_elim h₃, c
    have h₅: a =₍U₁₎ b → (((P.pred a).pred c).pred d ↔ ((P.pred b).pred c).pred d) := by forall_elim h₄, d
    have h₆: ((P.pred a).pred c).pred d ↔ ((P.pred b).pred c).pred d := by modus_ponens h₅, h₁
    have h₇: ¬((P.pred a).pred c).pred d ↔ ¬((P.pred b).pred c).pred d := PC₀.deductive_eq_l2r PC₀.iff_contrapositiveness h₆
    iterate h₇
end PC₁

end Logic
