import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁


theorem negation_preserves_congruence2 (P: CongruentBinaryPredicate U₁ U₂):
  ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x =₍U₁₎ y → (¬(P.pred x).pred z ↔ ¬(P.pred y).pred z) := by forall_intro
    variable(u: U₁.Particular)
    variable(v: U₁.Particular)
    variable(w: U₂.Particular)
    assume(h₁: u =₍U₁₎ v)
    have h₂: ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), u =₍U₁₎ y → ((P.pred u).pred z ↔ (P.pred y).pred z) := by forall_elim P.cong, u
    have h₃: ∀ (z: U₂.Particular), u =₍U₁₎ v → ((P.pred u).pred z ↔ (P.pred v).pred z) := by forall_elim h₂, v
    have h₄: u =₍U₁₎ v → ((P.pred u).pred w ↔ (P.pred v).pred w) := by forall_elim h₃, w
    have h₅: (P.pred u).pred w ↔ (P.pred v).pred w := by modus_ponens h₄, h₁
    have h₆: ¬(P.pred u).pred w ↔ ¬(P.pred v).pred w := PC₀.deductive_eq_l2r PC₀.iff_contrapositiveness h₅
    iterate h₆
end PC₁

end Logic
