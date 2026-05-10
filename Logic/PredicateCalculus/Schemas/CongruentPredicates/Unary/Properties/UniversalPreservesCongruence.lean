import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PropositionalCalculus
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

open ND

-- # Universal Preserves Congruence
-- If P(z, x) is congruent in x for each fixed z,
-- then ∀ z. P(z, x) is also congruent in x.
-- Proof by Kimi 2.6, 2026-05-10
def universal_preserves_congruence {U₁ U₂: Universal} (P: U₁.Particular → CongruentUnaryPredicate U₂): CongruentUnaryPredicate U₂ :=
  let pred: U₂.Particular → Prop := (x: U₂.Particular ↦ ∀ (z: U₁.Particular), (P z).pred x)
  let cong: ∀ (x: U₂.Particular), ∀ (y: U₂.Particular), x =₍U₂₎ y → (pred x ↔ pred y) := by forall_intro
    variable(x: U₂.Particular)
    variable(y: U₂.Particular)
    assume(h₀: x =₍U₂₎ y)
    -- Forward
    have h₁: (∀ (z: U₁.Particular), (P z).pred x) → (∀ (z: U₁.Particular), (P z).pred y) := by
      assume(h₁₁: ∀ (z: U₁.Particular), (P z).pred x)
      have h₁₂: ∀ (z: U₁.Particular), (P z).pred y := by forall_intro
        variable(z: U₁.Particular)
        have h₁₃: (P z).pred x := by forall_elim h₁₁, z
        have h₁₄: ∀ (w: U₂.Particular), x =₍U₂₎ w → ((P z).pred x ↔ (P z).pred w) := by forall_elim (P z).cong, x
        have h₁₅: x =₍U₂₎ y → ((P z).pred x ↔ (P z).pred y) := by forall_elim h₁₄, y
        have h₁₆: (P z).pred x ↔ (P z).pred y := by modus_ponens h₁₅, h₀
        have h₁₇: (P z).pred y := PC₀.deductive_eq_l2r h₁₆ h₁₃
        iterate h₁₇
      iterate h₁₂
    -- Backward
    have h₂: (∀ (z: U₁.Particular), (P z).pred y) → (∀ (z: U₁.Particular), (P z).pred x) := by
      assume(h₂₁: ∀ (z: U₁.Particular), (P z).pred y)
      have h₂₂: ∀ (z: U₁.Particular), (P z).pred x := by forall_intro
        variable(z: U₁.Particular)
        have h₂₃: (P z).pred y := by forall_elim h₂₁, z
        have h₂₄: ∀ (w: U₂.Particular), x =₍U₂₎ w → ((P z).pred x ↔ (P z).pred w) := by forall_elim (P z).cong, x
        have h₂₅: x =₍U₂₎ y → ((P z).pred x ↔ (P z).pred y) := by forall_elim h₂₄, y
        have h₂₆: (P z).pred x ↔ (P z).pred y := by modus_ponens h₂₅, h₀
        have h₂₇: (P z).pred x := PC₀.deductive_eq_r2l h₂₆ h₂₃
        iterate h₂₇
      iterate h₂₂
    have h₃: (∀ (z: U₁.Particular), (P z).pred x) ↔ (∀ (z: U₁.Particular), (P z).pred y) := by iff_intro h₁, h₂
    iterate h₃
  { pred := pred, cong := cong }

instance congruent_universal {U₁ U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop} [inst: ∀ z: U₁.Particular, CongruentUnary U₂ (P z)]:
    CongruentUnary U₂ (x: U₂.Particular ↦ ∀ (z: U₁.Particular), P z x) where
  cong := (universal_preserves_congruence ((z: U₁.Particular ↦ { pred := P z, cong := (inst z).cong }))).cong

end PC₁

end Logic
