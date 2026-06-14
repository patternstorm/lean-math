import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

open ND

-- # Existential Preserves Congruence
-- If P(x, d) is congruent in d for each fixed x,
-- then ∃ x. P(x, d) is also congruent in d.
def existential_preserves_congruence {U₁ U₂: Universal} (P: U₁.Particular → CongruentUnaryPredicate U₂): CongruentUnaryPredicate U₂ :=
  let pred: U₂.Particular → Prop := (x: U₂.Particular ↦ ∃ (z: U₁.Particular), (P z).pred x)
  let cong: ∀ (x: U₂.Particular), ∀ (y: U₂.Particular), x =₍U₂₎ y → (pred x ↔ pred y) := by forall_intro
    variable(x: U₂.Particular)
    variable(y: U₂.Particular)
    assume(h₀: x =₍U₂₎ y)
    -- Forward
    have h₁: (∃ (z: U₁.Particular), (P z).pred x) → (∃ (z: U₁.Particular), (P z).pred y) := by
      assume(h₁₁: ∃ (z: U₁.Particular), (P z).pred x)
      have ⟨(z: U₁.Particular), (h₁₂: (P z).pred x)⟩ := exists_elim h₁₁
      have h₁₃: ∀ (w: U₂.Particular), x =₍U₂₎ w → ((P z).pred x ↔ (P z).pred w) := by forall_elim (P z).cong, x
      have h₁₄: x =₍U₂₎ y → ((P z).pred x ↔ (P z).pred y) := by forall_elim h₁₃, y
      have h₁₅: (P z).pred x ↔ (P z).pred y := by modus_ponens h₁₄, h₀
      have h₁₆: (P z).pred x → (P z).pred y := by iff_elim_l2r h₁₅
      have h₁₇: (P z).pred y := by modus_ponens h₁₆, h₁₂
      have h₁₈: ∃ (z': U₁.Particular), (P z').pred y := by exists_intro h₁₇, z
      iterate h₁₈
    -- Backward
    have h₂: (∃ (z: U₁.Particular), (P z).pred y) → (∃ (z: U₁.Particular), (P z).pred x) := by
      assume(h₂₁: ∃ (z: U₁.Particular), (P z).pred y)
      have ⟨(z: U₁.Particular), (h₂₂: (P z).pred y)⟩ := exists_elim h₂₁
      have h₂₃: ∀ (w: U₂.Particular), x =₍U₂₎ w → ((P z).pred x ↔ (P z).pred w) := by forall_elim (P z).cong, x
      have h₂₄: x =₍U₂₎ y → ((P z).pred x ↔ (P z).pred y) := by forall_elim h₂₃, y
      have h₂₅: (P z).pred x ↔ (P z).pred y := by modus_ponens h₂₄, h₀
      have h₂₆: (P z).pred y → (P z).pred x := by iff_elim_r2l h₂₅
      have h₂₇: (P z).pred x := by modus_ponens h₂₆, h₂₂
      have h₂₈: ∃ (z': U₁.Particular), (P z').pred x := by exists_intro h₂₇, z
      iterate h₂₈
    have h₃: (∃ (z: U₁.Particular), (P z).pred x) ↔ (∃ (z: U₁.Particular), (P z).pred y) := by iff_intro h₁, h₂
    iterate h₃
  { pred := pred, cong := cong }

instance congruent_existential {U₁ U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    [inst: ∀ z: U₁.Particular, CongruentUnary U₂ (P z)]: CongruentUnary U₂ (x: U₂.Particular ↦ ∃ (z: U₁.Particular), P z x) where
  cong := (existential_preserves_congruence (fun z => { pred := P z, cong := (inst z).cong })).cong

end PC₁

end Logic
