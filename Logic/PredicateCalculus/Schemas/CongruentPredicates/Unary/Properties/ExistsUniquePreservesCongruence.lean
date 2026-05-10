import Logic.NaturalDeduction.Rules
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Definitions.ExistsUnique.Definition
import Logic.PropositionalCalculus
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition

namespace Logic

namespace PC₁

open ND

-- # Exists-Unique Preserves Congruence
-- If P(z, x) is congruent in x for each fixed z,
-- then ∃!₍U₁₎ z, P(z, x) is also congruent in x.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
def exists_unique_preserves_congruence {U₁ U₂: Universal} (P: U₁.Particular → CongruentUnaryPredicate U₂): CongruentUnaryPredicate U₂ :=
  let pred: U₂.Particular → Prop := (x: U₂.Particular ↦ ∃!₍U₁₎ (z: U₁.Particular), (P z).pred x)
  -- Unpack ∃! via the axiom schema (shared by both directions)
  let eu: ∀ (Q: U₁.Particular → Prop), ExistsUnique U₁ Q ↔ (∃ (z: U₁.Particular), Q z ∧ (∀ (w: U₁.Particular), Q w → w =₍U₁₎ z)) := by forall_elim exists_unique_def, U₁
  let cong: ∀ (x: U₂.Particular), ∀ (y: U₂.Particular), x =₍U₂₎ y → (pred x ↔ pred y) := by forall_intro
    variable(x: U₂.Particular)
    variable(y: U₂.Particular)
    assume(h₀: x =₍U₂₎ y)
    -- Forward: ∃!₍U₁₎ z, (P z).pred x → ∃!₍U₁₎ z, (P z).pred y
    have h₁: pred x → pred y := by
      assume(h₁₁: ∃!₍U₁₎ (z: U₁.Particular), (P z).pred x)
      -- Unfold ∃! for x
      have h₁₂: (∃!₍U₁₎ (z: U₁.Particular), (P z).pred x) ↔
        (∃ (z: U₁.Particular), (P z).pred x ∧ (∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z)) := by forall_elim eu, (z: U₁.Particular ↦ (P z).pred x)
      have h₁₃: ∃ (z: U₁.Particular), (P z).pred x ∧ (∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z) :=
        PC₀.deductive_eq_l2r h₁₂ h₁₁
      -- Extract witness z₀
      have ⟨(z₀: U₁.Particular), (h₁₄: (P z₀).pred x ∧ (∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z₀))⟩ := exists_elim h₁₃
      have h₁₅: (P z₀).pred x := by and_elim h₁₄
      have h₁₆: ∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z₀ := by and_elim h₁₄
      -- Transfer existence: (P z₀).pred x → (P z₀).pred y
      have h₁₇: ∀ (v: U₂.Particular), x =₍U₂₎ v → ((P z₀).pred x ↔ (P z₀).pred v) := by forall_elim (P z₀).cong, x
      have h₁₈: x =₍U₂₎ y → ((P z₀).pred x ↔ (P z₀).pred y) := by forall_elim h₁₇, y
      have h₁₉: (P z₀).pred x ↔ (P z₀).pred y := by modus_ponens h₁₈, h₀
      have h₁₁₀: (P z₀).pred y := PC₀.deductive_eq_l2r h₁₉ h₁₅
      -- Transfer uniqueness: ∀ w, (P w).pred y → w =₍U₁₎ z₀
      have h₁₁₁: ∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z₀ := by forall_intro
        variable(w: U₁.Particular)
        assume(h₁₁₁₁: (P w).pred y)
        have h₁₁₁₂: ∀ (v: U₂.Particular), x =₍U₂₎ v → ((P w).pred x ↔ (P w).pred v) := by forall_elim (P w).cong, x
        have h₁₁₁₃: x =₍U₂₎ y → ((P w).pred x ↔ (P w).pred y) := by forall_elim h₁₁₁₂, y
        have h₁₁₁₄: (P w).pred x ↔ (P w).pred y := by modus_ponens h₁₁₁₃, h₀
        have h₁₁₁₅: (P w).pred x := PC₀.deductive_eq_r2l h₁₁₁₄ h₁₁₁₁
        have h₁₁₁₆: (P w).pred x → w =₍U₁₎ z₀ := by forall_elim h₁₆, w
        have h₁₁₁₇: w =₍U₁₎ z₀ := by modus_ponens h₁₁₁₆, h₁₁₁₅
        iterate h₁₁₁₇
      -- Repackage into ∃!₍U₁₎ for y
      have h₁₁₂: (P z₀).pred y ∧ (∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z₀) := by and_intro h₁₁₀, h₁₁₁
      have h₁₁₃: ∃ (z: U₁.Particular), (P z).pred y ∧ (∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z) := by exists_intro h₁₁₂, z₀
      have h₁₁₄: (∃!₍U₁₎ (z: U₁.Particular), (P z).pred y) ↔
        (∃ (z: U₁.Particular), (P z).pred y ∧ (∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z)) := by
          forall_elim eu, (z: U₁.Particular ↦ (P z).pred y)
      have h₁₁₅: ∃!₍U₁₎ (z: U₁.Particular), (P z).pred y := PC₀.deductive_eq_r2l h₁₁₄ h₁₁₃
      iterate h₁₁₅
    -- Backward: ∃!₍U₁₎ z, (P z).pred y → ∃!₍U₁₎ z, (P z).pred x
    have h₂: pred y → pred x := by
      assume(h₂₁: ∃!₍U₁₎ (z: U₁.Particular), (P z).pred y)
      -- Unfold ∃! for y
      have h₂₂: (∃!₍U₁₎ (z: U₁.Particular), (P z).pred y) ↔
        (∃ (z: U₁.Particular), (P z).pred y ∧ (∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z)) := by
          forall_elim eu, (z: U₁.Particular ↦ (P z).pred y)
      have h₂₃: ∃ (z: U₁.Particular), (P z).pred y ∧ (∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z) :=
        PC₀.deductive_eq_l2r h₂₂ h₂₁
      -- Extract witness z₀
      have ⟨(z₀: U₁.Particular), (h₂₄: (P z₀).pred y ∧ (∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z₀))⟩ := exists_elim h₂₃
      have h₂₅: (P z₀).pred y := by and_elim h₂₄
      have h₂₆: ∀ (w: U₁.Particular), (P w).pred y → w =₍U₁₎ z₀ := by and_elim h₂₄
      -- Transfer existence: (P z₀).pred y → (P z₀).pred x
      have h₂₇: ∀ (v: U₂.Particular), x =₍U₂₎ v → ((P z₀).pred x ↔ (P z₀).pred v) := by forall_elim (P z₀).cong, x
      have h₂₈: x =₍U₂₎ y → ((P z₀).pred x ↔ (P z₀).pred y) := by forall_elim h₂₇, y
      have h₂₉: (P z₀).pred x ↔ (P z₀).pred y := by modus_ponens h₂₈, h₀
      have h₂₁₀: (P z₀).pred x := PC₀.deductive_eq_r2l h₂₉ h₂₅
      -- Transfer uniqueness: ∀ w, (P w).pred x → w =₍U₁₎ z₀
      have h₂₁₁: ∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z₀ := by forall_intro
        variable(w: U₁.Particular)
        assume(h₂₁₁₁: (P w).pred x)
        have h₂₁₁₂: ∀ (v: U₂.Particular), x =₍U₂₎ v → ((P w).pred x ↔ (P w).pred v) := by forall_elim (P w).cong, x
        have h₂₁₁₃: x =₍U₂₎ y → ((P w).pred x ↔ (P w).pred y) := by forall_elim h₂₁₁₂, y
        have h₂₁₁₄: (P w).pred x ↔ (P w).pred y := by modus_ponens h₂₁₁₃, h₀
        have h₂₁₁₅: (P w).pred y := PC₀.deductive_eq_l2r h₂₁₁₄ h₂₁₁₁
        have h₂₁₁₆: (P w).pred y → w =₍U₁₎ z₀ := by forall_elim h₂₆, w
        have h₂₁₁₇: w =₍U₁₎ z₀ := by modus_ponens h₂₁₁₆, h₂₁₁₅
        iterate h₂₁₁₇
      -- Repackage into ∃!₍U₁₎ for x
      have h₂₁₂: (P z₀).pred x ∧ (∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z₀) := by and_intro h₂₁₀, h₂₁₁
      have h₂₁₃: ∃ (z: U₁.Particular), (P z).pred x ∧ (∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z) := by exists_intro h₂₁₂, z₀
      have h₂₁₄: (∃!₍U₁₎ (z: U₁.Particular), (P z).pred x) ↔
        (∃ (z: U₁.Particular), (P z).pred x ∧ (∀ (w: U₁.Particular), (P w).pred x → w =₍U₁₎ z)) := by
          forall_elim eu, (z: U₁.Particular ↦ (P z).pred x)
      have h₂₁₅: ∃!₍U₁₎ (z: U₁.Particular), (P z).pred x := PC₀.deductive_eq_r2l h₂₁₄ h₂₁₃
      iterate h₂₁₅
    have h₃: pred x ↔ pred y := by iff_intro h₁, h₂
    iterate h₃
  { pred := pred, cong := cong }

instance congruent_exists_unique {U₁ U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    [inst: ∀ z: U₁.Particular, CongruentUnary U₂ (P z)]: CongruentUnary U₂ (x: U₂.Particular ↦ ∃!₍U₁₎ (z: U₁.Particular), P z x) where
  cong := (exists_unique_preserves_congruence ((z: U₁.Particular ↦ { pred := P z, cong := (inst z).cong }))).cong

end PC₁

end Logic
