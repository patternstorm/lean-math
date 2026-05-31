import Universe
import Logic
import Universals.Sets
import Universals.Relations.Particular

/-!
# Relation Universal

Relations over U₁ and U₂ form their own Universal. The Particulars are
`CongruentBinaryPredicate U₁ U₂` (binary predicates) and equality is
via logical equivalence.
-/

namespace Universe

open Logic
open Logic.PC₁


namespace Relations

-- # =ᵣₑₗ is an equivalence relation

-- ## `Relation` equality is reflexive
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-30
theorem eq_refl: ∀ (R: Relations.Particular U₁ U₂), eq R R := by forall_intro
  variable(R: Relations.Particular U₁ U₂)
  have h₁: ∀ (R₂: Relations.Particular U₁ U₂), eq R R₂ ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (R.pred x).pred y ↔ (R₂.pred x).pred y := by forall_elim eq_def, R
  have h₂: eq R R ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (R.pred x).pred y ↔ (R.pred x).pred y := by forall_elim h₁, R
  have h₃: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (R.pred x).pred y ↔ (R.pred x).pred y := by forall_intro
    variable(a: U₁.Particular)
    variable(b: U₂.Particular)
    have h₃₁: (R.pred a).pred b → (R.pred a).pred b := by
      assume(h₃₁₁: (R.pred a).pred b)
      iterate h₃₁₁
    have h₃₂: (R.pred a).pred b ↔ (R.pred a).pred b := by iff_intro h₃₁, h₃₁
    iterate h₃₂
  have h₄: eq R R := PC₀.deductive_eq_r2l h₂ h₃
  iterate h₄

-- ## `Relation` equality is symmetric
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-30
theorem eq_sym: ∀ (R₁: Relations.Particular U₁ U₂), ∀ (R₂: Relations.Particular U₁ U₂), eq R₁ R₂ → eq R₂ R₁ := by forall_intro
  variable(A: Relations.Particular U₁ U₂)
  variable(B: Relations.Particular U₁ U₂)
  have h₁: ∀ (R₂: Relations.Particular U₁ U₂), eq A R₂ ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (R₂.pred x).pred y := by forall_elim eq_def, A
  have h₂: eq A B ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (B.pred x).pred y := by forall_elim h₁, B
  have h₃: ∀ (R₂: Relations.Particular U₁ U₂), eq B R₂ ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (B.pred x).pred y ↔ (R₂.pred x).pred y := by forall_elim eq_def, B
  have h₄: eq B A ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (B.pred x).pred y ↔ (A.pred x).pred y := by forall_elim h₃, A
  have h₅: eq A B → eq B A := by
    assume(h₅₁: eq A B)
    have h₅₂: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (B.pred x).pred y ↔ (A.pred x).pred y := by forall_intro
      variable(a: U₁.Particular)
      variable(b: U₂.Particular)
      have h₅₂₁: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (B.pred x).pred y := PC₀.deductive_eq_l2r h₂ h₅₁
      have h₅₂₂: ∀ (y: U₂.Particular), (A.pred a).pred y ↔ (B.pred a).pred y := by forall_elim h₅₂₁, a
      have h₅₂₃: (A.pred a).pred b ↔ (B.pred a).pred b := by forall_elim h₅₂₂, b
      have h₅₂₄: (B.pred a).pred b ↔ (A.pred a).pred b := PC₀.deductive_eq_l2r PC₀.iff_comm h₅₂₃
      iterate h₅₂₄
    have h₅₃: eq B A := PC₀.deductive_eq_r2l h₄ h₅₂
    iterate h₅₃
  iterate h₅

-- ## `Relation` equality is transitive
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-30
theorem eq_trans: ∀ (R₁: Relations.Particular U₁ U₂), ∀ (R₂: Relations.Particular U₁ U₂), ∀ (R₃: Relations.Particular U₁ U₂), eq R₁ R₂ ∧ eq R₂ R₃ → eq R₁ R₃ := by forall_intro
  variable(A: Relations.Particular U₁ U₂)
  variable(B: Relations.Particular U₁ U₂)
  variable(C: Relations.Particular U₁ U₂)
  have h₁: ∀ (R₂: Relations.Particular U₁ U₂), eq A R₂ ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (R₂.pred x).pred y := by forall_elim eq_def, A
  have h₂: eq A B ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (B.pred x).pred y := by forall_elim h₁, B
  have h₃: ∀ (R₂: Relations.Particular U₁ U₂), eq B R₂ ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (B.pred x).pred y ↔ (R₂.pred x).pred y := by forall_elim eq_def, B
  have h₄: eq B C ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (B.pred x).pred y ↔ (C.pred x).pred y := by forall_elim h₃, C
  have h₅: eq A C ↔ ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (C.pred x).pred y := by forall_elim h₁, C
  assume(h₆: eq A B ∧ eq B C)
  have h₇: eq A B := by and_elim h₆
  have h₈: eq B C := by and_elim h₆
  have h₉: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (B.pred x).pred y := PC₀.deductive_eq_l2r h₂ h₇
  have h₁₀: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (B.pred x).pred y ↔ (C.pred x).pred y := PC₀.deductive_eq_l2r h₄ h₈
  have h₁₁: ∀ (x: U₁.Particular), ∀ (y: U₂.Particular), (A.pred x).pred y ↔ (C.pred x).pred y := by forall_intro
    variable(a: U₁.Particular)
    variable(b: U₂.Particular)
    have h₁₁₁: ∀ (y: U₂.Particular), (A.pred a).pred y ↔ (B.pred a).pred y := by forall_elim h₉, a
    have h₁₁₂: (A.pred a).pred b ↔ (B.pred a).pred b := by forall_elim h₁₁₁, b
    have h₁₁₃: ∀ (y: U₂.Particular), (B.pred a).pred y ↔ (C.pred a).pred y := by forall_elim h₁₀, a
    have h₁₁₄: (B.pred a).pred b ↔ (C.pred a).pred b := by forall_elim h₁₁₃, b
    have h₁₁₅: (A.pred a).pred b → (C.pred a).pred b := by
      assume(h₁₁₅₁: (A.pred a).pred b)
      have h₁₁₅₂: (B.pred a).pred b := PC₀.deductive_eq_l2r h₁₁₂ h₁₁₅₁
      have h₁₁₅₃: (C.pred a).pred b := PC₀.deductive_eq_l2r h₁₁₄ h₁₁₅₂
      iterate h₁₁₅₃
    have h₁₁₆: (C.pred a).pred b → (A.pred a).pred b := by
      assume(h₁₁₆₁: (C.pred a).pred b)
      have h₁₁₆₂: (B.pred a).pred b := PC₀.deductive_eq_r2l h₁₁₄ h₁₁₆₁
      have h₁₁₆₃: (A.pred a).pred b := PC₀.deductive_eq_r2l h₁₁₂ h₁₁₆₂
      iterate h₁₁₆₃
    have h₁₁₇: (A.pred a).pred b ↔ (C.pred a).pred b := by iff_intro h₁₁₅, h₁₁₆
    iterate h₁₁₇
  have h₁₂: eq A C := PC₀.deductive_eq_r2l h₅ h₁₁
  iterate h₁₂

-- # `Relation` equality
def equality: Equality (Relations.Particular U₁ U₂) :=
  let pred: Relations.Particular U₁ U₂ → Relations.Particular U₁ U₂ → Prop := eq
  let refl: ∀ (x: Relations.Particular U₁ U₂), pred x x := eq_refl
  let sym: ∀ (x: Relations.Particular U₁ U₂), ∀ (y: Relations.Particular U₁ U₂), pred x y → pred y x := eq_sym
  let trans: ∀ (x: Relations.Particular U₁ U₂), ∀ (y: Relations.Particular U₁ U₂), ∀ (z: Relations.Particular U₁ U₂), pred x y ∧ pred y z → pred x z := eq_trans
  { pred:= pred, refl:= refl, sym:= sym, trans:= trans }

-- # `Relation` Universal
-- Marked `@[reducible]` so the abbrev chain `Rel U₁ U₂ → (RelationUniversal U₁ U₂).Particular`
-- unfolds during typeclass resolution. Without this, Lean stops at the field
-- projection and can't find instances declared on `CongruentBinaryPredicate`
-- (e.g. the schema-level `CoeFun` that makes `R a b` work).
@[reducible] def RelationUniversal (U₁: Universal) (U₂: Universal): Universal := {
  Particular := Relations.Particular U₁ U₂
  eq := equality
}
notation "𝐑𝐞𝐥" => RelationUniversal
abbrev Rel U₁ U₂ := (RelationUniversal U₁ U₂).Particular

-- # =ᵣₑₗ notation
notation:50 A:51 " =ᵣₑₗ " B:51 => eq A B

end Relations

end Universe
