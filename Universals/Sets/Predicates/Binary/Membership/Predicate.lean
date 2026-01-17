import Logic
import Universe
import Universals.Sets.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # `Set` Membership perdicate, a `Particular` `x` is a member of the `Set` `A` if it satisfies its `Predicate`.
axiom mem: U.Particular → Particular U → Prop
notation:50 x:51 " ∈ₛₑₜ " S:51 => mem x S
axiom mem_def: ∀ (S: (Set U).Particular), ∀ (x: U.Particular), x ∈ₛₑₜ S ↔ S.pred x

def mem_unary (x: U.Particular): CongruentUnaryPredicate (Set U) :=
  let pred := (S: Particular U ↦ x ∈ₛₑₜ S)
  let cong: ∀ (X: (Set U).Particular), ∀ (Y: (Set U).Particular), X =ₛₑₜ Y → (x ∈ₛₑₜ X ↔ x ∈ₛₑₜ Y) := by forall_intro
    variable(A: (Set U).Particular)
    variable(B: (Set U).Particular)
    have h₁: ∀ S₂: (Set U).Particular, A =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), A.pred x ↔ S₂.pred x := by forall_elim eq_def, A
    have h₂: A =ₛₑₜ B ↔ ∀ (x: U.Particular), A.pred x ↔ B.pred x := by forall_elim h₁, B
    have h₃: ∀ (x: U.Particular), x ∈ₛₑₜ A ↔ A.pred x := by forall_elim mem_def, A
    have h₄: x ∈ₛₑₜ A ↔ A.pred x := by forall_elim h₃, x
    have h₅: ∀ (x: U.Particular), x ∈ₛₑₜ B ↔ B.pred x := by forall_elim mem_def, B
    have h₆: x ∈ₛₑₜ B ↔ B.pred x := by forall_elim h₅, x
    assume(h₇: A =ₛₑₜ B)
    have h₇₁: ∀ (x: U.Particular), A.pred x ↔ B.pred x := PC₀.deductive_eq_l2r h₂ h₇
    have h₇₂: A.pred x ↔ B.pred x := by forall_elim h₇₁, x
    have h₇₃: x ∈ₛₑₜ A → x ∈ₛₑₜ B := by
      assume(h₇₃₁: x ∈ₛₑₜ A)
      have h₇₃₂: A.pred x := PC₀.deductive_eq_l2r h₄ h₇₃₁
      have h₇₃₃: B.pred x := PC₀.deductive_eq_l2r h₇₂ h₇₃₂
      have h₇₃₄: x ∈ₛₑₜ B := PC₀.deductive_eq_r2l h₆ h₇₃₃
      iterate h₇₃₄
    have h₇₄: x ∈ₛₑₜ B → x ∈ₛₑₜ A := by
      assume(h₇₄₁: x ∈ₛₑₜ B)
      have h₇₄₂: B.pred x := PC₀.deductive_eq_l2r h₆ h₇₄₁
      have h₇₄₃: A.pred x := PC₀.deductive_eq_r2l h₇₂ h₇₄₂
      have h₇₄₄: x ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₄ h₇₄₃
      iterate h₇₄₄
    have h₇₅: x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B := by iff_intro h₇₃, h₇₄
    iterate h₇₅
  { pred:= pred, cong:= cong }

def mem_predicate: CongruentBinaryPredicate U (Set U) :=
  let pred:= (x: U.Particular ↦ mem_unary x)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), ∀ (X: (Set U).Particular), x =₍U₎ y → (x ∈ₛₑₜ X ↔ y ∈ₛₑₜ X) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    variable(S: (Set U).Particular)
    have h₁: ∀ (y: U.Particular), a =₍U₎ y → (S.pred a ↔ S.pred y) := by forall_elim S.cong, a
    have h₂: a =₍U₎ b → (S.pred a ↔ S.pred b) := by forall_elim h₁, b
    have h₃: ∀ (x: U.Particular), x ∈ₛₑₜ S ↔ S.pred x := by forall_elim mem_def, S
    have h₄ : a ∈ₛₑₜ S ↔ S.pred a := by forall_elim h₃, a
    have h₅ : b ∈ₛₑₜ S ↔ S.pred b := by forall_elim h₃, b
    assume(h₆: a =₍U₎ b)
    have h₇: S.pred a ↔ S.pred b := by modus_ponens h₂, h₆
    have h₈: a ∈ₛₑₜ S → b ∈ₛₑₜ S := by
      assume(h₈₁: a ∈ₛₑₜ S)
      have h₈₂: S.pred a := PC₀.deductive_eq_l2r h₄ h₈₁
      have h₈₃: S.pred b := PC₀.deductive_eq_l2r h₇ h₈₂
      have h₈₃: b ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₅ h₈₃
      iterate h₈₃
    have h₉: b ∈ₛₑₜ S → a ∈ₛₑₜ S := by
      assume(h₉₁: b ∈ₛₑₜ S)
      have h₉₂: S.pred b := PC₀.deductive_eq_l2r h₅ h₉₁
      have h₉₃: S.pred a := PC₀.deductive_eq_r2l h₇ h₉₂
      have h₉₃: a ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₄ h₉₃
      iterate h₉₃
    have h₁₀: a ∈ₛₑₜ S ↔ b ∈ₛₑₜ S := by iff_intro h₈, h₉
    iterate h₁₀
  { pred:= pred, cong:= cong }


-- # `Set` Non Membership predicate,
axiom not_mem: U.Particular → (Set U).Particular → Prop
notation:50 x:51 " ∉ₛₑₜ " S:51 => not_mem x S  -- Explicit precedence for arguments
axiom not_mem_def: ∀ (S: (Set U).Particular), ∀ (x: U.Particular), x ∉ₛₑₜ S ↔ ¬(S.pred x)

theorem not_mem_iff_neg_mem {A: (Set U).Particular} {u: U.Particular}: (u ∉ₛₑₜ A) ↔ ¬(u ∈ₛₑₜ A) := by
    have h₂: ∀ (x: U.Particular), x ∉ₛₑₜ A ↔ ¬(A.pred x) := by forall_elim not_mem_def, A
    have h₃: u ∉ₛₑₜ A ↔ ¬(A.pred u) := by forall_elim h₂, u
    have h₄: ∀ (x: U.Particular), x ∈ₛₑₜ A ↔ A.pred x := by forall_elim mem_def, A
    have h₅: u ∈ₛₑₜ A ↔ A.pred u := by forall_elim h₄, u
    have h₆: (u ∈ₛₑₜ A ↔ A.pred u) ↔ (¬(u ∈ₛₑₜ A) ↔ ¬(A.pred u)) := PC₀.iff_contrapositiveness
    have h₇: ¬(u ∈ₛₑₜ A) ↔ ¬(A.pred u) := PC₀.deductive_eq_l2r h₆ h₅
    have h₁: (u ∉ₛₑₜ A) → ¬(u ∈ₛₑₜ A) := by
      assume(h₁₁: u ∉ₛₑₜ A)
      have h₈: ¬(A.pred u) := PC₀.deductive_eq_l2r h₃ h₁₁
      have h₉: ¬(u ∈ₛₑₜ A) := PC₀.deductive_eq_r2l h₇ h₈
      iterate h₉
    have h₂: ¬(u ∈ₛₑₜ A) → (u ∉ₛₑₜ A) := by
      assume(h₂₁: ¬(u ∈ₛₑₜ A))
      have h₂₂: ¬(A.pred u) := PC₀.deductive_eq_l2r h₇ h₂₁
      have h₂₃: u ∉ₛₑₜ A := PC₀.deductive_eq_r2l h₃ h₂₂
      iterate h₂₃
    iff_intro h₁, h₂


def not_mem_unary (x: U.Particular): CongruentUnaryPredicate (Set U) :=
  let pred := (S: Particular U ↦ x ∉ₛₑₜ S)
  let cong: ∀ (X: (Set U).Particular), ∀ (Y: (Set U).Particular), X =ₛₑₜ Y → (x ∉ₛₑₜ X ↔ x ∉ₛₑₜ Y) := by forall_intro
    variable(A: (Set U).Particular)
    variable(B: (Set U).Particular)
    have h₁: ∀ (Y: (Set U).Particular), A =ₛₑₜ Y → (¬(x ∈ₛₑₜ A) ↔ ¬(x ∈ₛₑₜ Y)) := by forall_elim (negation_preserves_congruence1 (mem_unary x)), A
    have h₂: A =ₛₑₜ B → (¬(x ∈ₛₑₜ A) ↔ ¬(x ∈ₛₑₜ B)) := by forall_elim h₁, B
    assume(h₃: A =ₛₑₜ B)
    have h₄: ¬(x ∈ₛₑₜ A) ↔ ¬(x ∈ₛₑₜ B) := by modus_ponens h₂, h₃
    have h₅: (x ∉ₛₑₜ A) ↔ ¬(x ∈ₛₑₜ A) := not_mem_iff_neg_mem
    have h₆: (x ∉ₛₑₜ B) ↔ ¬(x ∈ₛₑₜ B) := not_mem_iff_neg_mem
    have h₇: x ∉ₛₑₜ A → x ∉ₛₑₜ B := by
      assume(h₇₁: x ∉ₛₑₜ A)
      have h₇₂: ¬(x ∈ₛₑₜ A) := PC₀.deductive_eq_l2r h₅ h₇₁
      have h₇₃: ¬(x ∈ₛₑₜ B) := PC₀.deductive_eq_l2r h₄ h₇₂
      have h₇₄: (x ∉ₛₑₜ B) := PC₀.deductive_eq_r2l h₆ h₇₃
      iterate h₇₄
    have h₈: x ∉ₛₑₜ B → x ∉ₛₑₜ A := by
      assume(h₈₁: x ∉ₛₑₜ B)
      have h₈₂: ¬(x ∈ₛₑₜ B) := PC₀.deductive_eq_l2r h₆ h₈₁
      have h₈₃: ¬(x ∈ₛₑₜ A) := PC₀.deductive_eq_r2l h₄ h₈₂
      have h₈₄: (x ∉ₛₑₜ A) := PC₀.deductive_eq_r2l h₅ h₈₃
      iterate h₈₄
    have h₉: x ∉ₛₑₜ A ↔ x ∉ₛₑₜ B := by iff_intro h₇, h₈
    iterate h₉
  { pred:= pred, cong:= cong }

def not_mem_predicate: CongruentBinaryPredicate U (Set U) :=
  let pred:= (x: U.Particular ↦ not_mem_unary x)
  let cong: ∀ (x: U.Particular), ∀ (y: U.Particular), ∀ (X: (Set U).Particular), x =₍U₎ y → (x ∉ₛₑₜ X ↔ y ∉ₛₑₜ X) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    variable(S: (Set U).Particular)
    have h₁: ∀ (y: U.Particular), ∀ (X: (Set U).Particular), a =₍U₎ y → (¬(a ∈ₛₑₜ X) ↔ ¬(y ∈ₛₑₜ X)) := by forall_elim (negation_preserves_congruence2 mem_predicate), a
    have h₂: ∀ (X: (Set U).Particular), a =₍U₎ b → (¬(a ∈ₛₑₜ X) ↔ ¬(b ∈ₛₑₜ X)) := by forall_elim h₁, b
    have h₃: a =₍U₎ b → (¬(a ∈ₛₑₜ S) ↔ ¬(b ∈ₛₑₜ S)) := by forall_elim h₂, S
    assume(h₄: a =₍U₎ b)
    have h₅: (¬(a ∈ₛₑₜ S) ↔ ¬(b ∈ₛₑₜ S)) := by modus_ponens h₃, h₄
    have h₆: a ∉ₛₑₜ S → b ∉ₛₑₜ S := by
      assume(h₆₁: a ∉ₛₑₜ S)
      have h₆₂: ¬(a ∈ₛₑₜ S) := PC₀.deductive_eq_l2r not_mem_iff_neg_mem h₆₁
      have h₆₃: ¬(b ∈ₛₑₜ S) := PC₀.deductive_eq_l2r h₅ h₆₂
      have h₆₄: b ∉ₛₑₜ S := PC₀.deductive_eq_r2l not_mem_iff_neg_mem h₆₃
      iterate h₆₄
    have h₇: b ∉ₛₑₜ S → a ∉ₛₑₜ S := by
      assume(h₇₁: b ∉ₛₑₜ S)
      have h₇₂: ¬(b ∈ₛₑₜ S) := PC₀.deductive_eq_l2r not_mem_iff_neg_mem h₇₁
      have h₇₃: ¬(a ∈ₛₑₜ S) := PC₀.deductive_eq_r2l h₅ h₇₂
      have h₇₄: a ∉ₛₑₜ S := PC₀.deductive_eq_r2l not_mem_iff_neg_mem h₇₃
      iterate h₇₄
    have h₈: a ∉ₛₑₜ S ↔ b ∉ₛₑₜ S := by iff_intro h₆, h₇
    iterate h₈
  { pred:= pred, cong:= cong }


end Sets

end Universe
