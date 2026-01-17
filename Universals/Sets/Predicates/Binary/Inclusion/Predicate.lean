import Logic
import Universe
import Universals.Sets.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


axiom inclusion: (Set U).Particular → (Set U).Particular → Prop
notation:50 S₁:51 " ⊆ₛₑₜ " S₂:51 => inclusion S₁ S₂
axiom inclusion_def: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), (S₁ ⊆ₛₑₜ S₂) ↔ ∀ (x: U.Particular), (S₁.pred x → S₂.pred x)

-- Fix first argument A, get predicate in second argument S: "supersets of A"
def supersets_of (A: (Set U).Particular): CongruentUnaryPredicate (Set U) :=
  let pred := (S: Particular U ↦ A ⊆ₛₑₜ S)
  let cong: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), S₁ =ₛₑₜ S₂ → (A ⊆ₛₑₜ S₁ ↔ A ⊆ₛₑₜ S₂) := by forall_intro
    variable(A₁: (Set U).Particular)
    variable(A₂: (Set U).Particular)
    assume(h₁: A₁ =ₛₑₜ A₂)
    have h₂: ∀ (S₂: Particular U), A₁ =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), A₁.pred x ↔ S₂.pred x := by forall_elim eq_def, A₁
    have h₃: A₁ =ₛₑₜ A₂ ↔ ∀ (x: U.Particular), A₁.pred x ↔ A₂.pred x := by forall_elim h₂, A₂
    have h₄: ∀ (x: U.Particular), A₁.pred x ↔ A₂.pred x := PC₀.deductive_eq_l2r h₃ h₁
    have h₅: ∀ (S: (Set U).Particular), (A ⊆ₛₑₜ S) ↔ ∀ (x: U.Particular), (A.pred x → S.pred x) := by forall_elim inclusion_def, A
    have h₆: (A ⊆ₛₑₜ A₁) ↔ ∀ (x: U.Particular), (A.pred x → A₁.pred x) := by forall_elim h₅, A₁
    have h₇: (A ⊆ₛₑₜ A₂) ↔ ∀ (x: U.Particular), (A.pred x → A₂.pred x) := by forall_elim h₅, A₂
    have h₈: A ⊆ₛₑₜ A₁ → A ⊆ₛₑₜ A₂ := by
      assume(h₈₁: A ⊆ₛₑₜ A₁)
      have h₈₂: ∀ (x: U.Particular), (A.pred x → A₁.pred x) := PC₀.deductive_eq_l2r h₆ h₈₁
      have h₈₃: ∀ (x: U.Particular), (A.pred x → A₂.pred x) := by forall_intro
        variable(u: U.Particular)
        assume(h₈₃₁: A.pred u)
        have h₈₃₂: A₁.pred u ↔ A₂.pred u := by forall_elim h₄, u
        have h₈₃₃: A.pred u → A₁.pred u := by forall_elim h₈₂, u
        have h₈₃₄: A₁.pred u := by modus_ponens h₈₃₃, h₈₃₁
        have h₈₃₅: A₂.pred u := PC₀.deductive_eq_l2r h₈₃₂ h₈₃₄
        iterate h₈₃₅
      have h₈₄: (A ⊆ₛₑₜ A₂) := PC₀.deductive_eq_r2l h₇ h₈₃
      iterate h₈₄
    have h₉: A ⊆ₛₑₜ A₂ → A ⊆ₛₑₜ A₁ := by
      assume(h₉₁: A ⊆ₛₑₜ A₂)
      have h₉₂: ∀ (x: U.Particular), (A.pred x → A₂.pred x) := PC₀.deductive_eq_l2r h₇ h₉₁
      have h₉₃: ∀ (x: U.Particular), (A.pred x → A₁.pred x) := by forall_intro
        variable(u: U.Particular)
        assume(h₉₃₁: A.pred u)
        have h₉₃₂: A₁.pred u ↔ A₂.pred u := by forall_elim h₄, u
        have h₉₃₃: A.pred u → A₂.pred u := by forall_elim h₉₂, u
        have h₉₃₄: A₂.pred u := by modus_ponens h₉₃₃, h₉₃₁
        have h₉₃₅: A₁.pred u := PC₀.deductive_eq_r2l h₉₃₂ h₉₃₄
        iterate h₉₃₅
      have h₉₄: (A ⊆ₛₑₜ A₁) := PC₀.deductive_eq_r2l h₆ h₉₃
      iterate h₉₄
    have h₁₀: A ⊆ₛₑₜ A₁ ↔ A ⊆ₛₑₜ A₂ := by iff_intro h₈, h₉
    iterate h₁₀
  { pred:= pred, cong:= cong }

-- Proof by Claude Opus 4.5 (claude-opus-4-5-20251101), 2026-01-17
def inclusion_predicate: CongruentBinaryPredicate (Set U) (Set U) :=
  let pred := (S: (Set U).Particular ↦ supersets_of S)
  let cong: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), ∀ (S: (Set U).Particular), S₁ =ₛₑₜ S₂ → (S₁ ⊆ₛₑₜ S ↔ S₂ ⊆ₛₑₜ S) := by forall_intro
    variable(A₁: (Set U).Particular)
    variable(A₂: (Set U).Particular)
    variable(B: (Set U).Particular)
    assume(h₁: A₁ =ₛₑₜ A₂)
    have h₂: ∀ (S₂: Particular U), A₁ =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), A₁.pred x ↔ S₂.pred x := by forall_elim eq_def, A₁
    have h₃: A₁ =ₛₑₜ A₂ ↔ ∀ (x: U.Particular), A₁.pred x ↔ A₂.pred x := by forall_elim h₂, A₂
    have h₄: ∀ (x: U.Particular), A₁.pred x ↔ A₂.pred x := PC₀.deductive_eq_l2r h₃ h₁
    have h₅: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), (S₁ ⊆ₛₑₜ S₂) ↔ ∀ (x: U.Particular), (S₁.pred x → S₂.pred x) := inclusion_def
    have h₆: ∀ (S₂: (Set U).Particular), (A₁ ⊆ₛₑₜ S₂) ↔ ∀ (x: U.Particular), (A₁.pred x → S₂.pred x) := by forall_elim h₅, A₁
    have h₇: (A₁ ⊆ₛₑₜ B) ↔ ∀ (x: U.Particular), (A₁.pred x → B.pred x) := by forall_elim h₆, B
    have h₈: ∀ (S₂: (Set U).Particular), (A₂ ⊆ₛₑₜ S₂) ↔ ∀ (x: U.Particular), (A₂.pred x → S₂.pred x) := by forall_elim h₅, A₂
    have h₉: (A₂ ⊆ₛₑₜ B) ↔ ∀ (x: U.Particular), (A₂.pred x → B.pred x) := by forall_elim h₈, B
    have h₁₀: A₁ ⊆ₛₑₜ B → A₂ ⊆ₛₑₜ B := by
      assume(h₁₀₁: A₁ ⊆ₛₑₜ B)
      have h₁₀₂: ∀ (x: U.Particular), (A₁.pred x → B.pred x) := PC₀.deductive_eq_l2r h₇ h₁₀₁
      have h₁₀₃: ∀ (x: U.Particular), (A₂.pred x → B.pred x) := by forall_intro
        variable(u: U.Particular)
        assume(h₁₀₃₁: A₂.pred u)
        have h₁₀₃₂: A₁.pred u ↔ A₂.pred u := by forall_elim h₄, u
        have h₁₀₃₃: A₁.pred u := PC₀.deductive_eq_r2l h₁₀₃₂ h₁₀₃₁
        have h₁₀₃₄: A₁.pred u → B.pred u := by forall_elim h₁₀₂, u
        have h₁₀₃₅: B.pred u := by modus_ponens h₁₀₃₄, h₁₀₃₃
        iterate h₁₀₃₅
      have h₁₀₄: (A₂ ⊆ₛₑₜ B) := PC₀.deductive_eq_r2l h₉ h₁₀₃
      iterate h₁₀₄
    have h₁₁: A₂ ⊆ₛₑₜ B → A₁ ⊆ₛₑₜ B := by
      assume(h₁₁₁: A₂ ⊆ₛₑₜ B)
      have h₁₁₂: ∀ (x: U.Particular), (A₂.pred x → B.pred x) := PC₀.deductive_eq_l2r h₉ h₁₁₁
      have h₁₁₃: ∀ (x: U.Particular), (A₁.pred x → B.pred x) := by forall_intro
        variable(u: U.Particular)
        assume(h₁₁₃₁: A₁.pred u)
        have h₁₁₃₂: A₁.pred u ↔ A₂.pred u := by forall_elim h₄, u
        have h₁₁₃₃: A₂.pred u := PC₀.deductive_eq_l2r h₁₁₃₂ h₁₁₃₁
        have h₁₁₃₄: A₂.pred u → B.pred u := by forall_elim h₁₁₂, u
        have h₁₁₃₅: B.pred u := by modus_ponens h₁₁₃₄, h₁₁₃₃
        iterate h₁₁₃₅
      have h₁₁₄: (A₁ ⊆ₛₑₜ B) := PC₀.deductive_eq_r2l h₇ h₁₁₃
      iterate h₁₁₄
    have h₁₂: A₁ ⊆ₛₑₜ B ↔ A₂ ⊆ₛₑₜ B := by iff_intro h₁₀, h₁₁
    iterate h₁₂
  { pred:= pred, cong:= cong }

-- Fix second argument S, get predicate in first argument A: "subsets of S"
-- Derived from inclusion_predicate.cong rather than proved from scratch.
-- Proof by Claude Opus 4.5 (claude-opus-4-5-20251101), 2026-01-17
def subsets_of (A: (Set U).Particular): CongruentUnaryPredicate (Set U) :=
  let pred := (S: (Set U).Particular ↦ S ⊆ₛₑₜ A)
  let cong: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), S₁ =ₛₑₜ S₂ → (S₁ ⊆ₛₑₜ A ↔ S₂ ⊆ₛₑₜ A) := by forall_intro
    variable(A₁: (Set U).Particular)
    variable(A₂: (Set U).Particular)
    assume(h₁: A₁ =ₛₑₜ A₂)
    have h₂: ∀ (S₂: (Set U).Particular), ∀ (S: (Set U).Particular), A₁ =ₛₑₜ S₂ → (A₁ ⊆ₛₑₜ S ↔ S₂ ⊆ₛₑₜ S) := by forall_elim inclusion_predicate.cong, A₁
    have h₃: ∀ (S: (Set U).Particular), A₁ =ₛₑₜ A₂ → (A₁ ⊆ₛₑₜ S ↔ A₂ ⊆ₛₑₜ S) := by forall_elim h₂, A₂
    have h₄: A₁ =ₛₑₜ A₂ → (A₁ ⊆ₛₑₜ A ↔ A₂ ⊆ₛₑₜ A) := by forall_elim h₃, A
    have h₅: A₁ ⊆ₛₑₜ A ↔ A₂ ⊆ₛₑₜ A := by modus_ponens h₄, h₁
    iterate h₅
  { pred := pred, cong := cong }

end Sets

end Universe
