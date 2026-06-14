import Logic
import Universe
import Universals.Sets.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # `Set` Inclusion predicate
-- `S` is included in `S'` if every member of `S` is also a member of `S'`.
--
-- Congruence is not auto-derivable because varying either Set requires
-- unfolding `Sets.eq_def` — a Sets-specific fact that the generic auto-cong
-- machinery does not (and should not) know. We prove combined cong inline
-- below; the fibers `supersets_of` and `subsets_of` derive their unary cong
-- for free via the framework's `fiber_first_preserves_binary_congruence` /
-- `fiber_second_preserves_binary_congruence`.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
binary_predicate inclusion : (S : (𝐒𝐞𝐭 U).Particular, S' : (𝐒𝐞𝐭 U).Particular ↦ ∀ (x: U.Particular), S.pred x → S'.pred x)
  with cong:
    ∀ (S: Set U), ∀ (S': Set U), ∀ (T: Set U), ∀ (T': Set U), S =ₛₑₜ S' → T =ₛₑₜ T' → ((∀ (x: U.Particular), S.pred x → T.pred x) ↔ (∀ (x: U.Particular), S'.pred x → T'.pred x)) := by forall_intro
      variable(S: Set U)
      variable(S': Set U)
      variable(T: Set U)
      variable(T': Set U)
      assume(h₁: S =ₛₑₜ S')
      assume(h₂: T =ₛₑₜ T')
      -- Unpack S =ₛₑₜ S' via Sets.eq_def.
      have h₃: ∀ (X: Set U), S =ₛₑₜ X ↔ ∀ (x: U.Particular), S.pred x ↔ X.pred x := by forall_elim eq_def, S
      have h₄: S =ₛₑₜ S' ↔ ∀ (x: U.Particular), S.pred x ↔ S'.pred x := by forall_elim h₃, S'
      have h₅: ∀ (x: U.Particular), S.pred x ↔ S'.pred x := PC₀.deductive_eq_l2r h₄ h₁
      -- Unpack T =ₛₑₜ T' via Sets.eq_def.
      have h₆: ∀ (X: Set U), T =ₛₑₜ X ↔ ∀ (x: U.Particular), T.pred x ↔ X.pred x := by forall_elim eq_def, T
      have h₇: T =ₛₑₜ T' ↔ ∀ (x: U.Particular), T.pred x ↔ T'.pred x := by forall_elim h₆, T'
      have h₈: ∀ (x: U.Particular), T.pred x ↔ T'.pred x := PC₀.deductive_eq_l2r h₇ h₂
      -- Forward direction.
      have h₉: (∀ (x: U.Particular), S.pred x → T.pred x) → (∀ (x: U.Particular), S'.pred x → T'.pred x) := by
        assume(h₉₁: ∀ (x: U.Particular), S.pred x → T.pred x)
        have h₉₂: ∀ (x: U.Particular), S'.pred x → T'.pred x := by forall_intro
          variable(a: U.Particular)
          assume(h₉₂₁: S'.pred a)
          have h₉₂₂: S.pred a ↔ S'.pred a := by forall_elim h₅, a
          have h₉₂₃: S.pred a := PC₀.deductive_eq_r2l h₉₂₂ h₉₂₁
          have h₉₂₄: S.pred a → T.pred a := by forall_elim h₉₁, a
          have h₉₂₅: T.pred a := by modus_ponens h₉₂₄, h₉₂₃
          have h₉₂₆: T.pred a ↔ T'.pred a := by forall_elim h₈, a
          have h₉₂₇: T'.pred a := PC₀.deductive_eq_l2r h₉₂₆ h₉₂₅
          iterate h₉₂₇
        iterate h₉₂
      -- Backward direction.
      have h₁₀: (∀ (x: U.Particular), S'.pred x → T'.pred x) → (∀ (x: U.Particular), S.pred x → T.pred x) := by
        assume(h₁₀₁: ∀ (x: U.Particular), S'.pred x → T'.pred x)
        have h₁₀₂: ∀ (x: U.Particular), S.pred x → T.pred x := by forall_intro
          variable(a: U.Particular)
          assume(h₁₀₂₁: S.pred a)
          have h₁₀₂₂: S.pred a ↔ S'.pred a := by forall_elim h₅, a
          have h₁₀₂₃: S'.pred a := PC₀.deductive_eq_l2r h₁₀₂₂ h₁₀₂₁
          have h₁₀₂₄: S'.pred a → T'.pred a := by forall_elim h₁₀₁, a
          have h₁₀₂₅: T'.pred a := by modus_ponens h₁₀₂₄, h₁₀₂₃
          have h₁₀₂₆: T.pred a ↔ T'.pred a := by forall_elim h₈, a
          have h₁₀₂₇: T.pred a := PC₀.deductive_eq_r2l h₁₀₂₆ h₁₀₂₅
          iterate h₁₀₂₇
        iterate h₁₀₂
      have h₁₁: (∀ (x: U.Particular), S.pred x → T.pred x) ↔ (∀ (x: U.Particular), S'.pred x → T'.pred x) := by iff_intro h₉, h₁₀
      iterate h₁₁

notation:50 S:51 " ⊆ₛₑₜ " S':51 => inclusion S S'


-- # Supersets of A
-- The unary predicate "is a superset of A" — fixing A as the first argument
-- of inclusion. Cong is the framework's first-arg fiber preservation.
def supersets_of (A: Set U) : CongruentUnaryPredicate (𝐒𝐞𝐭 U) :=
  { pred := (S : Set U ↦ inclusion A S)
    cong := fiber_first_preserves_binary_congruence (U₁ := 𝐒𝐞𝐭 U) (U₂ := 𝐒𝐞𝐭 U) (inclusion (U := U)) A }


-- # Subsets of A
-- The unary predicate "is a subset of A" — fixing A as the second argument
-- of inclusion. Cong is the framework's second-arg fiber preservation.
def subsets_of (A: Set U) : CongruentUnaryPredicate (𝐒𝐞𝐭 U) :=
  { pred := (S : Set U ↦ inclusion S A)
    cong := fiber_second_preserves_binary_congruence (U₁ := 𝐒𝐞𝐭 U) (U₂ := 𝐒𝐞𝐭 U) (inclusion (U := U)) A }


end Sets

end Universe
