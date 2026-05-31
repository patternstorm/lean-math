import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND

-- Preservation theorem: fixing the first argument of a `CongruentTernaryPredicate`
-- yields a binary predicate over the remaining two arguments that is congruent
-- in both. Derived from the combined cong by instantiating with reflexivity on
-- the first argument.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem fiber_first_preserves_congruence {U₁ U₂ U₃: Universal} (P: CongruentTernaryPredicate U₁ U₂ U₃) (x: U₁.Particular):
    ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      y₁ =₍U₂₎ y₂ → z₁ =₍U₃₎ z₂ → (P.pred x y₁ z₁ ↔ P.pred x y₂ z₂) := by forall_intro
  variable(b₁: U₂.Particular)
  variable(b₂: U₂.Particular)
  variable(c₁: U₃.Particular)
  variable(c₂: U₃.Particular)
  assume(h₁: b₁ =₍U₂₎ b₂)
  assume(h₂: c₁ =₍U₃₎ c₂)
  have h₃: x =₍U₁₎ x → b₁ =₍U₂₎ b₂ → c₁ =₍U₃₎ c₂ → (P.pred x b₁ c₁ ↔ P.pred x b₂ c₂) := by forall_elim P.cong, x, x, b₁, b₂, c₁, c₂
  have h₄: x =₍U₁₎ x := U₁.eq.refl x
  have h₅: b₁ =₍U₂₎ b₂ → c₁ =₍U₃₎ c₂ → (P.pred x b₁ c₁ ↔ P.pred x b₂ c₂) := by modus_ponens h₃, h₄
  have h₆: c₁ =₍U₃₎ c₂ → (P.pred x b₁ c₁ ↔ P.pred x b₂ c₂) := by modus_ponens h₅, h₁
  have h₇: P.pred x b₁ c₁ ↔ P.pred x b₂ c₂ := by modus_ponens h₆, h₂
  iterate h₇

-- Auto-inference: fixing the first argument of a `CongruentTernaryPredicate`
-- yields a `CongruentBinary` body in the remaining two arguments. Each cong
-- direction (inner/outer) is derived from `P.cong` directly with refls on
-- the unchanged arguments.
instance fiber_first_congruent_binary {U₁ U₂ U₃: Universal}
    (P: CongruentTernaryPredicate U₁ U₂ U₃) (x: U₁.Particular):
    CongruentBinary U₂ U₃ (fun y z => P.pred x y z) where
  inner_cong: ∀ (y: U₂.Particular), ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      z₁ =₍U₃₎ z₂ → (P.pred x y z₁ ↔ P.pred x y z₂) := by forall_intro
    variable(y: U₂.Particular)
    variable(z₁: U₃.Particular)
    variable(z₂: U₃.Particular)
    assume(h₁: z₁ =₍U₃₎ z₂)
    have h₂: ∀ (x₂': U₁.Particular), ∀ (y₁': U₂.Particular), ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x₂' → y₁' =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁' z₁' ↔ P.pred x₂' y₂' z₂') := by forall_elim P.cong, x
    have h₃: ∀ (y₁': U₂.Particular), ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y₁' =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁' z₁' ↔ P.pred x y₂' z₂') := by forall_elim h₂, x
    have h₄: ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y z₁' ↔ P.pred x y₂' z₂') := by forall_elim h₃, y
    have h₅: ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y =₍U₂₎ y → z₁' =₍U₃₎ z₂' → (P.pred x y z₁' ↔ P.pred x y z₂') := by forall_elim h₄, y
    have h₆: ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y =₍U₂₎ y → z₁ =₍U₃₎ z₂' → (P.pred x y z₁ ↔ P.pred x y z₂') := by forall_elim h₅, z₁
    have h₇: x =₍U₁₎ x → y =₍U₂₎ y → z₁ =₍U₃₎ z₂ → (P.pred x y z₁ ↔ P.pred x y z₂) := by forall_elim h₆, z₂
    have h₈: x =₍U₁₎ x := U₁.eq.refl x
    have h₉: y =₍U₂₎ y := U₂.eq.refl y
    have h₁₀: y =₍U₂₎ y → z₁ =₍U₃₎ z₂ → (P.pred x y z₁ ↔ P.pred x y z₂) := by modus_ponens h₇, h₈
    have h₁₁: z₁ =₍U₃₎ z₂ → (P.pred x y z₁ ↔ P.pred x y z₂) := by modus_ponens h₁₀, h₉
    have h₁₂: P.pred x y z₁ ↔ P.pred x y z₂ := by modus_ponens h₁₁, h₁
    iterate h₁₂
  outer_cong: ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), ∀ (z: U₃.Particular),
      y₁ =₍U₂₎ y₂ → (P.pred x y₁ z ↔ P.pred x y₂ z) := by forall_intro
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    variable(z: U₃.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    have h₂: ∀ (x₂': U₁.Particular), ∀ (y₁': U₂.Particular), ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x₂' → y₁' =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁' z₁' ↔ P.pred x₂' y₂' z₂') := by forall_elim P.cong, x
    have h₃: ∀ (y₁': U₂.Particular), ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y₁' =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁' z₁' ↔ P.pred x y₂' z₂') := by forall_elim h₂, x
    have h₄: ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y₁ =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁ z₁' ↔ P.pred x y₂' z₂') := by forall_elim h₃, y₁
    have h₅: ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y₁ =₍U₂₎ y₂ → z₁' =₍U₃₎ z₂' → (P.pred x y₁ z₁' ↔ P.pred x y₂ z₂') := by forall_elim h₄, y₂
    have h₆: ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y₁ =₍U₂₎ y₂ → z =₍U₃₎ z₂' → (P.pred x y₁ z ↔ P.pred x y₂ z₂') := by forall_elim h₅, z
    have h₇: x =₍U₁₎ x → y₁ =₍U₂₎ y₂ → z =₍U₃₎ z → (P.pred x y₁ z ↔ P.pred x y₂ z) := by forall_elim h₆, z
    have h₈: x =₍U₁₎ x := U₁.eq.refl x
    have h₉: z =₍U₃₎ z := U₃.eq.refl z
    have h₁₀: y₁ =₍U₂₎ y₂ → z =₍U₃₎ z → (P.pred x y₁ z ↔ P.pred x y₂ z) := by modus_ponens h₇, h₈
    have h₁₁: z =₍U₃₎ z → (P.pred x y₁ z ↔ P.pred x y₂ z) := by modus_ponens h₁₀, h₁
    have h₁₂: P.pred x y₁ z ↔ P.pred x y₂ z := by modus_ponens h₁₁, h₉
    iterate h₁₂

end PC₁

end Logic
