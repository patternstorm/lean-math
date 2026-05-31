import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND

-- Preservation theorem: fixing the first two arguments of a
-- `CongruentTernaryPredicate` yields a unary predicate on the third
-- argument that respects U₃'s equality.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem fiber_first_two_preserves_congruence {U₁ U₂ U₃: Universal}
    (P: CongruentTernaryPredicate U₁ U₂ U₃) (x: U₁.Particular) (y: U₂.Particular):
    ∀ (z₁: U₃.Particular), ∀ (z₂: U₃.Particular),
      z₁ =₍U₃₎ z₂ → (P.pred x y z₁ ↔ P.pred x y z₂) := by forall_intro
  variable(c₁: U₃.Particular)
  variable(c₂: U₃.Particular)
  assume(h₁: c₁ =₍U₃₎ c₂)
  have h₂: ∀ (x₂': U₁.Particular), ∀ (y₁': U₂.Particular), ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x₂' → y₁' =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁' z₁' ↔ P.pred x₂' y₂' z₂') := by forall_elim P.cong, x
  have h₃: ∀ (y₁': U₂.Particular), ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y₁' =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y₁' z₁' ↔ P.pred x y₂' z₂') := by forall_elim h₂, x
  have h₄: ∀ (y₂': U₂.Particular), ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y =₍U₂₎ y₂' → z₁' =₍U₃₎ z₂' → (P.pred x y z₁' ↔ P.pred x y₂' z₂') := by forall_elim h₃, y
  have h₅: ∀ (z₁': U₃.Particular), ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y =₍U₂₎ y → z₁' =₍U₃₎ z₂' → (P.pred x y z₁' ↔ P.pred x y z₂') := by forall_elim h₄, y
  have h₆: ∀ (z₂': U₃.Particular), x =₍U₁₎ x → y =₍U₂₎ y → c₁ =₍U₃₎ z₂' → (P.pred x y c₁ ↔ P.pred x y z₂') := by forall_elim h₅, c₁
  have h₇: x =₍U₁₎ x → y =₍U₂₎ y → c₁ =₍U₃₎ c₂ → (P.pred x y c₁ ↔ P.pred x y c₂) := by forall_elim h₆, c₂
  have h₈: x =₍U₁₎ x := U₁.eq.refl x
  have h₉: y =₍U₂₎ y := U₂.eq.refl y
  have h₁₀: y =₍U₂₎ y → c₁ =₍U₃₎ c₂ → (P.pred x y c₁ ↔ P.pred x y c₂) := by modus_ponens h₇, h₈
  have h₁₁: c₁ =₍U₃₎ c₂ → (P.pred x y c₁ ↔ P.pred x y c₂) := by modus_ponens h₁₀, h₉
  have h₁₂: P.pred x y c₁ ↔ P.pred x y c₂ := by modus_ponens h₁₁, h₁
  iterate h₁₂

-- Auto-inference: fixing the first two arguments yields a `CongruentUnary` body
-- on the third argument.
instance fiber_first_two_congruent_unary {U₁ U₂ U₃: Universal}
    (P: CongruentTernaryPredicate U₁ U₂ U₃) (x: U₁.Particular) (y: U₂.Particular):
    CongruentUnary U₃ (fun z => P.pred x y z) where
  cong := fiber_first_two_preserves_congruence P x y

end PC₁

end Logic
