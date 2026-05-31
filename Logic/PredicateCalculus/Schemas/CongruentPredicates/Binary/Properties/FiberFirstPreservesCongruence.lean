import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND

-- Preservation theorem: fixing the first argument of a `CongruentBinaryPredicate`
-- yields a unary predicate that respects U₂'s equality. Proven once from the
-- combined cong by instantiating with reflexivity on the first argument.
-- Name carries `_binary_` because the same shape exists at higher arities
-- (`fiber_first_preserves_congruence` for ternary).
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem fiber_first_preserves_binary_congruence {U₁ U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂) (x: U₁.Particular):
    ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), y₁ =₍U₂₎ y₂ → (P.pred x y₁ ↔ P.pred x y₂) := by forall_intro
  variable(a: U₂.Particular)
  variable(b: U₂.Particular)
  assume(h₁: a =₍U₂₎ b)
  have h₂: x =₍U₁₎ x → a =₍U₂₎ b → (P.pred x a ↔ P.pred x b) := by forall_elim P.cong, x, x, a, b
  have h₃: x =₍U₁₎ x := U₁.eq.refl x
  have h₄: a =₍U₂₎ b → (P.pred x a ↔ P.pred x b) := by modus_ponens h₂, h₃
  have h₅: P.pred x a ↔ P.pred x b := by modus_ponens h₄, h₁
  iterate h₅

-- Auto-inference: a fiber of a `CongruentBinaryPredicate` (fix first arg) is a
-- `CongruentUnary` body. Lets the auto-cong machinery recognize `fun y => P.pred x y`
-- as congruent in `y` whenever `P` is congruent and `x` is fixed.
instance fiber_first_binary_congruent_unary {U₁ U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂) (x: U₁.Particular):
    CongruentUnary U₂ (fun y => P.pred x y) where
  cong := fiber_first_preserves_binary_congruence P x

end PC₁

end Logic
