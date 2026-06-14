import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

open ND

-- Preservation theorem: fixing the second argument of a `CongruentBinaryPredicate`
-- yields a unary predicate that respects U₁'s equality. Proven once from the
-- combined cong by instantiating with reflexivity on the second argument.
-- Name carries `_binary_` to mirror `fiber_first_preserves_binary_congruence`
-- (the analogous higher-arity theorems live in the `Ternary` schemas).
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem fiber_second_preserves_binary_congruence {U₁ U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂) (y: U₂.Particular):
    ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), x₁ =₍U₁₎ x₂ → (P.pred x₁ y ↔ P.pred x₂ y) := by forall_intro
  variable(a: U₁.Particular)
  variable(b: U₁.Particular)
  assume(h₁: a =₍U₁₎ b)
  have h₂: a =₍U₁₎ b → y =₍U₂₎ y → (P.pred a y ↔ P.pred b y) := by forall_elim P.cong, a, b, y, y
  have h₃: y =₍U₂₎ y := U₂.eq.refl y
  have h₄: y =₍U₂₎ y → (P.pred a y ↔ P.pred b y) := by modus_ponens h₂, h₁
  have h₅: P.pred a y ↔ P.pred b y := by modus_ponens h₄, h₃
  iterate h₅

-- Auto-inference: a fiber of a `CongruentBinaryPredicate` (fix second arg) is a
-- `CongruentUnary` body. Lets the auto-cong machinery recognize `fun x => P.pred x y`
-- as congruent in `x` whenever `P` is congruent and `y` is fixed.
instance fiber_second_binary_congruent_unary {U₁ U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂) (y: U₂.Particular):
    CongruentUnary U₁ (fun x => P.pred x y) where
  cong := fiber_second_preserves_binary_congruence P y

end PC₁

end Logic
