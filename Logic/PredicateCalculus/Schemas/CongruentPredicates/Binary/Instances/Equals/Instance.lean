import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

-- # Equals: the binary equality predicate as a `CongruentBinaryPredicate U U`.
-- The combined cong proof is derived from `U.eq.sym` and `U.eq.trans`:
-- if `x₁ =₍U₎ x₂` and `y₁ =₍U₎ y₂`, then `x₁ =₍U₎ y₁ ↔ x₂ =₍U₎ y₂`
-- by chaining through `a₂ =₍U₎ a₁ ∧ a₁ =₍U₎ b₁ → a₂ =₍U₎ b₁`
-- and `a₂ =₍U₎ b₁ ∧ b₁ =₍U₎ b₂ → a₂ =₍U₎ b₂` (and a symmetric chain for the reverse).
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
def equals: CongruentBinaryPredicate U U :=
  let pred: U.Particular → U.Particular → Prop := (x: U.Particular, y: U.Particular ↦ x =₍U₎ y)
  let cong: ∀ (x₁: U.Particular), ∀ (x₂: U.Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular),
        x₁ =₍U₎ x₂ → y₁ =₍U₎ y₂ → (pred x₁ y₁ ↔ pred x₂ y₂) := by forall_intro
    variable(a₁: U.Particular)
    variable(a₂: U.Particular)
    variable(b₁: U.Particular)
    variable(b₂: U.Particular)
    assume(h₁: a₁ =₍U₎ a₂)
    assume(h₂: b₁ =₍U₎ b₂)
    -- Forward direction: pred a₁ b₁ → pred a₂ b₂ — i.e. a₁ =₍U₎ b₁ → a₂ =₍U₎ b₂
    have h₃: pred a₁ b₁ → pred a₂ b₂ := by
      assume(h₃₁: a₁ =₍U₎ b₁)
      -- a₂ =₍U₎ a₁ via sym on h₁
      have h₃₂: a₁ =₍U₎ a₂ → a₂ =₍U₎ a₁ := by forall_elim U.eq.sym, a₁, a₂
      have h₃₃: a₂ =₍U₎ a₁ := by modus_ponens h₃₂, h₁
      -- a₂ =₍U₎ b₁ via trans on (a₂ =₍U₎ a₁) ∧ (a₁ =₍U₎ b₁)
      have h₃₄: a₂ =₍U₎ a₁ ∧ a₁ =₍U₎ b₁ := by and_intro h₃₃, h₃₁
      have h₃₅: a₂ =₍U₎ a₁ ∧ a₁ =₍U₎ b₁ → a₂ =₍U₎ b₁ := by forall_elim U.eq.trans, a₂, a₁, b₁
      have h₃₆: a₂ =₍U₎ b₁ := by modus_ponens h₃₅, h₃₄
      -- a₂ =₍U₎ b₂ via trans on (a₂ =₍U₎ b₁) ∧ (b₁ =₍U₎ b₂)
      have h₃₇: a₂ =₍U₎ b₁ ∧ b₁ =₍U₎ b₂ := by and_intro h₃₆, h₂
      have h₃₈: a₂ =₍U₎ b₁ ∧ b₁ =₍U₎ b₂ → a₂ =₍U₎ b₂ := by forall_elim U.eq.trans, a₂, b₁, b₂
      have h₃₉: a₂ =₍U₎ b₂ := by modus_ponens h₃₈, h₃₇
      iterate h₃₉
    -- Backward direction: pred a₂ b₂ → pred a₁ b₁ — i.e. a₂ =₍U₎ b₂ → a₁ =₍U₎ b₁
    have h₄: pred a₂ b₂ → pred a₁ b₁ := by
      assume(h₄₁: a₂ =₍U₎ b₂)
      -- a₁ =₍U₎ b₂ via trans on (a₁ =₍U₎ a₂) ∧ (a₂ =₍U₎ b₂)
      have h₄₂: a₁ =₍U₎ a₂ ∧ a₂ =₍U₎ b₂ := by and_intro h₁, h₄₁
      have h₄₃: a₁ =₍U₎ a₂ ∧ a₂ =₍U₎ b₂ → a₁ =₍U₎ b₂ := by forall_elim U.eq.trans, a₁, a₂, b₂
      have h₄₄: a₁ =₍U₎ b₂ := by modus_ponens h₄₃, h₄₂
      -- b₂ =₍U₎ b₁ via sym on h₂
      have h₄₅: b₁ =₍U₎ b₂ → b₂ =₍U₎ b₁ := by forall_elim U.eq.sym, b₁, b₂
      have h₄₆: b₂ =₍U₎ b₁ := by modus_ponens h₄₅, h₂
      -- a₁ =₍U₎ b₁ via trans on (a₁ =₍U₎ b₂) ∧ (b₂ =₍U₎ b₁)
      have h₄₇: a₁ =₍U₎ b₂ ∧ b₂ =₍U₎ b₁ := by and_intro h₄₄, h₄₆
      have h₄₈: a₁ =₍U₎ b₂ ∧ b₂ =₍U₎ b₁ → a₁ =₍U₎ b₁ := by forall_elim U.eq.trans, a₁, b₂, b₁
      have h₄₉: a₁ =₍U₎ b₁ := by modus_ponens h₄₈, h₄₇
      iterate h₄₉
    have h₅: pred a₁ b₁ ↔ pred a₂ b₂ := by iff_intro h₃, h₄
    iterate h₅
  { pred := pred, cong := cong }

end PC₁

end Logic
