import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

structure Equality (X: Type) where
  pred: X → X → Prop
  refl: ∀ (x: X), pred x x
  sym: ∀ (x: X), ∀ (y: X), pred x y → pred y x
  trans: ∀ (x: X), ∀ (y: X), ∀  (z: X), pred x y ∧ pred y z → pred x z


-- # `CoeFun` for `Equality`: lets us write `eq a b` instead of `eq.pred a b`.
-- Mirrors the `CoeFun` instances on `CongruentUnaryPredicate` / `CongruentBinaryPredicate`,
-- so an `Equality T` value is callable as the binary predicate it carries.
instance {X : Type} : CoeFun (Equality X) (fun _ => X → X → Prop) where
  coe eq := eq.pred


-- # `Equality.cong` — equality is congruent w.r.t. itself.
--
-- For any equality `eq` on `X`, the binary predicate `eq.pred` respects `eq`
-- itself in both arguments: `eq.pred x₁ x₂ → eq.pred y₁ y₂ → (eq.pred x₁ y₁ ↔
-- eq.pred x₂ y₂)`. This is a consequence of `refl + sym + trans` alone — a
-- property of equality as an equivalence relation, not of any framework
-- packaging — and is therefore derived once at the schema, generic over `X`.
--
-- Downstream, this is what `equals : CongruentBinaryPredicate U U` exposes as
-- its `cong` field via a trivial projection (`equals.cong := U.eq.cong`).
-- Without `Equality.cong`, every consumer had to reconstruct this chain
-- externally; with it, the fact that equality is congruent lives in
-- equality's own contract.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-14
theorem Equality.cong {X: Type} (eq: Equality X): ∀ (x₁: X), ∀ (x₂: X), ∀ (y₁: X), ∀ (y₂: X), eq.pred x₁ x₂ → eq.pred y₁ y₂ → (eq.pred x₁ y₁ ↔ eq.pred x₂ y₂) := by forall_intro
  variable(a₁: X)
  variable(a₂: X)
  variable(b₁: X)
  variable(b₂: X)
  assume(h₁: eq.pred a₁ a₂)
  assume(h₂: eq.pred b₁ b₂)
  -- Forward direction: pred a₁ b₁ → pred a₂ b₂
  -- Chain: a₂ =eq a₁ (via sym on h₁), then a₂ =eq b₁ (via trans), then a₂ =eq b₂ (via trans on h₂)
  have h₃: eq.pred a₁ b₁ → eq.pred a₂ b₂ := by
    assume(h₃₁: eq.pred a₁ b₁)
    have h₃₂: eq.pred a₁ a₂ → eq.pred a₂ a₁ := by forall_elim eq.sym, a₁, a₂
    have h₃₃: eq.pred a₂ a₁ := by modus_ponens h₃₂, h₁
    have h₃₄: eq.pred a₂ a₁ ∧ eq.pred a₁ b₁ := by and_intro h₃₃, h₃₁
    have h₃₅: eq.pred a₂ a₁ ∧ eq.pred a₁ b₁ → eq.pred a₂ b₁ := by forall_elim eq.trans, a₂, a₁, b₁
    have h₃₆: eq.pred a₂ b₁ := by modus_ponens h₃₅, h₃₄
    have h₃₇: eq.pred a₂ b₁ ∧ eq.pred b₁ b₂ := by and_intro h₃₆, h₂
    have h₃₈: eq.pred a₂ b₁ ∧ eq.pred b₁ b₂ → eq.pred a₂ b₂ := by forall_elim eq.trans, a₂, b₁, b₂
    have h₃₉: eq.pred a₂ b₂ := by modus_ponens h₃₈, h₃₇
    iterate h₃₉
  -- Backward direction: pred a₂ b₂ → pred a₁ b₁
  -- Chain: a₁ =eq b₂ (via trans on h₁), then b₂ =eq b₁ (via sym on h₂), then a₁ =eq b₁ (via trans)
  have h₄: eq.pred a₂ b₂ → eq.pred a₁ b₁ := by
    assume(h₄₁: eq.pred a₂ b₂)
    have h₄₂: eq.pred a₁ a₂ ∧ eq.pred a₂ b₂ := by and_intro h₁, h₄₁
    have h₄₃: eq.pred a₁ a₂ ∧ eq.pred a₂ b₂ → eq.pred a₁ b₂ := by forall_elim eq.trans, a₁, a₂, b₂
    have h₄₄: eq.pred a₁ b₂ := by modus_ponens h₄₃, h₄₂
    have h₄₅: eq.pred b₁ b₂ → eq.pred b₂ b₁ := by forall_elim eq.sym, b₁, b₂
    have h₄₆: eq.pred b₂ b₁ := by modus_ponens h₄₅, h₂
    have h₄₇: eq.pred a₁ b₂ ∧ eq.pred b₂ b₁ := by and_intro h₄₄, h₄₆
    have h₄₈: eq.pred a₁ b₂ ∧ eq.pred b₂ b₁ → eq.pred a₁ b₁ := by forall_elim eq.trans, a₁, b₂, b₁
    have h₄₉: eq.pred a₁ b₁ := by modus_ponens h₄₈, h₄₇
    iterate h₄₉
  have h₅: eq.pred a₁ b₁ ↔ eq.pred a₂ b₂ := by iff_intro h₃, h₄
  iterate h₅

end PC₁

end Logic
