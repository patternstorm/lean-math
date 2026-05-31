import Logic
import Universe
import Universals.Sets.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Congruence for the set membership predicate.
--
-- This is the cong shape required by `mem`'s body. It's not auto-derivable
-- because varying the `S` argument requires unfolding `Sets.eq_def` — a
-- Sets-specific fact that the generic auto-cong machinery does not (and
-- should not) know. We prove it manually here. `not_mem` reuses this by
-- contrapositive (see `NonMembership/Predicate.lean`).
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem mem_cong:
    ∀ (x₁: U.Particular), ∀ (x₂: U.Particular), ∀ (S₁: Set U), ∀ (S₂: Set U),
      x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (S₁.pred x₁ ↔ S₂.pred x₂) := by forall_intro
  variable(x₁: U.Particular)
  variable(x₂: U.Particular)
  variable(S₁: Set U)
  variable(S₂: Set U)
  assume(h₁: x₁ =₍U₎ x₂)
  assume(h₂: S₁ =ₛₑₜ S₂)
  -- Vary x within S₁ via S₁'s own cong.
  have h₃: ∀ (y: U.Particular), x₁ =₍U₎ y → (S₁.pred x₁ ↔ S₁.pred y) := by forall_elim S₁.cong, x₁
  have h₄: x₁ =₍U₎ x₂ → (S₁.pred x₁ ↔ S₁.pred x₂) := by forall_elim h₃, x₂
  have h₅: S₁.pred x₁ ↔ S₁.pred x₂ := by modus_ponens h₄, h₁
  -- Vary S via Sets.eq_def (pointwise equivalence of preds).
  have h₆: ∀ (S₂': Set U), S₁ =ₛₑₜ S₂' ↔ ∀ (x: U.Particular), S₁.pred x ↔ S₂'.pred x := by forall_elim eq_def, S₁
  have h₇: S₁ =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), S₁.pred x ↔ S₂.pred x := by forall_elim h₆, S₂
  have h₈: ∀ (x: U.Particular), S₁.pred x ↔ S₂.pred x := PC₀.deductive_eq_l2r h₇ h₂
  have h₉: S₁.pred x₂ ↔ S₂.pred x₂ := by forall_elim h₈, x₂
  -- Chain: S₁.pred x₁ ↔ S₁.pred x₂ ↔ S₂.pred x₂
  have h₁₀: S₁.pred x₁ → S₂.pred x₂ := by
    assume(h₁₀₁: S₁.pred x₁)
    have h₁₀₂: S₁.pred x₂ := PC₀.deductive_eq_l2r h₅ h₁₀₁
    have h₁₀₃: S₂.pred x₂ := PC₀.deductive_eq_l2r h₉ h₁₀₂
    iterate h₁₀₃
  have h₁₁: S₂.pred x₂ → S₁.pred x₁ := by
    assume(h₁₁₁: S₂.pred x₂)
    have h₁₁₂: S₁.pred x₂ := PC₀.deductive_eq_r2l h₉ h₁₁₁
    have h₁₁₃: S₁.pred x₁ := PC₀.deductive_eq_r2l h₅ h₁₁₂
    iterate h₁₁₃
  have h₁₂: S₁.pred x₁ ↔ S₂.pred x₂ := by iff_intro h₁₀, h₁₁
  iterate h₁₂


-- # `Set` Membership predicate
-- A `Particular` `x` is a member of the `Set` `S` if it satisfies `S`'s
-- defining predicate. We write `S.pred x` (not `S x`) because a Set is a
-- structure carrying a predicate, not a function itself.
binary_predicate mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ S.pred x) with mem_cong

notation:50 x:51 " ∈ₛₑₜ " S:51 => mem x S


end Sets

end Universe
