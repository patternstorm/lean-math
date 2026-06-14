import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # `Set` Non-Membership predicate
-- `x` is NOT a member of `S` if it does not satisfy `S`'s defining predicate.
--
-- Congruence is derived from `mem_cong` (imported from Membership) by
-- contrapositive: if `S₁.pred x₁ ↔ S₂.pred x₂` then `¬S₁.pred x₁ ↔ ¬S₂.pred x₂`.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
binary_predicate not_mem : (x : U.Particular, S : (𝐒𝐞𝐭 U).Particular ↦ ¬(S.pred x))
  with cong:
    ∀ (x₁: U.Particular), ∀ (x₂: U.Particular), ∀ (S₁: Set U), ∀ (S₂: Set U), x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (¬S₁.pred x₁ ↔ ¬S₂.pred x₂) := by forall_intro
      variable(x₁: U.Particular)
      variable(x₂: U.Particular)
      variable(S₁: Set U)
      variable(S₂: Set U)
      assume(h₁: x₁ =₍U₎ x₂)
      assume(h₂: S₁ =ₛₑₜ S₂)
      -- Apply `mem_cong` to get the positive equivalence.
      have h₃: ∀ (b: U.Particular), ∀ (T₁: Set U), ∀ (T₂: Set U),
                x₁ =₍U₎ b → T₁ =ₛₑₜ T₂ → (T₁.pred x₁ ↔ T₂.pred b) := by forall_elim mem_cong, x₁
      have h₄: ∀ (T₁: Set U), ∀ (T₂: Set U),
                x₁ =₍U₎ x₂ → T₁ =ₛₑₜ T₂ → (T₁.pred x₁ ↔ T₂.pred x₂) := by forall_elim h₃, x₂
      have h₅: ∀ (T₂: Set U), x₁ =₍U₎ x₂ → S₁ =ₛₑₜ T₂ → (S₁.pred x₁ ↔ T₂.pred x₂) := by forall_elim h₄, S₁
      have h₆: x₁ =₍U₎ x₂ → S₁ =ₛₑₜ S₂ → (S₁.pred x₁ ↔ S₂.pred x₂) := by forall_elim h₅, S₂
      have h₇: S₁ =ₛₑₜ S₂ → (S₁.pred x₁ ↔ S₂.pred x₂) := by modus_ponens h₆, h₁
      have h₈: S₁.pred x₁ ↔ S₂.pred x₂ := by modus_ponens h₇, h₂
      -- Apply contrapositive equivalence: (P ↔ Q) ↔ (¬P ↔ ¬Q).
      have h₉: ¬S₁.pred x₁ ↔ ¬S₂.pred x₂ := PC₀.deductive_eq_l2r PC₀.iff_contrapositiveness h₈
      iterate h₉

notation:50 x:51 " ∉ₛₑₜ " S:51 => not_mem x S


end Sets

end Universe
