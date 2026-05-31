import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.NonMembership.Predicate

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Non-membership is logically equivalent to negated membership.
-- I.e., `x ∉ₛₑₜ A ↔ ¬(x ∈ₛₑₜ A)`. Both `mem` and `not_mem` are opaque
-- predicate symbols introduced by the `binary_predicate` macro; their
-- propositional bridges (`mem.def`, `not_mem.def`) connect them back to
-- `A.pred x` and `¬(A.pred x)` respectively. The equivalence follows by
-- chaining those bridges with `iff_contrapositiveness`.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem not_mem_is_neg_mem {A: Set U} {u: U.Particular}: (u ∉ₛₑₜ A) ↔ ¬(u ∈ₛₑₜ A) := by
  have h₁: ∀ (x: U.Particular), ∀ (S: (𝐒𝐞𝐭 U).Particular), not_mem x S ↔ ¬(S.pred x) := not_mem.def
  have h₂: ∀ (S: (𝐒𝐞𝐭 U).Particular), not_mem u S ↔ ¬(S.pred u) := by forall_elim h₁, u
  have h₃: not_mem u A ↔ ¬(A.pred u) := by forall_elim h₂, A
  have h₄: ∀ (x: U.Particular), ∀ (S: (𝐒𝐞𝐭 U).Particular), mem x S ↔ S.pred x := mem.def
  have h₅: ∀ (S: (𝐒𝐞𝐭 U).Particular), mem u S ↔ S.pred u := by forall_elim h₄, u
  have h₆: mem u A ↔ A.pred u := by forall_elim h₅, A
  have h₇: (mem u A ↔ A.pred u) ↔ (¬(mem u A) ↔ ¬(A.pred u)) := PC₀.iff_contrapositiveness
  have h₈: ¬(mem u A) ↔ ¬(A.pred u) := PC₀.deductive_eq_l2r h₇ h₆
  have h₉: (u ∉ₛₑₜ A) → ¬(u ∈ₛₑₜ A) := by
    assume(h₉₁: u ∉ₛₑₜ A)
    have h₉₂: ¬(A.pred u) := PC₀.deductive_eq_l2r h₃ h₉₁
    have h₉₃: ¬(u ∈ₛₑₜ A) := PC₀.deductive_eq_r2l h₈ h₉₂
    iterate h₉₃
  have h₁₀: ¬(u ∈ₛₑₜ A) → (u ∉ₛₑₜ A) := by
    assume(h₁₀₁: ¬(u ∈ₛₑₜ A))
    have h₁₀₂: ¬(A.pred u) := PC₀.deductive_eq_l2r h₈ h₁₀₁
    have h₁₀₃: u ∉ₛₑₜ A := PC₀.deductive_eq_r2l h₃ h₁₀₂
    iterate h₁₀₃
  iff_intro h₉, h₁₀


end Sets

end Universe
