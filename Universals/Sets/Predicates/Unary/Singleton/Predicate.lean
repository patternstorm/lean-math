import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Properties.SetExtensionality

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND


-- # Congruence for the singleton predicate.
--
-- Manual proof: the body `∃!₍U₎ x, x ∈ₛₑₜ S` varies in S through the
-- membership predicate. We unpack via `Sets.set_extensionality` (to lift
-- `S =ₛₑₜ S'` to pointwise membership equivalence) and `exists_unique_def`
-- (to convert `∃!₍U₎` to a plain ∃ + uniqueness), repackaging on the other side.
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-05-31
theorem is_singleton_cong: ∀ (S: Set U), ∀ (S': Set U),
      S =ₛₑₜ S' → ((∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S) ↔ (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S')) := by forall_intro
  variable(S: Set U)
  variable(S': Set U)
  assume(h₁: S =ₛₑₜ S')
  -- From set extensionality, S =ₛₑₜ S' gives us pointwise membership equivalence.
  have h₂: ∀ (X: Set U), S =ₛₑₜ X ↔ (∀ (x: U.Particular), x ∈ₛₑₜ S ↔ x ∈ₛₑₜ X) := by forall_elim set_extensionality, S
  have h₃: S =ₛₑₜ S' ↔ (∀ (x: U.Particular), x ∈ₛₑₜ S ↔ x ∈ₛₑₜ S') := by forall_elim h₂, S'
  have h₄: ∀ (x: U.Particular), x ∈ₛₑₜ S ↔ x ∈ₛₑₜ S' := PC₀.deductive_eq_l2r h₃ h₁
  -- Unpack ExistsUnique via the axiom schema.
  have h₅: ∀ (P: U.Particular → Prop), ExistsUnique U P ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x)) := by forall_elim exists_unique_def, U
  have h₆: ExistsUnique U (x: U.Particular ↦ x ∈ₛₑₜ S) ↔ (∃ (x: U.Particular), x ∈ₛₑₜ S ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ x)) := by forall_elim h₅, (x: U.Particular ↦ x ∈ₛₑₜ S)
  have h₇: ExistsUnique U (x: U.Particular ↦ x ∈ₛₑₜ S') ↔ (∃ (x: U.Particular), x ∈ₛₑₜ S' ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ x)) := by forall_elim h₅, (x: U.Particular ↦ x ∈ₛₑₜ S')
  -- Forward: ∃!₍U₎ x, x ∈ₛₑₜ S → ∃!₍U₎ x, x ∈ₛₑₜ S'.
  have h₈: (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S) → (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S') := by
    assume(h₈₁: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S)
    have h₈₂: ∃ (x: U.Particular), x ∈ₛₑₜ S ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ x) := PC₀.deductive_eq_l2r h₆ h₈₁
    have ⟨(w: U.Particular), (h₈₃: w ∈ₛₑₜ S ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ w))⟩ := exists_elim h₈₂
    have h₈₄: w ∈ₛₑₜ S := by and_elim h₈₃
    have h₈₅: ∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ w := by and_elim h₈₃
    -- Convert membership: w ∈ₛₑₜ S → w ∈ₛₑₜ S'.
    have h₈₆: w ∈ₛₑₜ S ↔ w ∈ₛₑₜ S' := by forall_elim h₄, w
    have h₈₇: w ∈ₛₑₜ S' := PC₀.deductive_eq_l2r h₈₆ h₈₄
    -- Convert uniqueness: ∀ y, y ∈ₛₑₜ S' → y =₍U₎ w.
    have h₈₈: ∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ w := by forall_intro
      variable(v: U.Particular)
      assume(h₈₈₁: v ∈ₛₑₜ S')
      have h₈₈₂: v ∈ₛₑₜ S ↔ v ∈ₛₑₜ S' := by forall_elim h₄, v
      have h₈₈₃: v ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₈₈₂ h₈₈₁
      have h₈₈₄: v ∈ₛₑₜ S → v =₍U₎ w := by forall_elim h₈₅, v
      have h₈₈₅: v =₍U₎ w := by modus_ponens h₈₈₄, h₈₈₃
      iterate h₈₈₅
    -- Repack: ∃ x, ... → ∃!₍U₎ x, x ∈ₛₑₜ S'.
    have h₈₉: w ∈ₛₑₜ S' ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ w) := by and_intro h₈₇, h₈₈
    have h₈₁₀: ∃ (x: U.Particular), x ∈ₛₑₜ S' ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ x) := by exists_intro h₈₉, w
    have h₈₁₁: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S' := PC₀.deductive_eq_r2l h₇ h₈₁₀
    iterate h₈₁₁
  -- Backward: symmetric.
  have h₉: (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S') → (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S) := by
    assume(h₉₁: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S')
    have h₉₂: ∃ (x: U.Particular), x ∈ₛₑₜ S' ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ x) := PC₀.deductive_eq_l2r h₇ h₉₁
    have ⟨(w: U.Particular), (h₉₃: w ∈ₛₑₜ S' ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ w))⟩ := exists_elim h₉₂
    have h₉₄: w ∈ₛₑₜ S' := by and_elim h₉₃
    have h₉₅: ∀ (y: U.Particular), y ∈ₛₑₜ S' → y =₍U₎ w := by and_elim h₉₃
    have h₉₆: w ∈ₛₑₜ S ↔ w ∈ₛₑₜ S' := by forall_elim h₄, w
    have h₉₇: w ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₉₆ h₉₄
    have h₉₈: ∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ w := by forall_intro
      variable(v: U.Particular)
      assume(h₉₈₁: v ∈ₛₑₜ S)
      have h₉₈₂: v ∈ₛₑₜ S ↔ v ∈ₛₑₜ S' := by forall_elim h₄, v
      have h₉₈₃: v ∈ₛₑₜ S' := PC₀.deductive_eq_l2r h₉₈₂ h₉₈₁
      have h₉₈₄: v ∈ₛₑₜ S' → v =₍U₎ w := by forall_elim h₉₅, v
      have h₉₈₅: v =₍U₎ w := by modus_ponens h₉₈₄, h₉₈₃
      iterate h₉₈₅
    have h₉₉: w ∈ₛₑₜ S ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ w) := by and_intro h₉₇, h₉₈
    have h₉₁₀: ∃ (x: U.Particular), x ∈ₛₑₜ S ∧ (∀ (y: U.Particular), y ∈ₛₑₜ S → y =₍U₎ x) := by exists_intro h₉₉, w
    have h₉₁₁: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₆ h₉₁₀
    iterate h₉₁₁
  have h₁₀: (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S) ↔ (∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S') := by iff_intro h₈, h₉
  iterate h₁₀


-- # Singleton predicate
-- A set S is a singleton if it has exactly one element.
unary_predicate is_singleton : (S : (𝐒𝐞𝐭 U).Particular ↦ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S) with is_singleton_cong


end Sets

end Universe
