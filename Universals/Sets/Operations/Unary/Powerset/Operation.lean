import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Inclusion.Predicate
import Universals.Sets.Properties.SetExtensionality

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- The `Powerset` operation: given a set S, returns the set of all subsets of S.
--
-- In ZFC, the Powerset Axiom must be postulated: "∀A ∃P ∀B (B ∈ P ↔ B ⊆ A)".
-- This is an existence claim — without it, ZFC cannot prove that the collection
-- of all subsets forms a set.
--
-- Our predicate-based approach avoids this. We define powerset as an operation
-- and specify its behavior: S' ∈ 𝒫 S ↔ S' ⊆ S. The predicate `S' ↦ S' ⊆ₛₑₜ S`
-- is well-formed over Set U, so the powerset is simply the extension of this
-- predicate — no existence axiom required.
axiom powerset: (Set U).Particular → (Set (Set U)).Particular
prefix:max "𝒫" => powerset

-- Behavior: S' is in the powerset of S iff S' is a subset of S.
axiom powerset_def: ∀ (S: (Set U).Particular), ∀ (S': (Set U).Particular), S' ∈ₛₑₜ (𝒫 S) ↔ S' ⊆ₛₑₜ S

-- Congruence: powerset respects set equality
-- Proof by Claude Opus 4.5 (claude-opus-4-5-20251101), 2026-01-17
theorem powerset_cong: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), S₁ =ₛₑₜ S₂ → (𝒫 S₁) =ₛₑₜ (𝒫 S₂) := by forall_intro
  variable (S₁: (Set U).Particular)
  variable (S₂: (Set U).Particular)
  assume (h₁: S₁ =ₛₑₜ S₂)

  -- By set extensionality, we need to show: ∀ S', S' ∈ 𝒫 S₁ ↔ S' ∈ 𝒫 S₂
  have h₂: ∀ (S': (Set U).Particular), S' ∈ₛₑₜ (𝒫 S₁) ↔ S' ∈ₛₑₜ (𝒫 S₂) := by forall_intro
    variable (A: (Set U).Particular)
    -- By powerset_def: A ∈ 𝒫 S ↔ A ⊆ S
    have h₂₁: ∀ (S: (Set U).Particular), S ∈ₛₑₜ (𝒫 S₁) ↔ S ⊆ₛₑₜ S₁ := by forall_elim powerset_def, S₁
    have h₂₂: A ∈ₛₑₜ (𝒫 S₁) ↔ A ⊆ₛₑₜ S₁ := by forall_elim h₂₁, A
    have h₂₃: ∀ (S: (Set U).Particular), S ∈ₛₑₜ (𝒫 S₂) ↔ S ⊆ₛₑₜ S₂ := by forall_elim powerset_def, S₂
    have h₂₄: A ∈ₛₑₜ (𝒫 S₂) ↔ A ⊆ₛₑₜ S₂ := by forall_elim h₂₃, A
    -- By supersets_of congruence: if S₁ = S₂, then A ⊆ S₁ ↔ A ⊆ S₂
    have h₂₅: A ⊆ₛₑₜ S₁ ↔ A ⊆ₛₑₜ S₂ := (supersets_of A).cong S₁ S₂ h₁
    -- Chain the equivalences
    have h₂₆: A ∈ₛₑₜ (𝒫 S₁) → A ∈ₛₑₜ (𝒫 S₂) := by
      assume (h₂₆₁: A ∈ₛₑₜ (𝒫 S₁))
      have h₂₆₂: A ⊆ₛₑₜ S₁ := PC₀.deductive_eq_l2r h₂₂ h₂₆₁
      have h₂₆₃: A ⊆ₛₑₜ S₂ := PC₀.deductive_eq_l2r h₂₅ h₂₆₂
      have h₂₆₄: A ∈ₛₑₜ (𝒫 S₂) := PC₀.deductive_eq_r2l h₂₄ h₂₆₃
      iterate h₂₆₄
    have h₂₇: A ∈ₛₑₜ (𝒫 S₂) → A ∈ₛₑₜ (𝒫 S₁) := by
      assume (h₂₇₁: A ∈ₛₑₜ (𝒫 S₂))
      have h₂₇₂: A ⊆ₛₑₜ S₂ := PC₀.deductive_eq_l2r h₂₄ h₂₇₁
      have h₂₇₃: A ⊆ₛₑₜ S₁ := PC₀.deductive_eq_r2l h₂₅ h₂₇₂
      have h₂₇₄: A ∈ₛₑₜ (𝒫 S₁) := PC₀.deductive_eq_r2l h₂₂ h₂₇₃
      iterate h₂₇₄
    iff_intro h₂₆, h₂₇

  -- Convert to set equality via extensionality
  have h₃: ∀ (S: (Set (Set U)).Particular), (𝒫 S₁) =ₛₑₜ S ↔ (∀ (S': (Set U).Particular), S' ∈ₛₑₜ (𝒫 S₁) ↔ S' ∈ₛₑₜ S) := by forall_elim set_extensionality, (𝒫 S₁)
  have h₄: (𝒫 S₁) =ₛₑₜ (𝒫 S₂) ↔ (∀ (S': (Set U).Particular), S' ∈ₛₑₜ (𝒫 S₁) ↔ S' ∈ₛₑₜ (𝒫 S₂)) := by forall_elim h₃, (𝒫 S₂)
  have h₅: (𝒫 S₁) =ₛₑₜ (𝒫 S₂) := PC₀.deductive_eq_r2l h₄ h₂
  iterate h₅

-- Bundle powerset as a CongruentUnaryOperation
noncomputable def powerset_operation: CongruentUnaryOperation (Set U) (Set (Set U)) :=
  { op := powerset, cong := powerset_cong }

end Sets

end Universe
