import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Properties.SetExtensionality
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁
open Logic.ND

-- # Singleton Element Extraction
-- Extracts the unique element from a singleton set.
axiom singleton_elem: SingletonSet U → U.Particular
prefix:max "⊙" => singleton_elem

axiom singleton_elem_def: ∀ (S: SingletonSet U), ∀ (y: U.Particular), y =₍U₎ (⊙ S) ↔ y ∈ₛₑₜ S

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
noncomputable def singleton_elem_operation: CongruentUnaryOperation (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) U :=
  let op: SingletonSet U → U.Particular := singleton_elem
  let cong: ∀ (S₁: SingletonSet U), ∀ (S₂: SingletonSet U), S₁ =₍𝐒𝐞𝐭 U₎ S₂ → (⊙ S₁ =₍U₎ ⊙ S₂) := by forall_intro
    variable(S₁: SingletonSet U)
    variable(S₂: SingletonSet U)

    -- Instantiate singleton_elem_def for S₁ and S₂
    have h₁: ∀ (y: U.Particular), y =₍U₎ (⊙ S₁) ↔ y ∈ₛₑₜ S₁ := by forall_elim singleton_elem_def, S₁
    have h₂: ∀ (y: U.Particular), y =₍U₎ (⊙ S₂) ↔ y ∈ₛₑₜ S₂ := by forall_elim singleton_elem_def, S₂

    -- Set extensionality
    have h₃: ∀ (S: Set U), S₁ =₍𝐒𝐞𝐭 U₎ S ↔ (∀ (x: U.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ S) := by forall_elim set_extensionality (U := U), S₁
    have h₄: S₁ =₍𝐒𝐞𝐭 U₎ S₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ S₂) := by forall_elim h₃, S₂

    assume(h₅: S₁ =₍𝐒𝐞𝐭 U₎ S₂)

    -- Derive membership equivalence
    have h₆: ∀ (x: U.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ S₂ := PC₀.deductive_eq_l2r h₄ h₅

    -- Instantiate everything at ⊙ S₁
    have h₇: (⊙ S₁) =₍U₎ (⊙ S₁) ↔ (⊙ S₁) ∈ₛₑₜ S₁ := by forall_elim h₁, (⊙ S₁)
    have h₈: (⊙ S₁) =₍U₎ (⊙ S₂) ↔ (⊙ S₁) ∈ₛₑₜ S₂ := by forall_elim h₂, (⊙ S₁)
    have h₉: (⊙ S₁) ∈ₛₑₜ S₁ ↔ (⊙ S₁) ∈ₛₑₜ S₂ := by forall_elim h₆, (⊙ S₁)

    -- Chain: reflexivity → membership in S₁ → membership in S₂ → equality
    have h₁₀: (⊙ S₁) =₍U₎ (⊙ S₁) := U.eq.refl (⊙ S₁)
    have h₁₁: (⊙ S₁) ∈ₛₑₜ S₁ := PC₀.deductive_eq_l2r h₇ h₁₀
    have h₁₂: (⊙ S₁) ∈ₛₑₜ S₂ := PC₀.deductive_eq_l2r h₉ h₁₁
    have h₁₃: (⊙ S₁) =₍U₎ (⊙ S₂) := PC₀.deductive_eq_r2l h₈ h₁₂
    iterate h₁₃
  { op := op, cong := cong }

end Sets

end Universe
