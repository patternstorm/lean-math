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

-- # Singleton Predicate
-- A set S is a singleton if it has exactly one element.
axiom is_singleton: Set U → Prop
axiom is_singleton_def: ∀ (S: Set U), is_singleton S ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ S

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
def singleton_predicate: CongruentUnaryPredicate (𝐒𝐞𝐭 U) :=
  let pred: Set U → Prop := (S: Set U ↦ is_singleton S)
  let cong: ∀ (S₁: Set U), ∀ (S₂: Set U), S₁ =ₛₑₜ S₂ → (is_singleton S₁ ↔ is_singleton S₂) := by forall_intro
    variable(A: Set U)
    variable(B: Set U)

    -- From set extensionality, A =ₛₑₜ B gives us membership equivalence
    have h₁: ∀ (S₂: Set U), A =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ S₂) := by forall_elim set_extensionality, A
    have h₂: A =ₛₑₜ B ↔ (∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B) := by forall_elim h₁, B

    -- Unfold is_singleton via axiom definition
    have h₃: is_singleton A ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := by forall_elim is_singleton_def, A
    have h₄: is_singleton B ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ B := by forall_elim is_singleton_def, B

    -- Unpack ExistsUnique via the axiom schema
    have h₅: ∀ (P: U.Particular → Prop), ExistsUnique U P ↔ (∃ (x: U.Particular), P x ∧ (∀ (y: U.Particular), P y → y =₍U₎ x)) := by forall_elim exists_unique_def, U
    have h₆: ExistsUnique U (x: U.Particular ↦ x ∈ₛₑₜ A) ↔ (∃ (x: U.Particular), x ∈ₛₑₜ A ∧ (∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ x)) := by forall_elim h₅, (x: U.Particular ↦ x ∈ₛₑₜ A)
    have h₇: ExistsUnique U (x: U.Particular ↦ x ∈ₛₑₜ B) ↔ (∃ (x: U.Particular), x ∈ₛₑₜ B ∧ (∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ x)) := by forall_elim h₅, (x: U.Particular ↦ x ∈ₛₑₜ B)

    assume(h₈: A =ₛₑₜ B)
    have h₉: ∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₂ h₈

    -- Forward: is_singleton A → is_singleton B
    have h₁₀: is_singleton A → is_singleton B := by
      assume(h₁₀₁: is_singleton A)
      -- Unfold: is_singleton A → ∃!₍U₎ → ∃ x, ...
      have h₁₀₂: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := PC₀.deductive_eq_l2r h₃ h₁₀₁
      have h₁₀₃: ∃ (x: U.Particular), x ∈ₛₑₜ A ∧ (∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ x) := PC₀.deductive_eq_l2r h₆ h₁₀₂
      have ⟨(w: U.Particular), (h₁₀₄: w ∈ₛₑₜ A ∧ (∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ w))⟩ := exists_elim h₁₀₃
      have h₁₀₅: w ∈ₛₑₜ A := by and_elim h₁₀₄
      have h₁₀₆: ∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ w := by and_elim h₁₀₄

      -- Convert membership: w ∈ₛₑₜ A → w ∈ₛₑₜ B
      have h₁₀₇: w ∈ₛₑₜ A ↔ w ∈ₛₑₜ B := by forall_elim h₉, w
      have h₁₀₈: w ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₁₀₇ h₁₀₅

      -- Convert uniqueness: ∀ y, y ∈ₛₑₜ B → y =₍U₎ w
      have h₁₀₉: ∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ w := by forall_intro
        variable(v: U.Particular)
        assume(h₁₀₉₁: v ∈ₛₑₜ B)
        have h₁₀₉₂: v ∈ₛₑₜ A ↔ v ∈ₛₑₜ B := by forall_elim h₉, v
        have h₁₀₉₃: v ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₁₀₉₂ h₁₀₉₁
        have h₁₀₉₄: v ∈ₛₑₜ A → v =₍U₎ w := by forall_elim h₁₀₆, v
        have h₁₀₉₅: v =₍U₎ w := by modus_ponens h₁₀₉₄, h₁₀₉₃
        iterate h₁₀₉₅

      -- Repack: ∃ x, ... → ∃!₍U₎ → is_singleton B
      have h₁₀₁₀: w ∈ₛₑₜ B ∧ (∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ w) := by and_intro h₁₀₈, h₁₀₉
      have h₁₀₁₁: ∃ (x: U.Particular), x ∈ₛₑₜ B ∧ (∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ x) := by exists_intro h₁₀₁₀, w
      have h₁₀₁₂: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ B := PC₀.deductive_eq_r2l h₇ h₁₀₁₁
      have h₁₀₁₃: is_singleton B := PC₀.deductive_eq_r2l h₄ h₁₀₁₂
      iterate h₁₀₁₃

    -- Backward: is_singleton B → is_singleton A (symmetric)
    have h₁₁: is_singleton B → is_singleton A := by
      assume(h₁₁₁: is_singleton B)
      have h₁₁₂: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₄ h₁₁₁
      have h₁₁₃: ∃ (x: U.Particular), x ∈ₛₑₜ B ∧ (∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ x) := PC₀.deductive_eq_l2r h₇ h₁₁₂
      have ⟨(w: U.Particular), (h₁₁₄: w ∈ₛₑₜ B ∧ (∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ w))⟩ := exists_elim h₁₁₃
      have h₁₁₅: w ∈ₛₑₜ B := by and_elim h₁₁₄
      have h₁₁₆: ∀ (y: U.Particular), y ∈ₛₑₜ B → y =₍U₎ w := by and_elim h₁₁₄

      -- Convert membership: w ∈ₛₑₜ B → w ∈ₛₑₜ A
      have h₁₁₇: w ∈ₛₑₜ A ↔ w ∈ₛₑₜ B := by forall_elim h₉, w
      have h₁₁₈: w ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₁₁₇ h₁₁₅

      -- Convert uniqueness: ∀ y, y ∈ₛₑₜ A → y =₍U₎ w
      have h₁₁₉: ∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ w := by forall_intro
        variable(v: U.Particular)
        assume(h₁₁₉₁: v ∈ₛₑₜ A)
        have h₁₁₉₂: v ∈ₛₑₜ A ↔ v ∈ₛₑₜ B := by forall_elim h₉, v
        have h₁₁₉₃: v ∈ₛₑₜ B := PC₀.deductive_eq_l2r h₁₁₉₂ h₁₁₉₁
        have h₁₁₉₄: v ∈ₛₑₜ B → v =₍U₎ w := by forall_elim h₁₁₆, v
        have h₁₁₉₅: v =₍U₎ w := by modus_ponens h₁₁₉₄, h₁₁₉₃
        iterate h₁₁₉₅

      -- Repack: ∃ x, ... → ∃!₍U₎ → is_singleton A
      have h₁₁₁₀: w ∈ₛₑₜ A ∧ (∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ w) := by and_intro h₁₁₈, h₁₁₉
      have h₁₁₁₁: ∃ (x: U.Particular), x ∈ₛₑₜ A ∧ (∀ (y: U.Particular), y ∈ₛₑₜ A → y =₍U₎ x) := by exists_intro h₁₁₁₀, w
      have h₁₁₁₂: ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := PC₀.deductive_eq_r2l h₆ h₁₁₁₁
      have h₁₁₁₃: is_singleton A := PC₀.deductive_eq_r2l h₃ h₁₁₁₂
      iterate h₁₁₁₃

    have h₁₂: is_singleton A ↔ is_singleton B := by iff_intro h₁₀, h₁₁
    iterate h₁₂
  { pred := pred, cong := cong }

end Sets

end Universe
