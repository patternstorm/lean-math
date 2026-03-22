import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Sets
import Universals.Arrows

/-!
# Correspondence Apply

Applies a correspondence to a source classification (set), producing the
corresponding target classification — the set of all target particulars
co-classified by any source particular in the input classification. This is the primary
operation of a correspondence as a classification mapping.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Arrows

axiom apply: U₁ ⭢ᶜ U₂ → Set U₁ → Set U₂
-- Allows using C S syntax for correspondence application by juxtaposition
noncomputable instance : CoeFun (U₁ ⭢ᶜ U₂) (fun _ => Set U₁ → Set U₂) where
  coe := apply

axiom apply_def: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (S: Set U₁), ∀ (b: U₂.Particular),
  b ∈ₛₑₜ (C S) ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
theorem apply_cong_first: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂),
  C₁ =→ᶜ C₂ → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by forall_intro
  variable(C₁: U₁ ⭢ᶜ U₂)
  variable(C₂: U₁ ⭢ᶜ U₂)
  assume(h₁: C₁ =→ᶜ C₂)
  variable(S: Set U₁)

  -- From C₁ =ₛₑₜ C₂, derive membership equivalence for any arrow
  have h₂: ∀ (T₂: Set (U₁ ➞ᵃ (𝐒𝐞𝐭 U₂))), C₁ =ₛₑₜ T₂ ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), f ∈ₛₑₜ C₁ ↔ f ∈ₛₑₜ T₂) := by forall_elim set_extensionality, C₁
  have h₃: C₁ =ₛₑₜ C₂ ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), f ∈ₛₑₜ C₁ ↔ f ∈ₛₑₜ C₂) := by forall_elim h₂, C₂
  have h₄: ∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), f ∈ₛₑₜ C₁ ↔ f ∈ₛₑₜ C₂ := PC₀.deductive_eq_l2r h₃ h₁

  -- Set extensionality for the result
  have h₅: ∀ (R₂: Set U₂), C₁ S =ₛₑₜ R₂ ↔ (∀ (b: U₂.Particular), b ∈ₛₑₜ C₁ S ↔ b ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ S
  have h₆: C₁ S =ₛₑₜ C₂ S ↔ (∀ (b: U₂.Particular), b ∈ₛₑₜ C₁ S ↔ b ∈ₛₑₜ C₂ S) := by forall_elim h₅, C₂ S

  -- apply_def for C₁ and C₂
  have h₇: ∀ (S': Set U₁), ∀ (b: U₂.Particular), b ∈ₛₑₜ (C₁ S') ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S' ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by forall_elim apply_def, C₁
  have h₈: ∀ (b: U₂.Particular), b ∈ₛₑₜ (C₁ S) ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by forall_elim h₇, S
  have h₉: ∀ (S': Set U₁), ∀ (b: U₂.Particular), b ∈ₛₑₜ (C₂ S') ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S' ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by forall_elim apply_def, C₂
  have h₁₀: ∀ (b: U₂.Particular), b ∈ₛₑₜ (C₂ S) ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by forall_elim h₉, S

  have h₁₁: ∀ (b: U₂.Particular), b ∈ₛₑₜ C₁ S ↔ b ∈ₛₑₜ C₂ S := by forall_intro
    variable(b: U₂.Particular)
    have h₁₁₁: b ∈ₛₑₜ C₁ S ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by forall_elim h₈, b
    have h₁₁₂: b ∈ₛₑₜ C₂ S ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by forall_elim h₁₀, b

    -- Forward: b ∈ C₁ S → b ∈ C₂ S
    have h₁₁₃: b ∈ₛₑₜ C₁ S → b ∈ₛₑₜ C₂ S := by
      assume(h₁₁₃₁: b ∈ₛₑₜ C₁ S)
      have h₁₁₃₂: ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := PC₀.deductive_eq_l2r h₁₁₁ h₁₁₃₁
      have ⟨(a: U₁.Particular), (h₁₁₃₃: a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T)⟩ := exists_elim h₁₁₃₂
      have h₁₁₃₄: a ∈ₛₑₜ S := by and_elim h₁₁₃₃
      have h₁₁₃₅: ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by and_elim h₁₁₃₃
      have ⟨(T: Set U₂), (h₁₁₃₆: (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T)⟩ := exists_elim h₁₁₃₅
      have h₁₁₃₇: (a ⭢ᵃ T) ∈ₛₑₜ C₁ := by and_elim h₁₁₃₆
      have h₁₁₃₈: b ∈ₛₑₜ T := by and_elim h₁₁₃₆
      -- Transfer arrow membership from C₁ to C₂
      have h₁₁₃₉: (a ⭢ᵃ T) ∈ₛₑₜ C₁ ↔ (a ⭢ᵃ T) ∈ₛₑₜ C₂ := by forall_elim h₄, (a ⭢ᵃ T)
      have h₁₁₃₁₀: (a ⭢ᵃ T) ∈ₛₑₜ C₂ := PC₀.deductive_eq_l2r h₁₁₃₉ h₁₁₃₇
      have h₁₁₃₁₁: (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by and_intro h₁₁₃₁₀, h₁₁₃₈
      have h₁₁₃₁₂: ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by exists_intro h₁₁₃₁₁, T
      have h₁₁₃₁₃: a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by and_intro h₁₁₃₄, h₁₁₃₁₂
      have h₁₁₃₁₄: ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by exists_intro h₁₁₃₁₃, a
      have h₁₁₃₁₅: b ∈ₛₑₜ C₂ S := PC₀.deductive_eq_r2l h₁₁₂ h₁₁₃₁₄
      iterate h₁₁₃₁₅

    -- Backward: b ∈ C₂ S → b ∈ C₁ S
    have h₁₁₄: b ∈ₛₑₜ C₂ S → b ∈ₛₑₜ C₁ S := by
      assume(h₁₁₄₁: b ∈ₛₑₜ C₂ S)
      have h₁₁₄₂: ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := PC₀.deductive_eq_l2r h₁₁₂ h₁₁₄₁
      have ⟨(a: U₁.Particular), (h₁₁₄₃: a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T)⟩ := exists_elim h₁₁₄₂
      have h₁₁₄₄: a ∈ₛₑₜ S := by and_elim h₁₁₄₃
      have h₁₁₄₅: ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T := by and_elim h₁₁₄₃
      have ⟨(T: Set U₂), (h₁₁₄₆: (a ⭢ᵃ T) ∈ₛₑₜ C₂ ∧ b ∈ₛₑₜ T)⟩ := exists_elim h₁₁₄₅
      have h₁₁₄₇: (a ⭢ᵃ T) ∈ₛₑₜ C₂ := by and_elim h₁₁₄₆
      have h₁₁₄₈: b ∈ₛₑₜ T := by and_elim h₁₁₄₆
      -- Transfer arrow membership from C₂ to C₁
      have h₁₁₄₉: (a ⭢ᵃ T) ∈ₛₑₜ C₁ ↔ (a ⭢ᵃ T) ∈ₛₑₜ C₂ := by forall_elim h₄, (a ⭢ᵃ T)
      have h₁₁₄₁₀: (a ⭢ᵃ T) ∈ₛₑₜ C₁ := PC₀.deductive_eq_r2l h₁₁₄₉ h₁₁₄₇
      have h₁₁₄₁₁: (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by and_intro h₁₁₄₁₀, h₁₁₄₈
      have h₁₁₄₁₂: ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by exists_intro h₁₁₄₁₁, T
      have h₁₁₄₁₃: a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by and_intro h₁₁₄₄, h₁₁₄₁₂
      have h₁₁₄₁₄: ∃ (a: U₁.Particular), a ∈ₛₑₜ S ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C₁ ∧ b ∈ₛₑₜ T := by exists_intro h₁₁₄₁₃, a
      have h₁₁₄₁₅: b ∈ₛₑₜ C₁ S := PC₀.deductive_eq_r2l h₁₁₁ h₁₁₄₁₄
      iterate h₁₁₄₁₅

    have h₁₁₅: b ∈ₛₑₜ C₁ S ↔ b ∈ₛₑₜ C₂ S := by iff_intro h₁₁₃, h₁₁₄
    iterate h₁₁₅

  have h₁₂: C₁ S =ₛₑₜ C₂ S := PC₀.deductive_eq_r2l h₆ h₁₁
  iterate h₁₂

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-21
theorem apply_cong_second: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (S₁: Set U₁), ∀ (S₂: Set U₁),
  S₁ =ₛₑₜ S₂ → C S₁ =ₛₑₜ C S₂ := by forall_intro
  variable(C: U₁ ⭢ᶜ U₂)
  variable(S₁: Set U₁)
  variable(S₂: Set U₁)
  assume(h₁: S₁ =ₛₑₜ S₂)

  -- Set extensionality on S₁ =ₛₑₜ S₂
  have h₂: ∀ (T₂: Set U₁), S₁ =ₛₑₜ T₂ ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ T₂) := by forall_elim set_extensionality, S₁
  have h₃: S₁ =ₛₑₜ S₂ ↔ (∀ (x: U₁.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ S₂) := by forall_elim h₂, S₂
  have h₄: ∀ (x: U₁.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ S₂ := PC₀.deductive_eq_l2r h₃ h₁

  -- Set extensionality for the result
  have h₅: ∀ (R₂: Set U₂), C S₁ =ₛₑₜ R₂ ↔ (∀ (b: U₂.Particular), b ∈ₛₑₜ C S₁ ↔ b ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C S₁
  have h₆: C S₁ =ₛₑₜ C S₂ ↔ (∀ (b: U₂.Particular), b ∈ₛₑₜ C S₁ ↔ b ∈ₛₑₜ C S₂) := by forall_elim h₅, C S₂

  -- apply_def for both sides
  have h₇: ∀ (S': Set U₁), ∀ (b: U₂.Particular), b ∈ₛₑₜ (C S') ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S' ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by forall_elim apply_def, C
  have h₈: ∀ (b: U₂.Particular), b ∈ₛₑₜ (C S₁) ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S₁ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by forall_elim h₇, S₁
  have h₉: ∀ (b: U₂.Particular), b ∈ₛₑₜ (C S₂) ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S₂ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by forall_elim h₇, S₂

  have h₁₀: ∀ (b: U₂.Particular), b ∈ₛₑₜ C S₁ ↔ b ∈ₛₑₜ C S₂ := by forall_intro
    variable(b: U₂.Particular)
    have h₁₀₁: b ∈ₛₑₜ C S₁ ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S₁ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by forall_elim h₈, b
    have h₁₀₂: b ∈ₛₑₜ C S₂ ↔ ∃ (a: U₁.Particular), a ∈ₛₑₜ S₂ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by forall_elim h₉, b

    -- Forward: b ∈ C S₁ → b ∈ C S₂
    have h₁₀₃: b ∈ₛₑₜ C S₁ → b ∈ₛₑₜ C S₂ := by
      assume(h₁₀₃₁: b ∈ₛₑₜ C S₁)
      have h₁₀₃₂: ∃ (a: U₁.Particular), a ∈ₛₑₜ S₁ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := PC₀.deductive_eq_l2r h₁₀₁ h₁₀₃₁
      have ⟨(a: U₁.Particular), (h₁₀₃₃: a ∈ₛₑₜ S₁ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T)⟩ := exists_elim h₁₀₃₂
      have h₁₀₃₄: a ∈ₛₑₜ S₁ := by and_elim h₁₀₃₃
      have h₁₀₃₅: ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by and_elim h₁₀₃₃
      have h₁₀₃₆: a ∈ₛₑₜ S₁ ↔ a ∈ₛₑₜ S₂ := by forall_elim h₄, a
      have h₁₀₃₇: a ∈ₛₑₜ S₂ := PC₀.deductive_eq_l2r h₁₀₃₆ h₁₀₃₄
      have h₁₀₃₈: a ∈ₛₑₜ S₂ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by and_intro h₁₀₃₇, h₁₀₃₅
      have h₁₀₃₉: ∃ (a: U₁.Particular), a ∈ₛₑₜ S₂ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by exists_intro h₁₀₃₈, a
      have h₁₀₃₁₀: b ∈ₛₑₜ C S₂ := PC₀.deductive_eq_r2l h₁₀₂ h₁₀₃₉
      iterate h₁₀₃₁₀

    -- Backward: b ∈ C S₂ → b ∈ C S₁
    have h₁₀₄: b ∈ₛₑₜ C S₂ → b ∈ₛₑₜ C S₁ := by
      assume(h₁₀₄₁: b ∈ₛₑₜ C S₂)
      have h₁₀₄₂: ∃ (a: U₁.Particular), a ∈ₛₑₜ S₂ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := PC₀.deductive_eq_l2r h₁₀₂ h₁₀₄₁
      have ⟨(a: U₁.Particular), (h₁₀₄₃: a ∈ₛₑₜ S₂ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T)⟩ := exists_elim h₁₀₄₂
      have h₁₀₄₄: a ∈ₛₑₜ S₂ := by and_elim h₁₀₄₃
      have h₁₀₄₅: ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by and_elim h₁₀₄₃
      have h₁₀₄₆: a ∈ₛₑₜ S₁ ↔ a ∈ₛₑₜ S₂ := by forall_elim h₄, a
      have h₁₀₄₇: a ∈ₛₑₜ S₁ := PC₀.deductive_eq_r2l h₁₀₄₆ h₁₀₄₄
      have h₁₀₄₈: a ∈ₛₑₜ S₁ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by and_intro h₁₀₄₇, h₁₀₄₅
      have h₁₀₄₉: ∃ (a: U₁.Particular), a ∈ₛₑₜ S₁ ∧ ∃ (T: Set U₂), (a ⭢ᵃ T) ∈ₛₑₜ C ∧ b ∈ₛₑₜ T := by exists_intro h₁₀₄₈, a
      have h₁₀₄₁₀: b ∈ₛₑₜ C S₁ := PC₀.deductive_eq_r2l h₁₀₁ h₁₀₄₉
      iterate h₁₀₄₁₀

    have h₁₀₅: b ∈ₛₑₜ C S₁ ↔ b ∈ₛₑₜ C S₂ := by iff_intro h₁₀₃, h₁₀₄
    iterate h₁₀₅

  have h₁₁: C S₁ =ₛₑₜ C S₂ := PC₀.deductive_eq_r2l h₆ h₁₀
  iterate h₁₁

-- For fixed C, apply maps source sets to target sets, congruent in the source set.
noncomputable def apply_with (C: U₁ ⭢ᶜ U₂): CongruentUnaryOperation (𝐒𝐞𝐭 U₁) (𝐒𝐞𝐭 U₂) :=
  let op: Set U₁ → Set U₂ := (S: Set U₁ ↦ C S)
  let cong: ∀ (S₁: Set U₁), ∀ (S₂: Set U₁), S₁ =ₛₑₜ S₂ → (C S₁ =ₛₑₜ C S₂) := by forall_intro
    variable(S₁: Set U₁)
    variable(S₂: Set U₁)
    have h₁: ∀ (S₁': Set U₁), ∀ (S₂': Set U₁),
      S₁' =ₛₑₜ S₂' → C S₁' =ₛₑₜ C S₂' := by forall_elim apply_cong_second, C
    have h₂: ∀ (S₂': Set U₁), S₁ =ₛₑₜ S₂' → C S₁ =ₛₑₜ C S₂' := by forall_elim h₁, S₁
    have h₃: S₁ =ₛₑₜ S₂ → C S₁ =ₛₑₜ C S₂ := by forall_elim h₂, S₂
    assume(h₄: S₁ =ₛₑₜ S₂)
    have h₅: C S₁ =ₛₑₜ C S₂ := by modus_ponens h₃, h₄
    iterate h₅
  { op := op, cong := cong }

-- Full binary operation, congruent in both arguments.
noncomputable def apply_operation: CongruentBinaryOperation (U₁ ➞ᶜ U₂) (𝐒𝐞𝐭 U₁) (𝐒𝐞𝐭 U₂) :=
  let op: U₁ ⭢ᶜ U₂ → CongruentUnaryOperation (𝐒𝐞𝐭 U₁) (𝐒𝐞𝐭 U₂) := (C: U₁ ⭢ᶜ U₂ ↦ apply_with C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), ∀ (S: Set U₁),
    C₁ =→ᶜ C₂ → ((apply_with C₁).op S =ₛₑₜ (apply_with C₂).op S) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    variable(S: Set U₁)
    have h₁: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (S': Set U₁), C₁ S' =ₛₑₜ C₂' S' := by forall_elim apply_cong_first, C₁
    have h₂: C₁ =→ᶜ C₂ → ∀ (S': Set U₁), C₁ S' =ₛₑₜ C₂ S' := by forall_elim h₁, C₂
    assume(h₃: C₁ =→ᶜ C₂)
    have h₄: ∀ (S': Set U₁), C₁ S' =ₛₑₜ C₂ S' := by modus_ponens h₂, h₃
    have h₅: C₁ S =ₛₑₜ C₂ S := by forall_elim h₄, S
    iterate h₅
  { op := op, cong := cong }

end Correspondences

end Universe
