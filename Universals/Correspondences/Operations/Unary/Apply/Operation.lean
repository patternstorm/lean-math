import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Sets
import Universals.Arrows

/-!
# Correspondence Apply

Applies a correspondence to a source particular, producing the set on the
right-hand side associated with that source.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets
open Arrows

axiom apply: U₁ ⭢ᶜ U₂ → U₁.Particular → Set U₂
-- Allows using C a syntax for correspondence application
noncomputable instance : CoeFun (U₁ ⭢ᶜ U₂) (fun _ => U₁.Particular → Set U₂) where
  coe := apply

axiom apply_def: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (a: U₁.Particular), ∀ (S: Set U₂),
  S =ₛₑₜ (apply C a) ↔ (a ⭢ᵃ S) ∈ₛₑₜ C

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem apply_cong_first: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂),
  C₁ =→ᶜ C₂ → ∀ (a: U₁.Particular), C₁ a =ₛₑₜ C₂ a := by forall_intro
  variable(C₁: U₁ ⭢ᶜ U₂)
  variable(C₂: U₁ ⭢ᶜ U₂)
  assume(h₁: C₁ =→ᶜ C₂)
  variable(a: U₁.Particular)

  -- From apply_def for C₁, instantiated at (a, C₁ a):
  -- C₁ a =ₛₑₜ C₁ a ↔ (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₁
  have h₂: ∀ (a: U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ C₁ a ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₁ := by forall_elim apply_def, C₁
  have h₃: ∀ (S: Set U₂), S =ₛₑₜ C₁ a ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₁ := by forall_elim h₂, a
  have h₄: C₁ a =ₛₑₜ C₁ a ↔ (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₁ := by forall_elim h₃, C₁ a

  -- Set reflexivity gives C₁ a =ₛₑₜ C₁ a
  have h₅: C₁ a =ₛₑₜ C₁ a := by forall_elim eq_refl, C₁ a

  -- Therefore the arrow (a ⭢ᵃ C₁ a) is in C₁
  have h₆: (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₁ := PC₀.deductive_eq_l2r h₄ h₅

  -- From C₁ =→ᶜ C₂ (which is C₁ =ₛₑₜ C₂), derive membership equivalence
  have h₇: ∀ (S₂: U₁ ⭢ᶜ U₂), C₁ =ₛₑₜ S₂ ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), f ∈ₛₑₜ C₁ ↔ f ∈ₛₑₜ S₂) := by forall_elim set_extensionality, C₁
  have h₈: C₁ =ₛₑₜ C₂ ↔ (∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), f ∈ₛₑₜ C₁ ↔ f ∈ₛₑₜ C₂) := by forall_elim h₇, C₂
  have h₉: ∀ (f: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), f ∈ₛₑₜ C₁ ↔ f ∈ₛₑₜ C₂ := PC₀.deductive_eq_l2r h₈ h₁
  have h₁₀: (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₁ ↔ (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₂ := by forall_elim h₉, (a ⭢ᵃ C₁ a)

  -- Therefore the arrow is also in C₂
  have h₁₁: (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₂ := PC₀.deductive_eq_l2r h₁₀ h₆

  -- From apply_def for C₂, instantiated at (a, C₁ a):
  -- C₁ a =ₛₑₜ C₂ a ↔ (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₂
  have h₁₂: ∀ (a: U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ C₂ a ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₂ := by forall_elim apply_def, C₂
  have h₁₃: ∀ (S: Set U₂), S =ₛₑₜ C₂ a ↔ (a ⭢ᵃ S) ∈ₛₑₜ C₂ := by forall_elim h₁₂, a
  have h₁₄: C₁ a =ₛₑₜ C₂ a ↔ (a ⭢ᵃ C₁ a) ∈ₛₑₜ C₂ := by forall_elim h₁₃, C₁ a

  -- Therefore C₁ a =ₛₑₜ C₂ a
  have h₁₅: C₁ a =ₛₑₜ C₂ a := PC₀.deductive_eq_r2l h₁₄ h₁₁
  iterate h₁₅

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-14
theorem apply_cong_second: ∀ (C: U₁ ⭢ᶜ U₂), ∀ (a₁: U₁.Particular), ∀ (a₂: U₁.Particular),
  a₁ =₍U₁₎ a₂ → C a₁ =ₛₑₜ C a₂ := by forall_intro
  variable(C: U₁ ⭢ᶜ U₂)
  variable(a₁: U₁.Particular)
  variable(a₂: U₁.Particular)
  assume(h₁: a₁ =₍U₁₎ a₂)

  -- Self-application: instantiate apply_def at (C, a₁, C a₁) + set reflexivity
  -- to derive that the arrow (a₁ ⭢ᵃ C a₁) is in C
  have h₂: ∀ (a: U₁.Particular), ∀ (S: Set U₂), S =ₛₑₜ  C a ↔ (a ⭢ᵃ S) ∈ₛₑₜ C := by forall_elim apply_def, C
  have h₃: ∀ (S: Set U₂), S =ₛₑₜ C a₁ ↔ (a₁ ⭢ᵃ S) ∈ₛₑₜ C := by forall_elim h₂, a₁
  have h₄: C a₁ =ₛₑₜ C a₁ ↔ (a₁ ⭢ᵃ C a₁) ∈ₛₑₜ C := by forall_elim h₃, C a₁
  have h₅: C a₁ =ₛₑₜ C a₁ := by forall_elim eq_refl, C a₁
  have h₆: (a₁ ⭢ᵃ C a₁) ∈ₛₑₜ C := PC₀.deductive_eq_l2r h₄ h₅

  -- Arrow equality: from a₁ =₍U₁₎ a₂ and set reflexivity on C a₁,
  -- build (a₁ ⭢ᵃ C a₁) =→ᵃ (a₂ ⭢ᵃ C a₁) via Arrows.eq_def
  -- (Arrows.eq_def needs explicit universals since a₁ alone cannot determine 𝐒𝐞𝐭 U₂;
  -- standalone arrow expressions in =→ᵃ need whole-expression type ascription
  -- (: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)) — see Universal.lean Note on Projection Inversion)
  have h₇: ∀ (b₁: Set U₂), ∀ (a₂: U₁.Particular), ∀ (b₂: Set U₂), (a₁ ⭢ᵃ b₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =ₛₑₜ b₂ := by forall_elim (@Arrows.eq_def U₁ (𝐒𝐞𝐭 U₂)), a₁
  have h₈: ∀ (a₂: U₁.Particular), ∀ (b₂: Set U₂), (a₁ ⭢ᵃ C a₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ C a₁ =ₛₑₜ b₂ := by forall_elim h₇, C a₁
  have h₉: ∀ (b₂: Set U₂), (a₁ ⭢ᵃ C a₁) =→ᵃ (a₂ ⭢ᵃ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ C a₁ =ₛₑₜ b₂ := by forall_elim h₈, a₂
  have h₁₀: (a₁ ⭢ᵃ C a₁) =→ᵃ (a₂ ⭢ᵃ C a₁ : U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)) ↔ a₁ =₍U₁₎ a₂ ∧ C a₁ =ₛₑₜ C a₁ := by forall_elim h₉, C a₁
  have h₁₁: a₁ =₍U₁₎ a₂ ∧ C a₁ =ₛₑₜ C a₁ := by and_intro h₁, h₅
  have h₁₂: (a₁ ⭢ᵃ C a₁) =→ᵃ (a₂ ⭢ᵃ C a₁ : U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)) := PC₀.deductive_eq_r2l h₁₀ h₁₁

  -- Membership transfer: use mem_def to convert ∈ₛₑₜ to C.pred, apply C.cong
  -- with the arrow equality, then convert back to ∈ₛₑₜ
  have h₁₃: ∀ (x: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)), x ∈ₛₑₜ C ↔ C.pred x := by forall_elim mem_def, C
  have h₁₄: (a₁ ⭢ᵃ C a₁) ∈ₛₑₜ C ↔ C.pred (a₁ ⭢ᵃ C a₁) := by forall_elim h₁₃, (a₁ ⭢ᵃ C a₁)
  have h₁₅: C.pred (a₁ ⭢ᵃ C a₁) := PC₀.deductive_eq_l2r h₁₄ h₆
  have h₁₆: ∀ (f₂: U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)),
    (a₁ ⭢ᵃ C a₁) =→ᵃ f₂ → (C.pred (a₁ ⭢ᵃ C a₁) ↔ C.pred f₂) := by forall_elim C.cong, (a₁ ⭢ᵃ C a₁)
  have h₁₇: (a₁ ⭢ᵃ C a₁) =→ᵃ (a₂ ⭢ᵃ C a₁ : U₁ ⭢ᵃ (𝐒𝐞𝐭 U₂)) →
    (C.pred (a₁ ⭢ᵃ C a₁) ↔ C.pred (a₂ ⭢ᵃ C a₁)) := by forall_elim h₁₆, (a₂ ⭢ᵃ C a₁)
  have h₁₈: C.pred (a₁ ⭢ᵃ C a₁) ↔ C.pred (a₂ ⭢ᵃ C a₁) := by modus_ponens h₁₇, h₁₂
  have h₁₉: C.pred (a₂ ⭢ᵃ C a₁) := PC₀.deductive_eq_l2r h₁₈ h₁₅
  have h₂₀: (a₂ ⭢ᵃ C a₁) ∈ₛₑₜ C ↔ C.pred (a₂ ⭢ᵃ C a₁) := by forall_elim h₁₃, (a₂ ⭢ᵃ C a₁)
  have h₂₁: (a₂ ⭢ᵃ C a₁) ∈ₛₑₜ C := PC₀.deductive_eq_r2l h₂₀ h₁₉

  -- Read off: apply_def at (C, a₂, C a₁) gives the result
  have h₂₂: ∀ (S: Set U₂), S =ₛₑₜ (apply C a₂) ↔ (a₂ ⭢ᵃ S) ∈ₛₑₜ C := by forall_elim h₂, a₂
  have h₂₃: C a₁ =ₛₑₜ apply C a₂ ↔ (a₂ ⭢ᵃ C a₁) ∈ₛₑₜ C := by forall_elim h₂₂, C a₁
  have h₂₄: C a₁ =ₛₑₜ apply C a₂ := PC₀.deductive_eq_r2l h₂₃ h₂₁
  iterate h₂₄

-- For fixed C, apply_with maps source elements to sets, congruent in the source.
noncomputable def apply_with (C: U₁ ⭢ᶜ U₂): CongruentUnaryOperation U₁ (𝐒𝐞𝐭 U₂) :=
  let op: U₁.Particular → Set U₂ := (a: U₁.Particular ↦ apply C a)
  let cong: ∀ (a₁: U₁.Particular), ∀ (a₂: U₁.Particular), a₁ =₍U₁₎ a₂ → (C a₁ =ₛₑₜ apply C a₂) := by forall_intro
    variable(a₁: U₁.Particular)
    variable(a₂: U₁.Particular)
    have h₁: ∀ (a₁': U₁.Particular), ∀ (a₂': U₁.Particular),
      a₁' =₍U₁₎ a₂' → C a₁' =ₛₑₜ apply C a₂' := by forall_elim apply_cong_second, C
    have h₂: ∀ (a₂': U₁.Particular), a₁ =₍U₁₎ a₂' → C a₁ =ₛₑₜ apply C a₂' := by forall_elim h₁, a₁
    have h₃: a₁ =₍U₁₎ a₂ → C a₁ =ₛₑₜ apply C a₂ := by forall_elim h₂, a₂
    assume(h₄: a₁ =₍U₁₎ a₂)
    have h₅: C a₁ =ₛₑₜ apply C a₂ := by modus_ponens h₃, h₄
    iterate h₅
  { op := op, cong := cong }

-- Full binary operation, congruent in both arguments.
noncomputable def apply_operation: CongruentBinaryOperation (U₁ ➞ᶜ U₂) U₁ (𝐒𝐞𝐭 U₂) :=
  let op: U₁ ⭢ᶜ U₂ → CongruentUnaryOperation U₁ (𝐒𝐞𝐭 U₂) := (C: U₁ ⭢ᶜ U₂ ↦ apply_with C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), ∀ (a: U₁.Particular),
    C₁ =→ᶜ C₂ → ((apply_with C₁).op a =ₛₑₜ (apply_with C₂).op a) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    variable(a: U₁.Particular)
    have h₁: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (a': U₁.Particular), C₁ a' =ₛₑₜ C₂' a' := by forall_elim apply_cong_first, C₁
    have h₂: C₁ =→ᶜ C₂ → ∀ (a': U₁.Particular), C₁ a' =ₛₑₜ C₂ a' := by forall_elim h₁, C₂
    assume(h₃: C₁ =→ᶜ C₂)
    have h₄: ∀ (a': U₁.Particular), C₁ a' =ₛₑₜ C₂ a' := by modus_ponens h₂, h₃
    have h₅: C₁ a =ₛₑₜ C₂ a := by forall_elim h₄, a
    iterate h₅
  { op := op, cong := cong }

end Correspondences

end Universe
