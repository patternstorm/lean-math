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

-- # Singleton Of Operation
-- Constructs the singleton set {x} for a given element x.
-- Returns a particular of the Singleton sub-universal (a set proven to be a singleton).
axiom singleton_of: U.Particular → SingletonSet U
macro "{" x:term "}ₛₑₜ" : term => `(singleton_of $x)

axiom singleton_of_def: ∀ (x: U.Particular), ∀ (y: U.Particular), y ∈ₛₑₜ ↑{x}ₛₑₜ ↔ y =₍U₎ x

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-15
noncomputable def singleton_of_operation: CongruentUnaryOperation U (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) :=
  let op: U.Particular → SingletonSet U := singleton_of
  let cong: ∀ (a: U.Particular), ∀ (b: U.Particular), a =₍U₎ b → (↑{a}ₛₑₜ =ₛₑₜ ↑{b}ₛₑₜ) := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)

    -- Instantiate singleton_of_def for a and b
    have h₁: ∀ (y: U.Particular), y ∈ₛₑₜ ↑{a}ₛₑₜ ↔ y =₍U₎ a := by forall_elim singleton_of_def, a
    have h₂: ∀ (y: U.Particular), y ∈ₛₑₜ ↑{b}ₛₑₜ ↔ y =₍U₎ b := by forall_elim singleton_of_def, b

    -- Set extensionality for the underlying sets
    have h₃: ∀ (S₂: Set U), ↑{a}ₛₑₜ =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ ↑{a}ₛₑₜ ↔ x ∈ₛₑₜ S₂) := by forall_elim set_extensionality, ↑{a}ₛₑₜ
    have h₄: ↑{a}ₛₑₜ =ₛₑₜ ↑{b}ₛₑₜ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ ↑{a}ₛₑₜ ↔ x ∈ₛₑₜ ↑{b}ₛₑₜ) := by forall_elim h₃, ↑{b}ₛₑₜ

    assume(h₅: a =₍U₎ b)

    -- Prove ∀ y, y ∈ₛₑₜ ↑{a}ₛₑₜ ↔ y ∈ₛₑₜ ↑{b}ₛₑₜ
    have h₆: ∀ (y: U.Particular), y ∈ₛₑₜ ↑{a}ₛₑₜ ↔ y ∈ₛₑₜ ↑{b}ₛₑₜ := by forall_intro
      variable(y: U.Particular)

      have h₆₁: y ∈ₛₑₜ ↑{a}ₛₑₜ ↔ y =₍U₎ a := by forall_elim h₁, y
      have h₆₂: y ∈ₛₑₜ ↑{b}ₛₑₜ ↔ y =₍U₎ b := by forall_elim h₂, y

      -- Forward: y ∈ₛₑₜ ↑{a}ₛₑₜ → y ∈ₛₑₜ ↑{b}ₛₑₜ
      have h₆₃: y ∈ₛₑₜ ↑{a}ₛₑₜ → y ∈ₛₑₜ ↑{b}ₛₑₜ := by
        assume(h₆₃₁: y ∈ₛₑₜ ↑{a}ₛₑₜ)
        have h₆₃₂: y =₍U₎ a := PC₀.deductive_eq_l2r h₆₁ h₆₃₁
        have h₆₃₃: y =₍U₎ a ∧ a =₍U₎ b := by and_intro h₆₃₂, h₅
        have h₆₃₄: y =₍U₎ b := U.eq.trans y a b h₆₃₃
        have h₆₃₅: y ∈ₛₑₜ ↑{b}ₛₑₜ := PC₀.deductive_eq_r2l h₆₂ h₆₃₄
        iterate h₆₃₅

      -- Backward: y ∈ₛₑₜ ↑{b}ₛₑₜ → y ∈ₛₑₜ ↑{a}ₛₑₜ
      have h₆₄: y ∈ₛₑₜ ↑{b}ₛₑₜ → y ∈ₛₑₜ ↑{a}ₛₑₜ := by
        assume(h₆₄₁: y ∈ₛₑₜ ↑{b}ₛₑₜ)
        have h₆₄₂: y =₍U₎ b := PC₀.deductive_eq_l2r h₆₂ h₆₄₁
        have h₆₄₃: b =₍U₎ a := U.eq.sym a b h₅
        have h₆₄₄: y =₍U₎ b ∧ b =₍U₎ a := by and_intro h₆₄₂, h₆₄₃
        have h₆₄₅: y =₍U₎ a := U.eq.trans y b a h₆₄₄
        have h₆₄₆: y ∈ₛₑₜ ↑{a}ₛₑₜ := PC₀.deductive_eq_r2l h₆₁ h₆₄₅
        iterate h₆₄₆

      have h₆₅: y ∈ₛₑₜ ↑{a}ₛₑₜ ↔ y ∈ₛₑₜ ↑{b}ₛₑₜ := by iff_intro h₆₃, h₆₄
      iterate h₆₅

    -- Apply set extensionality backward
    have h₇: ↑{a}ₛₑₜ =ₛₑₜ ↑{b}ₛₑₜ := PC₀.deductive_eq_r2l h₄ h₆
    iterate h₇
  { op := op, cong := cong }

end Sets

end Universe
