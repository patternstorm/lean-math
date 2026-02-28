import Universals.Dyads.Definitions

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

/-!
# Predicate Associativity of Dyads

For any predicate P on left-nested dyads ((U₁ ⋈ U₂) ⋈ U₃), we can construct
a predicate Q on right-nested dyads (U₁ ⋈ (U₂ ⋈ U₃)) that preserves
propositional content: Q(a ⋈ (b ⋈ c)) ↔ P((a ⋈ b) ⋈ c).

The construction uses two nested applications of uncurry:
1. Inner: for each a, uncurry (b, c) ↦ P((a ⋈ b) ⋈ c) into a unary pred on (U₂ ⋈ U₃)
2. Outer: uncurry the result into a unary pred on (U₁ ⋈ (U₂ ⋈ U₃))

The proof chains two applications of uncurry_def.
-/

-- The reassociated predicate: left-nested → right-nested
noncomputable def reassoc
  {U₁: Universal} {U₂: Universal} {U₃: Universal}
  (P: ((U₁ ⋈ U₂) ⋈ U₃).Particular → Prop): (U₁ ⋈ (U₂ ⋈ U₃)).Particular → Prop :=
  uncurry (x: U₁.Particular ↦
    uncurry (y: U₂.Particular ↦ (z: U₃.Particular ↦
      P ((x ⋈ y) ⋈ z))))

-- Predicate associativity: reassociation preserves propositional content.
-- This is a single theorem (axiom scheme): each concrete P generates one instance.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-28
theorem predicate_associativity
  {U₁: Universal} {U₂: Universal} {U₃: Universal}
  (P: ((U₁ ⋈ U₂) ⋈ U₃).Particular → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), ∀ (c: U₃.Particular),
    reassoc P (a ⋈ (b ⋈ c)) ↔ P ((a ⋈ b) ⋈ c) := by forall_intro
  variable(a: U₁.Particular)
  variable(b: U₂.Particular)
  variable(c: U₃.Particular)
  -- Outer uncurry_def: reassoc P (a ⋈ (b ⋈ c)) ↔ (inner uncurry)(b ⋈ c)
  let outer_R: U₁.Particular → (U₂ ⋈ U₃).Particular → Prop :=
    (x: U₁.Particular ↦ uncurry (y: U₂.Particular ↦ (z: U₃.Particular ↦ P ((x ⋈ y) ⋈ z))))
  have h₁: ∀ (x: U₁.Particular), ∀ (d: (U₂ ⋈ U₃).Particular),
    uncurry outer_R (x ⋈ d) ↔ outer_R x d := uncurry_def outer_R
  have h₂: ∀ (d: (U₂ ⋈ U₃).Particular),
    uncurry outer_R (a ⋈ d) ↔ outer_R a d := by forall_elim h₁, a
  have h₃: uncurry outer_R (a ⋈ (b ⋈ c)) ↔ outer_R a (b ⋈ c) := by forall_elim h₂, (b ⋈ c)
  -- Inner uncurry_def: (inner uncurry)(b ⋈ c) ↔ P((a ⋈ b) ⋈ c)
  let inner_R: U₂.Particular → U₃.Particular → Prop :=
    (y: U₂.Particular ↦ (z: U₃.Particular ↦ P ((a ⋈ y) ⋈ z)))
  have h₄: ∀ (y: U₂.Particular), ∀ (z: U₃.Particular),
    uncurry inner_R (y ⋈ z) ↔ inner_R y z := uncurry_def inner_R
  have h₅: ∀ (z: U₃.Particular),
    uncurry inner_R (b ⋈ z) ↔ inner_R b z := by forall_elim h₄, b
  have h₆: uncurry inner_R (b ⋈ c) ↔ inner_R b c := by forall_elim h₅, c
  -- Chain: reassoc P (a ⋈ (b ⋈ c)) ↔ outer_R a (b ⋈ c) ↔ P((a ⋈ b) ⋈ c)
  have h₇: reassoc P (a ⋈ (b ⋈ c)) → P ((a ⋈ b) ⋈ c) := by
    assume(h₇₁: reassoc P (a ⋈ (b ⋈ c)))
    have h₇₂: outer_R a (b ⋈ c) := PC₀.deductive_eq_l2r h₃ h₇₁
    have h₇₃: inner_R b c := PC₀.deductive_eq_l2r h₆ h₇₂
    iterate h₇₃
  have h₈: P ((a ⋈ b) ⋈ c) → reassoc P (a ⋈ (b ⋈ c)) := by
    assume(h₈₁: P ((a ⋈ b) ⋈ c))
    have h₈₂: uncurry inner_R (b ⋈ c) := PC₀.deductive_eq_r2l h₆ h₈₁
    have h₈₃: reassoc P (a ⋈ (b ⋈ c)) := PC₀.deductive_eq_r2l h₃ h₈₂
    iterate h₈₃
  have h₉: reassoc P (a ⋈ (b ⋈ c)) ↔ P ((a ⋈ b) ⋈ c) := by iff_intro h₇, h₈
  iterate h₉

end Dyads
end Universe
