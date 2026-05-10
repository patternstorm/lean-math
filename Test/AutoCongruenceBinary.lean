import Logic.PredicateCalculus.Schemas.Universal.Schema
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

/-!
# Binary Auto-Congruence Prototype

Tests the redesigned CongruentUnary class where `cong` is stored directly
(not bundled in a CongruentUnaryPredicate). This ensures `.pred = P`
definitionally in the CoeDep coercion, enabling a bridge instance that
derives CongruentBinary from unary instances.
-/

namespace Test.AutoCongruenceBinary

open Logic
open Logic.PC₁
open Logic.ND

-- ============================================================
-- # 1. Structures (same as framework)
-- ============================================================

structure CongruentUnaryPredicate' (U: Universal): Type where
  pred: U.Particular → Prop
  cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (pred x ↔ pred y)

structure CongruentBinaryPredicate' (U₁: Universal) (U₂: Universal): Type where
  pred: U₁.Particular → CongruentUnaryPredicate' U₂
  cong: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), x =₍U₁₎ y → ((pred x).pred z ↔ (pred y).pred z)

-- ============================================================
-- # 2. Redesigned class — stores cong directly
-- ============================================================

class CongruentUnary' (U: Universal) (P: U.Particular → Prop) where
  cong: ∀ (x: U.Particular), ∀ (y: U.Particular), x =₍U₎ y → (P x ↔ P y)

class CongruentBinary' (U₁: Universal) (U₂: Universal) (P: U₁.Particular → U₂.Particular → Prop) where
  inner_cong: ∀ (x: U₁.Particular), ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂)
  outer_cong: ∀ (x₁: U₁.Particular), ∀ (x₂: U₁.Particular), ∀ (z: U₂.Particular), x₁ =₍U₁₎ x₂ → (P x₁ z ↔ P x₂ z)

-- ============================================================
-- # 3. CoeDep coercions — pred = P definitionally
-- ============================================================

instance congruent_coercion' {U: Universal} {P: U.Particular → Prop}
    [c: CongruentUnary' U P]: CoeDep (U.Particular → Prop) P (CongruentUnaryPredicate' U) where
  coe := { pred := P, cong := c.cong }

instance congruent_binary_coercion' {U₁ U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    [c: CongruentBinary' U₁ U₂ P]: CoeDep (U₁.Particular → U₂.Particular → Prop) P (CongruentBinaryPredicate' U₁ U₂) where
  coe :=
    let pred: U₁.Particular → CongruentUnaryPredicate' U₂ :=
      (x: U₁.Particular ↦
        let fiber_cong: ∀ (y₁: U₂.Particular), ∀ (y₂: U₂.Particular), y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂) := by
          have h₁ := by forall_elim c.inner_cong, x
          iterate h₁
        { pred := P x, cong := fiber_cong })
    { pred := pred, cong := c.outer_cong }

-- ============================================================
-- # 4. Unary instances
-- ============================================================

-- Constant: body doesn't mention x
instance (priority := 100) congruent_constant' {U: Universal} {A: Prop}:
    CongruentUnary' U (_: U.Particular ↦ A) where
  cong := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(_h: a =₍U₎ b)
    have h₁: A → A := by
      assume(h₁₁: A)
      iterate h₁₁
    have h₂: A ↔ A := by iff_intro h₁, h₁
    iterate h₂

-- Equal-from: x =₍U₎ a
instance congruent_equal_from' {U: Universal} {a: U.Particular}:
    CongruentUnary' U (x: U.Particular ↦ x =₍U₎ a) where
  cong := by forall_intro
    variable(u: U.Particular)
    variable(v: U.Particular)
    assume(h₁: u =₍U₎ v)
    have fwd: u =₍U₎ a → v =₍U₎ a := by
      assume(h₂: u =₍U₎ a)
      have h₃: v =₍U₎ u := U.eq.sym u v h₁
      have h₄: v =₍U₎ u ∧ u =₍U₎ a := by and_intro h₃, h₂
      have h₅: v =₍U₎ a := U.eq.trans v u a h₄
      iterate h₅
    have bwd: v =₍U₎ a → u =₍U₎ a := by
      assume(h₂: v =₍U₎ a)
      have h₃: u =₍U₎ v ∧ v =₍U₎ a := by and_intro h₁, h₂
      have h₄: u =₍U₎ a := U.eq.trans u v a h₃
      iterate h₄
    have h₅: u =₍U₎ a ↔ v =₍U₎ a := by iff_intro fwd, bwd
    iterate h₅

-- Conjunction: P x ∧ Q x
instance congruent_conjunction' {U: Universal} {P Q: U.Particular → Prop}
    [p: CongruentUnary' U P] [q: CongruentUnary' U Q]:
    CongruentUnary' U (x: U.Particular ↦ P x ∧ Q x) where
  cong := by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h₁: a =₍U₎ b)
    have h₂: ∀ (y: U.Particular), a =₍U₎ y → (P a ↔ P y) := by forall_elim p.cong, a
    have h₃: a =₍U₎ b → (P a ↔ P b) := by forall_elim h₂, b
    have h₄: P a ↔ P b := by modus_ponens h₃, h₁
    have h₅: ∀ (y: U.Particular), a =₍U₎ y → (Q a ↔ Q y) := by forall_elim q.cong, a
    have h₆: a =₍U₎ b → (Q a ↔ Q b) := by forall_elim h₅, b
    have h₇: Q a ↔ Q b := by modus_ponens h₆, h₁
    have fwd: P a ∧ Q a → P b ∧ Q b := by
      assume(h₈: P a ∧ Q a)
      have h₉: P a := by and_elim h₈
      have h₁₀: Q a := by and_elim h₈
      have h₁₁: P b := PC₀.deductive_eq_l2r h₄ h₉
      have h₁₂: Q b := PC₀.deductive_eq_l2r h₇ h₁₀
      have h₁₃: P b ∧ Q b := by and_intro h₁₁, h₁₂
      iterate h₁₃
    have bwd: P b ∧ Q b → P a ∧ Q a := by
      assume(h₈: P b ∧ Q b)
      have h₉: P b := by and_elim h₈
      have h₁₀: Q b := by and_elim h₈
      have h₁₁: P a := PC₀.deductive_eq_r2l h₄ h₉
      have h₁₂: Q a := PC₀.deductive_eq_r2l h₇ h₁₀
      have h₁₃: P a ∧ Q a := by and_intro h₁₁, h₁₂
      iterate h₁₃
    have h₁₄: P a ∧ Q a ↔ P b ∧ Q b := by iff_intro fwd, bwd
    iterate h₁₄

-- Existential: ∃ z, P z x
instance congruent_existential' {U₁ U₂: Universal} {P: U₁.Particular → U₂.Particular → Prop}
    [inst: ∀ z: U₁.Particular, CongruentUnary' U₂ (P z)]:
    CongruentUnary' U₂ (x: U₂.Particular ↦ ∃ (z: U₁.Particular), P z x) where
  cong := by forall_intro
    variable(x: U₂.Particular)
    variable(y: U₂.Particular)
    assume(h₀: x =₍U₂₎ y)
    have fwd: (∃ (z: U₁.Particular), P z x) → (∃ (z: U₁.Particular), P z y) := by
      assume(h₁: ∃ (z: U₁.Particular), P z x)
      have ⟨(z: U₁.Particular), (h₂: P z x)⟩ := exists_elim h₁
      have h₃: ∀ (w: U₂.Particular), x =₍U₂₎ w → (P z x ↔ P z w) := by forall_elim (inst z).cong, x
      have h₄: x =₍U₂₎ y → (P z x ↔ P z y) := by forall_elim h₃, y
      have h₅: P z x ↔ P z y := by modus_ponens h₄, h₀
      have h₆: P z y := PC₀.deductive_eq_l2r h₅ h₂
      have h₇: ∃ (z': U₁.Particular), P z' y := by exists_intro h₆, z
      iterate h₇
    have bwd: (∃ (z: U₁.Particular), P z y) → (∃ (z: U₁.Particular), P z x) := by
      assume(h₁: ∃ (z: U₁.Particular), P z y)
      have ⟨(z: U₁.Particular), (h₂: P z y)⟩ := exists_elim h₁
      have h₃: ∀ (w: U₂.Particular), x =₍U₂₎ w → (P z x ↔ P z w) := by forall_elim (inst z).cong, x
      have h₄: x =₍U₂₎ y → (P z x ↔ P z y) := by forall_elim h₃, y
      have h₅: P z x ↔ P z y := by modus_ponens h₄, h₀
      have h₆: P z x := PC₀.deductive_eq_r2l h₅ h₂
      have h₇: ∃ (z': U₁.Particular), P z' x := by exists_intro h₆, z
      iterate h₇
    have h₈: (∃ (z: U₁.Particular), P z x) ↔ (∃ (z: U₁.Particular), P z y) := by iff_intro fwd, bwd
    iterate h₈

-- ============================================================
-- # 5. Binary bridge instance
-- ============================================================

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-10
instance (priority := 50) congruent_binary_from_unary' {U₁ U₂: Universal}
    {P: U₁.Particular → U₂.Particular → Prop}
    [inner: ∀ x: U₁.Particular, CongruentUnary' U₂ (P x)]
    [outer: ∀ z: U₂.Particular, CongruentUnary' U₁ (fun x => P x z)]:
    CongruentBinary' U₁ U₂ P where
  inner_cong := by forall_intro
    variable(x: U₁.Particular)
    variable(y₁: U₂.Particular)
    variable(y₂: U₂.Particular)
    assume(h₁: y₁ =₍U₂₎ y₂)
    have h₂: ∀ (b: U₂.Particular), y₁ =₍U₂₎ b → (P x y₁ ↔ P x b) := by forall_elim (inner x).cong, y₁
    have h₃: y₁ =₍U₂₎ y₂ → (P x y₁ ↔ P x y₂) := by forall_elim h₂, y₂
    have h₄: P x y₁ ↔ P x y₂ := by modus_ponens h₃, h₁
    iterate h₄
  outer_cong := by forall_intro
    variable(x₁: U₁.Particular)
    variable(x₂: U₁.Particular)
    variable(z: U₂.Particular)
    assume(h₁: x₁ =₍U₁₎ x₂)
    have h₂: ∀ (b: U₁.Particular), x₁ =₍U₁₎ b → ((fun x => P x z) x₁ ↔ (fun x => P x z) b) := by forall_elim (outer z).cong, x₁
    have h₃: x₁ =₍U₁₎ x₂ → ((fun x => P x z) x₁ ↔ (fun x => P x z) x₂) := by forall_elim h₂, x₂
    have h₄: (fun x => P x z) x₁ ↔ (fun x => P x z) x₂ := by modus_ponens h₃, h₁
    iterate h₄

-- ============================================================
-- # 6. Tests
-- ============================================================

variable {U V: Universal}

-- Test 1: simple unary — x =₍U₎ a
example (a: U.Particular): CongruentUnaryPredicate' U :=
  (x: U.Particular ↦ x =₍U₎ a)

-- Test 2: constant
example (A: Prop): CongruentUnaryPredicate' U :=
  (_: U.Particular ↦ A)

-- Test 3: conjunction of constant and equality
example (a: U.Particular) (A: Prop): CongruentUnaryPredicate' U :=
  (x: U.Particular ↦ A ∧ x =₍U₎ a)

-- Test 4: existential over equality
example (f: V.Particular → U.Particular): CongruentUnaryPredicate' U :=
  (x: U.Particular ↦ ∃ (z: V.Particular), x =₍U₎ f z)

-- Test 5: simple binary — conjunction of equalities
example (a: U.Particular) (b: V.Particular): CongruentBinaryPredicate' U V :=
  (x: U.Particular, y: V.Particular ↦ x =₍U₎ a ∧ y =₍V₎ b)

-- Test 6: binary with existentials (subsumption-like pattern)
variable {W₁ W₂: Universal}
variable (f: W₁.Particular → U.Particular) (g: W₂.Particular → V.Particular)

example: CongruentBinaryPredicate' U V :=
  (x: U.Particular, y: V.Particular ↦
    ∃ (a': W₁.Particular), ∃ (b': W₂.Particular),
      x =₍U₎ f a' ∧ y =₍V₎ g b')

end Test.AutoCongruenceBinary
