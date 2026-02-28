import Universe
import Logic
import Universals.Sets.Definitions

/-!
# Test: Relata and the Pred Characterization

This test verifies the proposal that:
1. Typed relata `a ~ b : A ~ B` provide relation-particulars
2. `A ~ B` forms a Universal with component-wise equality
3. Standard Lean curried predicates `A → B → Prop` satisfy the Pred characterization
4. CongruentBinaryPredicate U₁ U₂ converts to CongruentUnaryPredicate (U₁ ~ U₂)
   — binary relations ARE sets of relata
-/

namespace Universe
namespace RelataTest

open Logic
open Logic.PC₁
open Logic.ND

-- ═══════════════════════════════════════════════════════
-- § 1. The ~ type constructor: typed relata
-- ═══════════════════════════════════════════════════════

-- A relatum is a particular that represents a relation between two things.
-- If a : A and b : B then a ~ b : A ~ B — the relatum of a and b.
--
-- Unary predicates select particulars: P(x) picks out elements of a Universal.
-- Higher-arity predicates select relata: R(x,y) picks out relation-particulars
-- from a RelatumUniversal. This is the uniform view: all predicates select
-- particulars — the difference is only what kind of particular (element vs relatum).
--
-- A ~ B is the type of relation-particulars between A-things and B-things.
-- This is not a "pair" or "product" — it is a relatum, a particular
-- representing the relatedness of a and b. The distinction is semantic,
-- not structural: products package data, relata represent relations.

structure Rel (A B : Type) where
  left : A
  right : B

infixr:35 " ~ " => Rel

-- ═══════════════════════════════════════════════════════
-- § 2. Relatum Universal: component-wise equality
-- ═══════════════════════════════════════════════════════

-- Just as particulars of a Universal carry an equality, relata form their own
-- Universal with component-wise equality. This makes RelatumUniversal U₁ U₂
-- a first-class Universal: relata can be quantified over, collected into sets,
-- and subjected to the same predicate/set machinery as any other particulars.
-- Two relata are equal iff their components are equal in their respective Universals.

def RelatumUniversal (U₁ U₂ : Universal) : Universal :=
  let T := U₁.Particular ~ U₂.Particular
  {
    Particular := T
    eq := {
      pred := fun (a : T) (b : T) => a.left =₍U₁₎ b.left ∧ a.right =₍U₂₎ b.right
      refl := fun (a : T) =>
        ⟨U₁.eq.refl a.left, U₂.eq.refl a.right⟩
      sym := fun (a : T) (b : T) (h : a.left =₍U₁₎ b.left ∧ a.right =₍U₂₎ b.right) =>
        ⟨U₁.eq.sym a.left b.left h.left, U₂.eq.sym a.right b.right h.right⟩
      trans := fun (a : T) (b : T) (c : T)
        (h : (a.left =₍U₁₎ b.left ∧ a.right =₍U₂₎ b.right) ∧
             (b.left =₍U₁₎ c.left ∧ b.right =₍U₂₎ c.right)) =>
        ⟨U₁.eq.trans a.left b.left c.left ⟨h.left.left, h.right.left⟩,
         U₂.eq.trans a.right b.right c.right ⟨h.left.right, h.right.right⟩⟩
    }
  }

-- ═══════════════════════════════════════════════════════
-- § 3. Axiom scheme: curry/uncurry as predicate equivalence
-- ═══════════════════════════════════════════════════════

-- These are axiom schemas, not second-order axioms. Each concrete predicate
-- generates one instance. R : A → B → Prop is a metavariable ranging over
-- predicate symbols — a statement template with two placeholders — not a function.
-- (See README.md: "Predicates with free variables are not considered functions.")
--
-- In type theory or HOL, curry/uncurry are provable via lambda abstraction.
-- Here they must be postulated because lambda abstraction treats predicates as
-- functions, introducing the circularity that Functions are derived from predicates.
--
-- These are conservative definitional extensions: they introduce new predicate
-- symbols defined by equivalence, adding no new theorems in the old language.
-- They establish that binary predicates on A and B and unary predicates on A ~ B
-- carry the same propositional content — just transported between domains.

-- Uncurry: binary predicate → unary predicate on relata
axiom uncurry (A B : Type) (R : A → B → Prop) : (A ~ B) → Prop
axiom uncurry_def (A B : Type) (R : A → B → Prop) :
    ∀ (r : A ~ B), uncurry A B R r ↔ R r.left r.right

-- Curry: unary predicate on relata → binary predicate
axiom curry (A B : Type) (P : (A ~ B) → Prop) : A → B → Prop
axiom curry_def (A B : Type) (P : (A ~ B) → Prop) :
    ∀ (a : A), ∀ (b : B), curry A B P a b ↔ P ⟨a, b⟩

-- 3. Theorem: if R is congruent, the uncurried predicate is congruent on the relatum Universal
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-28
theorem uncurry_cong (U₁ U₂ : Universal) (R : CongruentBinaryPredicate U₁ U₂) :
    ∀ (r₁: (RelatumUniversal U₁ U₂).Particular), ∀ (r₂: (RelatumUniversal U₁ U₂).Particular),
      r₁ =₍RelatumUniversal U₁ U₂₎ r₂ →
        (uncurry U₁.Particular U₂.Particular (fun (a: U₁.Particular) (b: U₂.Particular) => (R.pred a).pred b) r₁ ↔
         uncurry U₁.Particular U₂.Particular (fun (a: U₁.Particular) (b: U₂.Particular) => (R.pred a).pred b) r₂) := by forall_intro
  variable(a: (RelatumUniversal U₁ U₂).Particular)
  variable(b: (RelatumUniversal U₁ U₂).Particular)
  assume(h₁: a =₍RelatumUniversal U₁ U₂₎ b)
  -- Let P be the plain binary predicate extracted from R
  let P: U₁.Particular → U₂.Particular → Prop := (x: U₁.Particular ↦ (y: U₂.Particular ↦ (R.pred x).pred y))
  -- Unfold uncurry_def for a and b
  have h₂: uncurry U₁.Particular U₂.Particular P a ↔ P a.left a.right := by forall_elim (uncurry_def U₁.Particular U₂.Particular P), a
  have h₃: uncurry U₁.Particular U₂.Particular P b ↔ P b.left b.right := by forall_elim (uncurry_def U₁.Particular U₂.Particular P), b
  -- Extract component equalities
  have h₁₁: a.left =₍U₁₎ b.left ∧ a.right =₍U₂₎ b.right := h₁
  have h₄: a.left =₍U₁₎ b.left := by and_elim h₁₁
  have h₅: a.right =₍U₂₎ b.right := by and_elim h₁₁
  -- Congruence in the first component via R.cong
  have h₆: ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), a.left =₍U₁₎ y → ((R.pred a.left).pred z ↔ (R.pred y).pred z) := by forall_elim R.cong, a.left
  have h₇: ∀ (z: U₂.Particular), a.left =₍U₁₎ b.left → ((R.pred a.left).pred z ↔ (R.pred b.left).pred z) := by forall_elim h₆, b.left
  have h₈: a.left =₍U₁₎ b.left → ((R.pred a.left).pred a.right ↔ (R.pred b.left).pred a.right) := by forall_elim h₇, a.right
  have h₉: (R.pred a.left).pred a.right ↔ (R.pred b.left).pred a.right := by modus_ponens h₈, h₄
  -- Congruence in the second component via (R.pred b.left).cong
  have h₁₀: ∀ (v: U₂.Particular), a.right =₍U₂₎ v → ((R.pred b.left).pred a.right ↔ (R.pred b.left).pred v) := by forall_elim (R.pred b.left).cong, a.right
  have h₁₁: a.right =₍U₂₎ b.right → ((R.pred b.left).pred a.right ↔ (R.pred b.left).pred b.right) := by forall_elim h₁₀, b.right
  have h₁₂: (R.pred b.left).pred a.right ↔ (R.pred b.left).pred b.right := by modus_ponens h₁₁, h₅
  -- Chain: uncurry a ↔ uncurry b via unfolding through the components
  have h₁₃: uncurry U₁.Particular U₂.Particular P a → uncurry U₁.Particular U₂.Particular P b := by
    assume(h₁₃₁: uncurry U₁.Particular U₂.Particular P a)
    have h₁₃₂: P a.left a.right := PC₀.deductive_eq_l2r h₂ h₁₃₁
    have h₁₃₃: (R.pred b.left).pred a.right := PC₀.deductive_eq_l2r h₉ h₁₃₂
    have h₁₃₄: (R.pred b.left).pred b.right := PC₀.deductive_eq_l2r h₁₂ h₁₃₃
    have h₁₃₅: uncurry U₁.Particular U₂.Particular P b := PC₀.deductive_eq_r2l h₃ h₁₃₄
    iterate h₁₃₅
  have h₁₄: uncurry U₁.Particular U₂.Particular P b → uncurry U₁.Particular U₂.Particular P a := by
    assume(h₁₄₁: uncurry U₁.Particular U₂.Particular P b)
    have h₁₄₂: P b.left b.right := PC₀.deductive_eq_l2r h₃ h₁₄₁
    have h₁₄₃: (R.pred b.left).pred a.right := PC₀.deductive_eq_r2l h₁₂ h₁₄₂
    have h₁₄₄: (R.pred a.left).pred a.right := PC₀.deductive_eq_r2l h₉ h₁₄₃
    have h₁₄₅: uncurry U₁.Particular U₂.Particular P a := PC₀.deductive_eq_r2l h₂ h₁₄₄
    iterate h₁₄₅
  have h₁₅: uncurry U₁.Particular U₂.Particular P a ↔ uncurry U₁.Particular U₂.Particular P b := by iff_intro h₁₃, h₁₄
  iterate h₁₅

-- ═══════════════════════════════════════════════════════
-- § 4. Ternary predicates compose via arity-2 uncurrying
-- ═══════════════════════════════════════════════════════

-- A ternary predicate R : A → B → C → Prop uncurries to (A ~ B ~ C) → Prop
-- by applying uncurry twice. The congruence proof for the ternary case
-- uses only the arity-2 tools (uncurry_def + R.cong).

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-28
theorem tern_intermediate_cong (U₁ U₂ U₃ : Universal) (R : CongruentTernaryPredicate U₁ U₂ U₃) :
    ∀ (x: U₁.Particular), ∀ (y: U₁.Particular), ∀ (r: (RelatumUniversal U₂ U₃).Particular),
      x =₍U₁₎ y →
        (uncurry U₂.Particular U₃.Particular (fun (u: U₂.Particular) (v: U₃.Particular) => ((R.pred x).pred u).pred v) r ↔
         uncurry U₂.Particular U₃.Particular (fun (u: U₂.Particular) (v: U₃.Particular) => ((R.pred y).pred u).pred v) r) := by forall_intro
  variable(x: U₁.Particular)
  variable(y: U₁.Particular)
  variable(r: (RelatumUniversal U₂ U₃).Particular)
  assume(h₁: x =₍U₁₎ y)
  let Px: U₂.Particular → U₃.Particular → Prop := (u: U₂.Particular ↦ (v: U₃.Particular ↦ ((R.pred x).pred u).pred v))
  let Py: U₂.Particular → U₃.Particular → Prop := (u: U₂.Particular ↦ (v: U₃.Particular ↦ ((R.pred y).pred u).pred v))
  -- Unfold uncurry_def for both
  have h₂: uncurry U₂.Particular U₃.Particular Px r ↔ Px r.left r.right := by forall_elim (uncurry_def U₂.Particular U₃.Particular Px), r
  have h₃: uncurry U₂.Particular U₃.Particular Py r ↔ Py r.left r.right := by forall_elim (uncurry_def U₂.Particular U₃.Particular Py), r
  -- Use R.cong to relate Px and Py at the components
  have h₄: ∀ (y': U₁.Particular), ∀ (u: U₂.Particular), ∀ (v: U₃.Particular),
    x =₍U₁₎ y' → (((R.pred x).pred u).pred v ↔ ((R.pred y').pred u).pred v) := by forall_elim R.cong, x
  have h₅: ∀ (u: U₂.Particular), ∀ (v: U₃.Particular),
    x =₍U₁₎ y → (((R.pred x).pred u).pred v ↔ ((R.pred y).pred u).pred v) := by forall_elim h₄, y
  have h₆: ∀ (v: U₃.Particular),
    x =₍U₁₎ y → (((R.pred x).pred r.left).pred v ↔ ((R.pred y).pred r.left).pred v) := by forall_elim h₅, r.left
  have h₇: x =₍U₁₎ y → (((R.pred x).pred r.left).pred r.right ↔ ((R.pred y).pred r.left).pred r.right) := by forall_elim h₆, r.right
  have h₈: Px r.left r.right ↔ Py r.left r.right := by modus_ponens h₇, h₁
  -- Chain through the iff's
  have h₉: uncurry U₂.Particular U₃.Particular Px r → uncurry U₂.Particular U₃.Particular Py r := by
    assume(h₉₁: uncurry U₂.Particular U₃.Particular Px r)
    have h₉₂: Px r.left r.right := PC₀.deductive_eq_l2r h₂ h₉₁
    have h₉₃: Py r.left r.right := PC₀.deductive_eq_l2r h₈ h₉₂
    have h₉₄: uncurry U₂.Particular U₃.Particular Py r := PC₀.deductive_eq_r2l h₃ h₉₃
    iterate h₉₄
  have h₁₀: uncurry U₂.Particular U₃.Particular Py r → uncurry U₂.Particular U₃.Particular Px r := by
    assume(h₁₀₁: uncurry U₂.Particular U₃.Particular Py r)
    have h₁₀₂: Py r.left r.right := PC₀.deductive_eq_l2r h₃ h₁₀₁
    have h₁₀₃: Px r.left r.right := PC₀.deductive_eq_r2l h₈ h₁₀₂
    have h₁₀₄: uncurry U₂.Particular U₃.Particular Px r := PC₀.deductive_eq_r2l h₂ h₁₀₃
    iterate h₁₀₄
  have h₁₁: uncurry U₂.Particular U₃.Particular Px r ↔ uncurry U₂.Particular U₃.Particular Py r := by iff_intro h₉, h₁₀
  iterate h₁₁

end RelataTest
end Universe
