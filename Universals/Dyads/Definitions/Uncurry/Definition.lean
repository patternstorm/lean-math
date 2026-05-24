import Universe
import Logic
import Universals.Dyads.Universal

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Predicate Uncurry
-- Axiom scheme: for any binary predicate R on two types, there exists a unary predicate
-- on their Dyad — called `uncurry R` — such that saying something about a and b
-- separately (R a b) is the same as saying it about their dyad (uncurry R (a ⋈ b)).
-- Whatever is true of the pair is true of the dyad, and vice versa. Uncurry just
-- changes the syntactic form — from two placeholders to one — without changing
-- what's being asserted.
--
-- Each concrete binary predicate R generates one instance of this axiom scheme.
-- R is a metavariable ranging over predicate symbols, not a second-order quantification.
--
-- The name "uncurry" is borrowed from function theory, but here it operates on
-- statement templates, not functions.
--
-- Predicate uncurry must be postulated as an axiom scheme rather than proved via
-- lambda abstraction — see README.md § "Variable-Arity Predicates" for why.
--
-- Higher arities compose: for a ternary predicate R(x,y,z), uncurry the last two
-- arguments to get a binary predicate on U₁ and U₂ ⋈ U₃, then uncurry again to get
-- a unary predicate on U₁ ⋈ (U₂ ⋈ U₃). The same two axiom schemes handle any arity.
--
-- This is a conservative definitional extension: it introduces a new predicate symbol
-- defined by equivalence, adding no new theorems in the old language.
--
-- R is a named parameter (not universally quantified) because this is an axiom scheme:
-- each concrete R generates one instance.
axiom uncurry {U₁: Universal}{U₂: Universal} (R: U₁.Particular → U₂.Particular → Prop): U₁ ⋈ U₂ → Prop
axiom uncurry_def {U₁: Universal}{U₂: Universal} (R: U₁.Particular → U₂.Particular → Prop):
  ∀ (a: U₁.Particular), ∀ (b: U₂.Particular), (uncurry R) (a ⋈ b) ↔ R a b

-- # Uncurry Preserves Congruence
-- If P is a congruent binary predicate, then uncurry (applied to the raw
-- binary function extracted from P) is a congruent unary predicate on dyads.
-- This is the inverse of curry_cong: curry goes from unary-on-dyads to binary,
-- uncurry goes from binary to unary-on-dyads.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-05-23
noncomputable def uncurry_cong {U₁ U₂: Universal} (P: CongruentBinaryPredicate U₁ U₂): CongruentUnaryPredicate (U₁ ⧓ U₂) :=
  let R: U₁.Particular → U₂.Particular → Prop := (a: U₁.Particular, b: U₂.Particular ↦ (P.pred a).pred b)
  let pred: U₁ ⋈ U₂ → Prop := uncurry R
  let cong: ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂), d₁ =ₗₓₗ d₂ → (pred d₁ ↔ pred d₂) := by forall_intro
    variable(d₁: U₁ ⋈ U₂)
    variable(d₂: U₁ ⋈ U₂)
    assume(h₁: d₁ =ₗₓₗ d₂)
    -- Decompose d₁ via exhaustiveness
    have h₂: ∃ (a₁: U₁.Particular), ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁) := by forall_elim exhaustiveness, d₁
    have ⟨(a₁: U₁.Particular), (h₃: ∃ (b₁: U₂.Particular), d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₂
    have ⟨(b₁: U₂.Particular), (h₄: d₁ 🟰 (a₁ ⋈ b₁))⟩ := exists_elim h₃
    -- Decompose d₂ via exhaustiveness
    have h₅: ∃ (a₂: U₁.Particular), ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂) := by forall_elim exhaustiveness, d₂
    have ⟨(a₂: U₁.Particular), (h₆: ∃ (b₂: U₂.Particular), d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₅
    have ⟨(b₂: U₂.Particular), (h₇: d₂ 🟰 (a₂ ⋈ b₂))⟩ := exists_elim h₆
    -- Transfer d₁ =ₗₓₗ d₂ to (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) via Leibniz substitution
    let pred₁: U₁ ⋈ U₂ → Prop := (x: U₁ ⋈ U₂ ↦ x =ₗₓₗ d₂)
    have h₈: d₁ 🟰 (a₁ ⋈ b₁) → (pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁)) := by forall_elim leibniz_eq_subs, pred₁, d₁, (a₁ ⋈ b₁)
    have h₉: pred₁ d₁ ↔ pred₁ (a₁ ⋈ b₁) := by modus_ponens h₈, h₄
    have h₁₀: (a₁ ⋈ b₁) =ₗₓₗ d₂ := PC₀.deductive_eq_l2r h₉ h₁
    let pred₂: U₁ ⋈ U₂ → Prop := (x: U₁ ⋈ U₂ ↦ (a₁ ⋈ b₁) =ₗₓₗ x)
    have h₁₁: d₂ 🟰 (a₂ ⋈ b₂) → (pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂)) := by forall_elim leibniz_eq_subs, pred₂, d₂, (a₂ ⋈ b₂)
    have h₁₂: pred₂ d₂ ↔ pred₂ (a₂ ⋈ b₂) := by modus_ponens h₁₁, h₇
    have h₁₃: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₁₂ h₁₀
    -- Extract relata equalities via eq_def
    have h₁₄: (a₁ ⋈ b₁) =ₗₓₗ (a₂ ⋈ b₂) ↔ a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := by forall_elim eq_def, a₁, b₁, a₂, b₂
    have h₁₅: a₁ =₍U₁₎ a₂ ∧ b₁ =₍U₂₎ b₂ := PC₀.deductive_eq_l2r h₁₄ h₁₃
    have h₁₆: a₁ =₍U₁₎ a₂ := by and_elim h₁₅
    have h₁₇: b₁ =₍U₂₎ b₂ := by and_elim h₁₅
    -- Transfer pred to constructor form via Leibniz substitution
    let pred₃: U₁ ⋈ U₂ → Prop := (x: U₁ ⋈ U₂ ↦ pred x)
    have h₁₈: d₁ 🟰 (a₁ ⋈ b₁) → (pred₃ d₁ ↔ pred₃ (a₁ ⋈ b₁)) := by forall_elim leibniz_eq_subs, pred₃, d₁, (a₁ ⋈ b₁)
    have h₁₉: pred d₁ ↔ pred (a₁ ⋈ b₁) := by modus_ponens h₁₈, h₄
    have h₂₀: d₂ 🟰 (a₂ ⋈ b₂) → (pred₃ d₂ ↔ pred₃ (a₂ ⋈ b₂)) := by forall_elim leibniz_eq_subs, pred₃, d₂, (a₂ ⋈ b₂)
    have h₂₁: pred d₂ ↔ pred (a₂ ⋈ b₂) := by modus_ponens h₂₀, h₇
    -- Unfold pred at constructor form via uncurry_def
    have h₂₂: (uncurry R) (a₁ ⋈ b₁) ↔ R a₁ b₁ := by forall_elim uncurry_def R, a₁, b₁
    have h₂₃: (uncurry R) (a₂ ⋈ b₂) ↔ R a₂ b₂ := by forall_elim uncurry_def R, a₂, b₂
    -- Binary congruence: first argument (a₁ =₍U₁₎ a₂)
    have h₂₄: ∀ (y: U₁.Particular), ∀ (z: U₂.Particular), a₁ =₍U₁₎ y → ((P.pred a₁).pred z ↔ (P.pred y).pred z) := by forall_elim P.cong, a₁
    have h₂₅: ∀ (z: U₂.Particular), a₁ =₍U₁₎ a₂ → ((P.pred a₁).pred z ↔ (P.pred a₂).pred z) := by forall_elim h₂₄, a₂
    have h₂₆: a₁ =₍U₁₎ a₂ → ((P.pred a₁).pred b₁ ↔ (P.pred a₂).pred b₁) := by forall_elim h₂₅, b₁
    have h₂₇: (P.pred a₁).pred b₁ ↔ (P.pred a₂).pred b₁ := by modus_ponens h₂₆, h₁₆
    -- Binary congruence: second argument (b₁ =₍U₂₎ b₂)
    have h₂₈: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((P.pred a₂).pred b₁ ↔ (P.pred a₂).pred y) := by forall_elim (P.pred a₂).cong, b₁
    have h₂₉: b₁ =₍U₂₎ b₂ → ((P.pred a₂).pred b₁ ↔ (P.pred a₂).pred b₂) := by forall_elim h₂₈, b₂
    have h₃₀: (P.pred a₂).pred b₁ ↔ (P.pred a₂).pred b₂ := by modus_ponens h₂₉, h₁₇
    -- Chain: pred d₁ → pred d₂
    have h₃₁: pred d₁ → pred d₂ := by
      assume(h₃₁₁: pred d₁)
      have h₃₁₂: pred (a₁ ⋈ b₁) := PC₀.deductive_eq_l2r h₁₉ h₃₁₁
      have h₃₁₃: (P.pred a₁).pred b₁ := PC₀.deductive_eq_l2r h₂₂ h₃₁₂
      have h₃₁₄: (P.pred a₂).pred b₁ := PC₀.deductive_eq_l2r h₂₇ h₃₁₃
      have h₃₁₅: (P.pred a₂).pred b₂ := PC₀.deductive_eq_l2r h₃₀ h₃₁₄
      have h₃₁₆: pred (a₂ ⋈ b₂) := PC₀.deductive_eq_r2l h₂₃ h₃₁₅
      have h₃₁₇: pred d₂ := PC₀.deductive_eq_r2l h₂₁ h₃₁₆
      iterate h₃₁₇
    -- Chain: pred d₂ → pred d₁
    have h₃₂: pred d₂ → pred d₁ := by
      assume(h₃₂₁: pred d₂)
      have h₃₂₂: pred (a₂ ⋈ b₂) := PC₀.deductive_eq_l2r h₂₁ h₃₂₁
      have h₃₂₃: (P.pred a₂).pred b₂ := PC₀.deductive_eq_l2r h₂₃ h₃₂₂
      have h₃₂₄: (P.pred a₂).pred b₁ := PC₀.deductive_eq_r2l h₃₀ h₃₂₃
      have h₃₂₅: (P.pred a₁).pred b₁ := PC₀.deductive_eq_r2l h₂₇ h₃₂₄
      have h₃₂₆: pred (a₁ ⋈ b₁) := PC₀.deductive_eq_r2l h₂₂ h₃₂₅
      have h₃₂₇: pred d₁ := PC₀.deductive_eq_r2l h₁₉ h₃₂₆
      iterate h₃₂₇
    have h₃₃: pred d₁ ↔ pred d₂ := by iff_intro h₃₁, h₃₂
    iterate h₃₃
  { pred := pred, cong := cong }

-- # Uncurry Congruence Instance
-- This lets the CoeDep coercion convert (uncurry R) into a CongruentUnaryPredicate without
-- an explicit call to uncurry_cong.
noncomputable instance congruent_uncurry {U₁ U₂: Universal} {P: CongruentBinaryPredicate U₁ U₂}:
    CongruentUnary (U₁ ⧓ U₂) (uncurry (a: U₁.Particular, b: U₂.Particular ↦ (P.pred a).pred b)) where
  cong := (uncurry_cong P).cong

end Dyads
end Universe
