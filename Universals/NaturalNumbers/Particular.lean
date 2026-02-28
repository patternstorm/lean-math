import Universe
import Logic

/-!
# Natural Numbers — Particular

The abstract data type specification for natural numbers.
This defines the type, how to construct its syntactical terms via generative constructors, and the impurifier equations, which
identify which different syntactic terms denote the same canonical term, i.e. they define the equivalence relation on syntactic terms
that defines canonical terms.
-/

namespace Universe

namespace NaturalNumbers

open Logic
open Logic.PC₁
open Logic.ND

-- # Type
axiom NaturalNumber : Type
notation "ℕ" => NaturalNumber

-- # Equality
axiom eq: ℕ → ℕ → Prop
notation:50 a:51 " =ₙₐₜ " b:51 => eq a b

-- # Generative Constructors
axiom zero : ℕ
notation "𝟬" => zero

axiom succ : ℕ → ℕ
prefix:max "𝚜" => succ

-- # Impurifier Equations
-- These define the equivalence relation on syntactic terms that defines canonical terms.
-- For an inductive type with constructors C₁, ..., Cₙ, the impurifier equations form an
-- n×n grid where each cell (Cᵢ, Cⱼ) specifies when Cᵢ(...) =ₜ Cⱼ(...). This is a general
-- method to ensure impurifier equations are properly defined: every pair of constructor
-- applications must have its equality behavior specified.
--
--              𝟬                𝚜 m
--   𝟬      𝟬 =ₙₐₜ 𝟬          ¬(𝟬 =ₙₐₜ 𝚜 m)
--           (always)           (never)
--
--   𝚜 n    ¬(𝚜 n =ₙₐₜ 𝟬)    𝚜 n =ₙₐₜ 𝚜 m ↔ n =ₙₐₜ m
--            (never)        (iff args equal)
--
-- Diagonal cells: same-constructor comparisons.
--   Nullary (𝟬): reflexivity.
--   With arguments (𝚜): biconditional reducing to argument equality.
-- Off-diagonal cells: different-constructor comparisons. For free types (like ℕ),
--   these are always false (no confusion). Other types may identify distinct constructors.
--
-- This grid has exactly one axiom per cell, making the specification symmetric and minimal.
axiom zero_refl: 𝟬 =ₙₐₜ 𝟬
axiom zero_is_not_succ: ∀ (n: ℕ), ¬(𝟬 =ₙₐₜ 𝚜 n)
axiom succ_is_not_zero: ∀ (n: ℕ), ¬(𝚜 n =ₙₐₜ 𝟬)
axiom succ_cong: ∀ (n: ℕ), ∀ (m: ℕ), (𝚜 n) =ₙₐₜ (𝚜 m) ↔ n =ₙₐₜ m

-- # Induction Axiom Instances
-- Specific first-order instances of the standard induction principle,
-- needed to prove that the constructor axioms generate the expected syntactic terms and
-- an equality that is an equivalence relation.
-- Since NaturalNumber is an opaque axiom (not an inductive type), Lean does not provide
-- a recursor or case analysis for it. We provide one instance per predicate rather than
-- the general schema ∀ (P: ℕ → Prop), P(𝟬) → (∀ n, P(n) → P(𝚜 n)) → ∀ n, P(n).
-- Note: the general schema could equally be justified as an axiom schema (with P as a
-- schema parameter, not a second-order quantification), just as we do with leibniz_eq_subs.
-- We choose explicit instances here for clarity about exactly which induction principles
-- the ADT specification requires.
-- (1) exhaustiveness: every term is 𝟬 or 𝚜 k (the "no junk" property of the ADT),
-- (2-4) reflexivity, symmetry, and transitivity of =ₙₐₜ.

-- P(n) = n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k)
axiom exhaustiveness_induction:
    (𝟬 🟰 𝟬 ∨ (∃ (k: ℕ), 𝟬 🟰 𝚜 k)) ∧
    (∀ (n: ℕ), (n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k)) → ((𝚜 n) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 n) 🟰 𝚜 k))) →
    (∀ (n: ℕ), n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k))

theorem exhaustiveness: ∀ (n: ℕ), n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k) := by
    have h₁: 𝟬 🟰 𝟬 := by forall_elim leibniz_eq_refl, 𝟬
    have h₂: 𝟬 🟰 𝟬 ∨ (∃ (k: ℕ), 𝟬 🟰 𝚜 k) := by or_intro h₁
    have h₃: ∀ (n: ℕ), (n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k)) → ((𝚜 n) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 n) 🟰 𝚜 k)) := by forall_intro
        variable(a: ℕ)
        assume(h₃₁: a 🟰 𝟬 ∨ (∃ (k: ℕ), a 🟰 𝚜 k))
        let pred := (x: ℕ ↦ (𝚜 x) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 x) 🟰 𝚜 k))
        have h₃₂: a 🟰 𝟬 → (𝚜 a) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 a) 🟰 𝚜 k) := by
            assume(h₃₃: a 🟰 𝟬)
            have h₃₄: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
            have h₃₅: ∀ (y: ℕ), a 🟰 y → (pred a ↔ pred y) := by forall_elim h₃₄, a
            have h₃₆: a 🟰 𝟬 → (pred a ↔ pred 𝟬) := by forall_elim h₃₅, 𝟬
            have h₃₇: pred a ↔ pred 𝟬 := by modus_ponens h₃₆, h₃₃
            have h₃₈: 𝚜 𝟬 🟰 𝚜 𝟬 := by forall_elim leibniz_eq_refl, 𝚜 𝟬
            have h₃₉: ∃ (k: ℕ), (𝚜 𝟬) 🟰 𝚜 k := by exists_intro h₃₈, 𝟬
            have h₃₁₀: (𝚜 𝟬) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 𝟬) 🟰 𝚜 k) := by or_intro h₃₉
            have h₃₁₁: pred a := PC₀.deductive_eq_r2l h₃₇ h₃₁₀
            iterate h₃₁₁
        have h₃₃: (∃ (k: ℕ), a 🟰 𝚜 k) → ((𝚜 a) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 a) 🟰 𝚜 k)) := by
            assume(h₃₃₁: ∃ (k: ℕ), a 🟰 𝚜 k)
            have ⟨(b: ℕ), (h₃₃₂: a 🟰 𝚜 b)⟩ := exists_elim h₃₃₁
            let pred := (x: ℕ ↦ 𝚜 a 🟰 𝚜 x)
            have h₃₃₃: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
            have h₃₃₄: ∀ (y: ℕ), a 🟰 y → (pred a ↔ pred y) := by forall_elim h₃₃₃, a
            have h₃₃₅: a 🟰 𝚜 b → (pred a ↔ pred 𝚜 b) := by forall_elim h₃₃₄, 𝚜 b
            have h₃₃₆: pred a ↔ pred 𝚜 b := by modus_ponens h₃₃₅, h₃₃₂
            have h₃₃₇: 𝚜 a 🟰 𝚜 a := by forall_elim leibniz_eq_refl, 𝚜 a
            have h₃₃₈: (𝚜 a) 🟰 𝚜 𝚜 b := PC₀.deductive_eq_l2r h₃₃₆ h₃₃₇
            have h₃₃₉: ∃ (k: ℕ), (𝚜 a) 🟰 𝚜 k := by exists_intro h₃₃₈, 𝚜 b
            have h₃₃₁₀: (𝚜 a) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 a) 🟰 𝚜 k) := by or_intro h₃₃₉
            iterate h₃₃₁₀
        have h₃₄: (𝚜 a) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 a) 🟰 𝚜 k) := by or_elimination h₃₁, h₃₂, h₃₃
        iterate h₃₄
    have h₄: (𝟬 🟰 𝟬 ∨ (∃ (k: ℕ), 𝟬 🟰 𝚜 k)) ∧
        (∀ (n: ℕ), (n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k)) → ((𝚜 n) 🟰 𝟬 ∨ (∃ (k: ℕ), (𝚜 n) 🟰 𝚜 k))) := by and_intro h₂, h₃
    have h₅: ∀ (n: ℕ), n 🟰 𝟬 ∨ (∃ (k: ℕ), n 🟰 𝚜 k) := by modus_ponens exhaustiveness_induction, h₄
    iterate h₅

-- P(n) = n =ₙₐₜ n
axiom eq_refl_induction:
    (𝟬 =ₙₐₜ 𝟬) ∧
    (∀ (n: ℕ), n =ₙₐₜ n → (𝚜 n) =ₙₐₜ (𝚜 n)) →
    (∀ (n: ℕ), n =ₙₐₜ n)

-- P(n) = ∀ m, n =ₙₐₜ m → m =ₙₐₜ n
axiom eq_sym_induction:
    (∀ (m: ℕ), 𝟬 =ₙₐₜ m → m =ₙₐₜ 𝟬) ∧
    (∀ (n: ℕ), (∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n) →
        (∀ (m: ℕ), (𝚜 n) =ₙₐₜ m → m =ₙₐₜ (𝚜 n))) →
    (∀ (n: ℕ), ∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n)

-- P(n) = ∀ m p, n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p
axiom eq_trans_induction:
    (∀ (m: ℕ), ∀ (p: ℕ), 𝟬 =ₙₐₜ m ∧ m =ₙₐₜ p → 𝟬 =ₙₐₜ p) ∧
    (∀ (n: ℕ), (∀ (m: ℕ), ∀ (p: ℕ), n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p) →
        (∀ (m: ℕ), ∀ (p: ℕ), (𝚜 n) =ₙₐₜ m ∧ m =ₙₐₜ p → (𝚜 n) =ₙₐₜ p)) →
    (∀ (n: ℕ), ∀ (m: ℕ), ∀ (p: ℕ), n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p)

end NaturalNumbers

end Universe
