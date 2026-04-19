import Logic.PredicateCalculus.Schemas.SubUniversal.Schema
import Logic.PredicateCalculus.Schemas.RefinedUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Instances.Equals
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁

/-!
# Refined universals are sub-universals

For every universal U and congruent unary predicate P on U, the refined
universal U ↾ P embeds into U. This file defines the following schemas,
parameterized over U and P:

- `embedding_graph`: the binary predicate G(x, y) = ↑x =₍U₎ y, built from `equal_to`
- `embedding_sym` + `embedding_def`: the operation symbol and its
  defining axiom, following the standard ADT pattern (axiom + defining iff)
- `embedding`: the congruent unary operation bundling graph, symbol, and
  defining axiom
- `is_subuniversal`: the sub-universal proof, deriving `preserves_eq` from the
  defining axiom using the ND framework

-/

-- The binary predicate G(x, y) = ↑x =₍U₎ y, built from the schema-level `equal_to`.
-- Inner congruence (in y) is provided by `equal_to`. Outer congruence (in x) is
-- proved from transitivity and symmetry of U.eq.
--
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-12
noncomputable def embedding_graph {U: Universal} (P: CongruentUnaryPredicate U): CongruentBinaryPredicate (U ↾ P) U :=
  let Uₚ: Universal := U ↾ P
  let pred: Uₚ.Particular → CongruentUnaryPredicate U := (x: Uₚ.Particular ↦ equal_to ↑x)
  -- Outer congruence (in x): x₁ =₍Uₚ₎ x₂ → (↑x₁ =₍U₎ z ↔ ↑x₂ =₍U₎ z)
  -- x₁ =₍Uₚ₎ x₂ is definitionally ↑x₁ =₍U₎ ↑x₂, so this follows
  -- from transitivity and symmetry of U.eq.
  let cong: ∀ (x₁: Uₚ.Particular), ∀ (x₂: Uₚ.Particular), ∀ (z: U.Particular), x₁ =₍Uₚ₎ x₂ → ((pred x₁).pred z ↔ (pred x₂).pred z) := by forall_intro
    variable(x₁: Uₚ.Particular)
    variable(x₂: Uₚ.Particular)
    variable(z: U.Particular)
    assume(h₁: x₁ =₍Uₚ₎ x₂)
    -- h₁ is definitionally ↑x₁ =₍U₎ ↑x₂
    have h₂: (pred x₁).pred z → (pred x₂).pred z := by
      assume(h₃: ↑x₁ =₍U₎ z)
      have h₄: ↑x₁ =₍U₎ ↑x₂ → ↑x₂ =₍U₎ ↑x₁ := by forall_elim U.eq.sym, ↑x₁, ↑x₂
      have h₅: ↑x₂ =₍U₎ ↑x₁ := by modus_ponens h₄, h₁
      have h₆: ↑x₂ =₍U₎ ↑x₁ ∧ ↑x₁ =₍U₎ z := by and_intro h₅, h₃
      have h₇: ↑x₂ =₍U₎ ↑x₁ ∧ ↑x₁ =₍U₎ z → ↑x₂ =₍U₎ z := by forall_elim U.eq.trans, ↑x₂, ↑x₁, z
      have h₈: ↑x₂ =₍U₎ z := by modus_ponens h₇, h₆
      iterate h₈
    have h₉: (pred x₂).pred z → (pred x₁).pred z := by
      assume(h₁₀: ↑x₂ =₍U₎ z)
      have h₁₁: ↑x₁ =₍U₎ ↑x₂ ∧ ↑x₂ =₍U₎ z := by and_intro h₁, h₁₀
      have h₁₂: ↑x₁ =₍U₎ ↑x₂ ∧ ↑x₂ =₍U₎ z → ↑x₁ =₍U₎ z := by forall_elim U.eq.trans, ↑x₁, ↑x₂, z
      have h₁₃: ↑x₁ =₍U₎ z := by modus_ponens h₁₂, h₁₁
      iterate h₁₃
    have h₁₄: (pred x₁).pred z ↔ (pred x₂).pred z := by iff_intro h₂, h₉
    iterate h₁₄
  { pred := pred, cong := cong }

-- The embedding operation symbol: the canonical injection (U ↾ P) → U.
-- Defining axiom: embedding_sym P x =₍U₎ y ↔ ↑x =₍U₎ y.
axiom embedding_sym {U: Universal} (P: CongruentUnaryPredicate U):(U ↾ P).Particular → U.Particular
axiom embedding_def {U: Universal} (P: CongruentUnaryPredicate U): ∀ (x: (U ↾ P).Particular), ∀ (y: U.Particular),
    (embedding_sym P x =₍U₎ y) ↔ ((embedding_graph P).pred x).pred y

noncomputable def embedding {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P) ⟴ U :=
  { ext := embedding_graph P, op := embedding_sym P, «def» := embedding_def P }

-- A refined universal U ↾ P is a sub-universal of U.
-- The proof derives preserves_eq from the defining axiom of the embedding.
--
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-12
noncomputable def is_subuniversal {U: Universal} (P: CongruentUnaryPredicate U): (U ↾ P) <: U :=
  let Uₚ: Universal := U ↾ P
  let e: (U ↾ P) ⟴ U := embedding P
  -- Key lemma: e z =₍U₎ ↑z (the symbol agrees with the coercion).
  -- From the defining axiom at (z, ↑z): e z =₍U₎ ↑z ↔ ↑z =₍U₎ ↑z.
  -- The RHS holds by reflexivity, so the LHS holds.
  let e_val: ∀ (z: Uₚ.Particular), e z =₍U₎ ↑z := by forall_intro
    variable(z: Uₚ.Particular)
    have h₁: ∀ (w: U.Particular), (e z =₍U₎ w) ↔ (e.ext.pred z).pred w := by forall_elim e.«def», z
    have h₂: (e z =₍U₎ ↑z) ↔ (e.ext.pred z).pred ↑z := by forall_elim h₁, ↑z
    have h₃: ↑z =₍U₎ ↑z := by forall_elim U.eq.refl, ↑z
    have h₄: e z =₍U₎ ↑z := PC₀.deductive_eq_r2l h₂ h₃
    iterate h₄
  -- preserves_eq: x =₍Uₚ₎ y ↔ e x =₍U₎ e y
  -- Forward: x =₍Uₚ₎ y is ↑x =₍U₎ ↑y. Chain e x =₍U₎ ↑x =₍U₎ ↑y =₍U₎ e y.
  -- Backward: from e x =₍U₎ e y, chain ↑x =₍U₎ e x =₍U₎ e y =₍U₎ ↑y.
  let preserves_eq: ∀ (x: Uₚ.Particular), ∀ (y: Uₚ.Particular),
      x =₍Uₚ₎ y ↔ (e x =₍U₎ e y) := by forall_intro
    variable(x: Uₚ.Particular)
    variable(y: Uₚ.Particular)
    have h₁: e x =₍U₎ ↑x := by forall_elim e_val, x
    have h₂: e y =₍U₎ ↑y := by forall_elim e_val, y
    have h₃: x =₍Uₚ₎ y → (e x =₍U₎ e y) := by
      assume(h₄: x =₍Uₚ₎ y)
      -- h₄ is definitionally ↑x =₍U₎ ↑y
      -- e x =₍U₎ ↑x ∧ ↑x =₍U₎ ↑y → e x =₍U₎ ↑y
      have h₅: e x =₍U₎ ↑x ∧ ↑x =₍U₎ ↑y := by and_intro h₁, h₄
      have h₆: e x =₍U₎ ↑x ∧ ↑x =₍U₎ ↑y → e x =₍U₎ ↑y := by forall_elim U.eq.trans, e x, ↑x, ↑y
      have h₇: e x =₍U₎ ↑y := by modus_ponens h₆, h₅
      -- ↑y =₍U₎ e y (sym of h₂)
      have h₈: e y =₍U₎ ↑y → ↑y =₍U₎ e y := by forall_elim U.eq.sym, e y, ↑y
      have h₉: ↑y =₍U₎ e y := by modus_ponens h₈, h₂
      -- e x =₍U₎ ↑y ∧ ↑y =₍U₎ e y → e x =₍U₎ e y
      have h₁₀: e x =₍U₎ ↑y ∧ ↑y =₍U₎ e y := by and_intro h₇, h₉
      have h₁₁: e x =₍U₎ ↑y ∧ ↑y =₍U₎ e y → e x =₍U₎ e y := by forall_elim U.eq.trans, e x, ↑y, e y
      have h₁₂: e x =₍U₎ e y := by modus_ponens h₁₁, h₁₀
      iterate h₁₂
    have h₁₃: (e x =₍U₎ e y) → x =₍Uₚ₎ y := by
      assume(h₁₄: e x =₍U₎ e y)
      -- ↑x =₍U₎ e x (sym of h₁)
      have h₁₅: e x =₍U₎ ↑x → ↑x =₍U₎ e x := by forall_elim U.eq.sym, e x, ↑x
      have h₁₆: ↑x =₍U₎ e x := by modus_ponens h₁₅, h₁
      -- ↑x =₍U₎ e x ∧ e x =₍U₎ e y → ↑x =₍U₎ e y
      have h₁₇: ↑x =₍U₎ e x ∧ e x =₍U₎ e y := by and_intro h₁₆, h₁₄
      have h₁₈: ↑x =₍U₎ e x ∧ e x =₍U₎ e y → ↑x =₍U₎ e y := by forall_elim U.eq.trans, ↑x, e x, e y
      have h₁₉: ↑x =₍U₎ e y := by modus_ponens h₁₈, h₁₇
      -- ↑x =₍U₎ e y ∧ e y =₍U₎ ↑y → ↑x =₍U₎ ↑y
      have h₂₀: ↑x =₍U₎ e y ∧ e y =₍U₎ ↑y := by and_intro h₁₉, h₂
      have h₂₁: ↑x =₍U₎ e y ∧ e y =₍U₎ ↑y → ↑x =₍U₎ ↑y := by forall_elim U.eq.trans, ↑x, e y, ↑y
      have h₂₂: ↑x =₍U₎ ↑y := by modus_ponens h₂₁, h₂₀
      iterate h₂₂
    have h₂₃: x =₍Uₚ₎ y ↔ (e x =₍U₎ e y) := by iff_intro h₃, h₁₃
    iterate h₂₃
  { embedding := e, preserves_eq := preserves_eq }

end PC₁

end Logic
