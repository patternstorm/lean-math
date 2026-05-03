import Universe
import Logic
import Universals.Dyads.Universal
import Universals.Dyads.Predicates.SubsumeGraph.Properties

namespace Universe
namespace Dyads

open Logic
open Logic.PC₁
open Logic.ND

-- # Subsume graph predicate
private def subsume_graph_pred {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂) (d': U₁' ⋈ U₂') (d: U₁ ⋈ U₂): Prop :=
  ∃ (a': U₁'.Particular), ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b')

-- # Subsume graph unary predicate — fix the left parameter `d'`
--
-- Proof by Claude Opus 4.7, 2026-04-19
noncomputable def subsume_of {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂) (d': U₁' ⋈ U₂'): CongruentUnaryPredicate (U₁ ⧓ U₂) :=
  let pred: U₁ ⋈ U₂ → Prop := subsume_graph_pred e₁ e₂ d'
  let cong: ∀ (d₁: U₁ ⋈ U₂), ∀ (d₂: U₁ ⋈ U₂), d₁ =ₗₓₗ d₂ → (pred d₁ ↔ pred d₂) := by forall_intro
    variable(d₁: U₁ ⋈ U₂)
    variable(d₂: U₁ ⋈ U₂)
    assume(h₀: d₁ =ₗₓₗ d₂)
    -- Forward: from a witness for d₁, build a witness for d₂ by chaining d₂ =ₗₓₗ d₁ =ₗₓₗ image.
    have fwd: pred d₁ → pred d₂ := by
      assume(h₁: pred d₁)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular),
        d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃:
        d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁ =ₗₓₗ d₂ → d₂ =ₗₓₗ d₁ := by forall_elim eq_sym, d₁, d₂
      have h₇: d₂ =ₗₓₗ d₁ := by modus_ponens h₆, h₀
      have h₈: d₂ =ₗₓₗ d₁ ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₇, h₅
      have h₉: d₂ =ₗₓₗ d₁ ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') →
        d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
          forall_elim eq_trans, d₂, d₁, (e₁.embedding a' ⋈ e₂.embedding b')
      have h₁₀: d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by modus_ponens h₉, h₈
      have h₁₁: d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
        and_intro h₄, h₁₀
      have h₁₂: ∃ (b'': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b'') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by exists_intro h₁₁, b'
      have h₁₃: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular), d' =ₗₓₗ (a'' ⋈ b'') ∧ d₂ =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by exists_intro h₁₂, a'
      iterate h₁₃
    -- Backward: symmetric, using d₁ =ₗₓₗ d₂ directly with transitivity.
    have bwd: pred d₂ → pred d₁ := by
      assume(h₁: pred d₂)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃: d' =ₗₓₗ (a' ⋈ b') ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁ =ₗₓₗ d₂ ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₀, h₅
      have h₇: d₁ =ₗₓₗ d₂ ∧ d₂ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') →
        d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
          forall_elim eq_trans, d₁, d₂, (e₁.embedding a' ⋈ e₂.embedding b')
      have h₈: d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by modus_ponens h₇, h₆
      have h₉: d' =ₗₓₗ (a' ⋈ b') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by
        and_intro h₄, h₈
      have h₁₀: ∃ (b'': U₂'.Particular),
        d' =ₗₓₗ (a' ⋈ b'') ∧ d₁ =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by
          exists_intro h₉, b'
      have h₁₁: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular),
        d' =ₗₓₗ (a'' ⋈ b'') ∧ d₁ =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by
          exists_intro h₁₀, a'
      iterate h₁₁
    have result: pred d₁ ↔ pred d₂ := by iff_intro fwd, bwd
    iterate result
  { pred := pred, cong := cong }

-- Proof by Claude Opus 4.7, 2026-04-19
noncomputable def subsume_graph {U₁' U₁ U₂' U₂: Universal} (e₁: U₁' <: U₁) (e₂: U₂' <: U₂): UnaryOperationGraph (U₁' ⧓ U₂') (U₁ ⧓ U₂) :=
  let pred: U₁' ⋈ U₂' → CongruentUnaryPredicate (U₁ ⧓ U₂) := (d': U₁' ⋈ U₂' ↦ subsume_of e₁ e₂ d')
  let cong: ∀ (d₁': U₁' ⋈ U₂'), ∀ (d₂': U₁' ⋈ U₂'), ∀ (d: U₁ ⋈ U₂), d₁' =ₗₓₗ d₂' → ((pred d₁').pred d ↔ (pred d₂').pred d) := by forall_intro
    variable(d₁': U₁' ⋈ U₂')
    variable(d₂': U₁' ⋈ U₂')
    variable(d: U₁ ⋈ U₂)
    assume(h₀: d₁' =ₗₓₗ d₂')
    -- Forward: replace d₁' with d₂' inside the first conjunct by sym + trans.
    have fwd: (pred d₁').pred d → (pred d₂').pred d := by
      assume(h₁: (pred d₁').pred d)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d₁' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃: d₁' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d₁' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁' =ₗₓₗ d₂' → d₂' =ₗₓₗ d₁' := by forall_elim eq_sym, d₁', d₂'
      have h₇: d₂' =ₗₓₗ d₁' := by modus_ponens h₆, h₀
      have h₈: d₂' =ₗₓₗ d₁' ∧ d₁' =ₗₓₗ (a' ⋈ b') := by and_intro h₇, h₄
      have h₉: d₂' =ₗₓₗ d₁' ∧ d₁' =ₗₓₗ (a' ⋈ b') → d₂' =ₗₓₗ (a' ⋈ b') := by forall_elim eq_trans, d₂', d₁', (a' ⋈ b')
      have h₁₀: d₂' =ₗₓₗ (a' ⋈ b') := by modus_ponens h₉, h₈
      have h₁₁: d₂' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₁₀, h₅
      have h₁₂: ∃ (b'': U₂'.Particular), d₂' =ₗₓₗ (a' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by exists_intro h₁₁, b'
      have h₁₃: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular), d₂' =ₗₓₗ (a'' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by exists_intro h₁₂, a'
      iterate h₁₃
    -- Backward: use d₁' =ₗₓₗ d₂' directly with transitivity.
    have bwd: (pred d₂').pred d → (pred d₁').pred d := by
      assume(h₁: (pred d₂').pred d)
      have ⟨(a': U₁'.Particular), (h₂: ∃ (b': U₂'.Particular), d₂' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₁
      have ⟨(b': U₂'.Particular), (h₃: d₂' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'))⟩ := exists_elim h₂
      have h₄: d₂' =ₗₓₗ (a' ⋈ b') := by and_elim h₃
      have h₅: d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_elim h₃
      have h₆: d₁' =ₗₓₗ d₂' ∧ d₂' =ₗₓₗ (a' ⋈ b') := by and_intro h₀, h₄
      have h₇: d₁' =ₗₓₗ d₂' ∧ d₂' =ₗₓₗ (a' ⋈ b') → d₁' =ₗₓₗ (a' ⋈ b') := by forall_elim eq_trans, d₁', d₂', (a' ⋈ b')
      have h₈: d₁' =ₗₓₗ (a' ⋈ b') := by modus_ponens h₇, h₆
      have h₉: d₁' =ₗₓₗ (a' ⋈ b') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b') := by and_intro h₈, h₅
      have h₁₀: ∃ (b'': U₂'.Particular), d₁' =ₗₓₗ (a' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a' ⋈ e₂.embedding b'') := by exists_intro h₉, b'
      have h₁₁: ∃ (a'': U₁'.Particular), ∃ (b'': U₂'.Particular), d₁' =ₗₓₗ (a'' ⋈ b'') ∧ d =ₗₓₗ (e₁.embedding a'' ⋈ e₂.embedding b'') := by exists_intro h₁₀, a'
      iterate h₁₁
    have result: (pred d₁').pred d ↔ (pred d₂').pred d := by iff_intro fwd, bwd
    iterate result
  let ltot := subsume_left_totality e₁ e₂
  let rdet := subsume_right_determinacy e₁ e₂
  { pred := pred, cong := cong, ltot := ltot, rdet := rdet }

end Dyads
end Universe
