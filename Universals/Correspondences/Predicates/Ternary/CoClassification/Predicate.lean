import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Application.Operation

/-!
# Co-Classification — Ternary Predicate

Co-classification is fundamentally a ternary predicate on (C, b₁, b₂):
two target particulars b₁, b₂ are co-classified by correspondence C iff
there is a unique source particular that co-classifies both of them.

```
co_classified(C, b₁, b₂)  ↔  ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C(↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C(↑{a}ₛₑₜ)
```

The predicate is built in three layers:
- **Inner** co_classified(C, b₁, _) = co_classified_with(_)
- **Middle** co_classified(C, _, _) = co_classified_by(_,_)
- **Outer** (`co_classification_predicate`): congruent ternary predicate on (C, b₁, b₂)
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets

-- # Inner congruent unary predicate
-- For fixed C and b₁, the predicate on b₂: ∃! a, b₁ ∈ C({a}) ∧ b₂ ∈ C({a}).
-- Congruence in b₂ uses mem_def and .cong of C(↑{a}ₛₑₜ).
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
noncomputable def co_classified_with (C: U₁ ⭢ᶜ U₂) (b₁: U₂.Particular): CongruentUnaryPredicate U₂ :=
  let pred: U₂.Particular → Prop := (b₂: U₂.Particular ↦ ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
  let cong: ∀ (b₂: U₂.Particular), ∀ (b₂': U₂.Particular), b₂ =₍U₂₎ b₂' → (pred b₂ ↔ pred b₂') := by forall_intro
    variable(b₂: U₂.Particular)
    variable(b₂': U₂.Particular)
    assume(h₁: b₂ =₍U₂₎ b₂')

    -- Unfold ∃! for both b₂ and b₂'
    let P: U₁.Particular → Prop := (a: U₁.Particular ↦ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
    let P': U₁.Particular → Prop := (a: U₁.Particular ↦ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ))
    have eu_U₁: ∀ (Q: U₁.Particular → Prop), ExistsUnique U₁ Q ↔ (∃ (x: U₁.Particular), Q x ∧ (∀ (y: U₁.Particular), Q y → y =₍U₁₎ x)) := by forall_elim exists_unique_def, U₁
    have eu_P: ExistsUnique U₁ P ↔ (∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P
    have eu_P': ExistsUnique U₁ P' ↔ (∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P'

    have h₂: pred b₂ → pred b₂' := by
      assume(h₂₁: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
      -- Unfold ∃! to ∃ with uniqueness
      have h₂₁': ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P h₂₁
      have ⟨(a: U₁.Particular), (h₂₂: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a))⟩ := exists_elim h₂₁'
      have h₂₃: P a := by and_elim h₂₂
      have h₂₃_unique: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by and_elim h₂₂
      have h₂₃a: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₃
      have h₂₄: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₃
      -- Transfer b₂ membership to b₂' via mem_def + .cong
      have h₂₅: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a}ₛₑₜ)
      have h₂₆: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₂ := by forall_elim h₂₅, b₂
      have h₂₇: (C (↑{a}ₛₑₜ)).pred b₂ := PC₀.deductive_eq_l2r h₂₆ h₂₄
      have h₂₈: ∀ (y: U₂.Particular), b₂ =₍U₂₎ y → ((C (↑{a}ₛₑₜ)).pred b₂ ↔ (C (↑{a}ₛₑₜ)).pred y) := by forall_elim (C (↑{a}ₛₑₜ)).cong, b₂
      have h₂₉: b₂ =₍U₂₎ b₂' → ((C (↑{a}ₛₑₜ)).pred b₂ ↔ (C (↑{a}ₛₑₜ)).pred b₂') := by forall_elim h₂₈, b₂'
      have h₂₁₀: (C (↑{a}ₛₑₜ)).pred b₂ ↔ (C (↑{a}ₛₑₜ)).pred b₂' := by modus_ponens h₂₉, h₁
      have h₂₁₁: (C (↑{a}ₛₑₜ)).pred b₂' := PC₀.deductive_eq_l2r h₂₁₀ h₂₇
      have h₂₁₂: b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₂' := by forall_elim h₂₅, b₂'
      have h₂₁₃: b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₂₁₂ h₂₁₁
      have h₂₁₄: P' a := by and_intro h₂₃a, h₂₁₃
      -- Transfer uniqueness: ∀ y, P' y → y =₍U₁₎ a
      have h₂₁₅: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by forall_intro
        variable(a': U₁.Particular)
        assume(h₂₁₅₁: P' a')
        have h₂₁₅₂: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₂₁₅₁
        have h₂₁₅₃: b₂' ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₂₁₅₁
        -- Transfer b₂' back to b₂ for a'
        have h₂₁₅₄: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a'}ₛₑₜ)
        have h₂₁₅₅: b₂' ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₂' := by forall_elim h₂₁₅₄, b₂'
        have h₂₁₅₆: (C (↑{a'}ₛₑₜ)).pred b₂' := PC₀.deductive_eq_l2r h₂₁₅₅ h₂₁₅₃
        have h₂₁₅₇: ∀ (y: U₂.Particular), b₂ =₍U₂₎ y → ((C (↑{a'}ₛₑₜ)).pred b₂ ↔ (C (↑{a'}ₛₑₜ)).pred y) := by forall_elim (C (↑{a'}ₛₑₜ)).cong, b₂
        have h₂₁₅₈: b₂ =₍U₂₎ b₂' → ((C (↑{a'}ₛₑₜ)).pred b₂ ↔ (C (↑{a'}ₛₑₜ)).pred b₂') := by forall_elim h₂₁₅₇, b₂'
        have h₂₁₅₉: (C (↑{a'}ₛₑₜ)).pred b₂ ↔ (C (↑{a'}ₛₑₜ)).pred b₂' := by modus_ponens h₂₁₅₈, h₁
        have h₂₁₅₁₀: (C (↑{a'}ₛₑₜ)).pred b₂ := PC₀.deductive_eq_r2l h₂₁₅₉ h₂₁₅₆
        have h₂₁₅₁₁: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₂ := by forall_elim h₂₁₅₄, b₂
        have h₂₁₅₁₂: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := PC₀.deductive_eq_r2l h₂₁₅₁₁ h₂₁₅₁₀
        have h₂₁₅₁₃: P a' := by and_intro h₂₁₅₂, h₂₁₅₁₂
        have h₂₁₅₁₄: P a' → a' =₍U₁₎ a := by forall_elim h₂₃_unique, a'
        have h₂₁₅₁₅: a' =₍U₁₎ a := by modus_ponens h₂₁₅₁₄, h₂₁₅₁₃
        iterate h₂₁₅₁₅
      -- Reconstruct ∃!
      have h₂₁₆: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a) := by and_intro h₂₁₄, h₂₁₅
      have h₂₁₇: ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := by exists_intro h₂₁₆, a
      have h₂₁₈: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P' h₂₁₇
      iterate h₂₁₈

    have h₃: pred b₂' → pred b₂ := by
      assume(h₃₁: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have h₃₁': ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P' h₃₁
      have ⟨(a: U₁.Particular), (h₃₂: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a))⟩ := exists_elim h₃₁'
      have h₃₃: P' a := by and_elim h₃₂
      have h₃₃_unique: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by and_elim h₃₂
      have h₃₃a: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₃
      have h₃₄: b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₃
      -- Transfer b₂' membership to b₂ via mem_def + .cong
      have h₃₅: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a}ₛₑₜ)
      have h₃₆: b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₂' := by forall_elim h₃₅, b₂'
      have h₃₇: (C (↑{a}ₛₑₜ)).pred b₂' := PC₀.deductive_eq_l2r h₃₆ h₃₄
      have h₃₈: ∀ (y: U₂.Particular), b₂ =₍U₂₎ y → ((C (↑{a}ₛₑₜ)).pred b₂ ↔ (C (↑{a}ₛₑₜ)).pred y) := by forall_elim (C (↑{a}ₛₑₜ)).cong, b₂
      have h₃₉: b₂ =₍U₂₎ b₂' → ((C (↑{a}ₛₑₜ)).pred b₂ ↔ (C (↑{a}ₛₑₜ)).pred b₂') := by forall_elim h₃₈, b₂'
      have h₃₁₀: (C (↑{a}ₛₑₜ)).pred b₂ ↔ (C (↑{a}ₛₑₜ)).pred b₂' := by modus_ponens h₃₉, h₁
      have h₃₁₁: (C (↑{a}ₛₑₜ)).pred b₂ := PC₀.deductive_eq_r2l h₃₁₀ h₃₇
      have h₃₁₂: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₂ := by forall_elim h₃₅, b₂
      have h₃₁₃: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₃₁₂ h₃₁₁
      have h₃₁₄: P a := by and_intro h₃₃a, h₃₁₃
      -- Transfer uniqueness: ∀ y, P y → y =₍U₁₎ a
      have h₃₁₅: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by forall_intro
        variable(a': U₁.Particular)
        assume(h₃₁₅₁: P a')
        have h₃₁₅₂: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₃₁₅₁
        have h₃₁₅₃: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₃₁₅₁
        -- Transfer b₂ to b₂' for a'
        have h₃₁₅₄: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a'}ₛₑₜ)
        have h₃₁₅₅: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₂ := by forall_elim h₃₁₅₄, b₂
        have h₃₁₅₆: (C (↑{a'}ₛₑₜ)).pred b₂ := PC₀.deductive_eq_l2r h₃₁₅₅ h₃₁₅₃
        have h₃₁₅₇: ∀ (y: U₂.Particular), b₂ =₍U₂₎ y → ((C (↑{a'}ₛₑₜ)).pred b₂ ↔ (C (↑{a'}ₛₑₜ)).pred y) := by forall_elim (C (↑{a'}ₛₑₜ)).cong, b₂
        have h₃₁₅₈: b₂ =₍U₂₎ b₂' → ((C (↑{a'}ₛₑₜ)).pred b₂ ↔ (C (↑{a'}ₛₑₜ)).pred b₂') := by forall_elim h₃₁₅₇, b₂'
        have h₃₁₅₉: (C (↑{a'}ₛₑₜ)).pred b₂ ↔ (C (↑{a'}ₛₑₜ)).pred b₂' := by modus_ponens h₃₁₅₈, h₁
        have h₃₁₅₁₀: (C (↑{a'}ₛₑₜ)).pred b₂' := PC₀.deductive_eq_l2r h₃₁₅₉ h₃₁₅₆
        have h₃₁₅₁₁: b₂' ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₂' := by forall_elim h₃₁₅₄, b₂'
        have h₃₁₅₁₂: b₂' ∈ₛₑₜ C (↑{a'}ₛₑₜ) := PC₀.deductive_eq_r2l h₃₁₅₁₁ h₃₁₅₁₀
        have h₃₁₅₁₃: P' a' := by and_intro h₃₁₅₂, h₃₁₅₁₂
        have h₃₁₅₁₄: P' a' → a' =₍U₁₎ a := by forall_elim h₃₃_unique, a'
        have h₃₁₅₁₅: a' =₍U₁₎ a := by modus_ponens h₃₁₅₁₄, h₃₁₅₁₃
        iterate h₃₁₅₁₅
      -- Reconstruct ∃!
      have h₃₁₆: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a) := by and_intro h₃₁₄, h₃₁₅
      have h₃₁₇: ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := by exists_intro h₃₁₆, a
      have h₃₁₈: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P h₃₁₇
      iterate h₃₁₈

    have h₄: pred b₂ ↔ pred b₂' := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

-- # Co-classification binary predicate
-- Uses co_classified_with for each b₁, then proves cross-argument congruence in b₁.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
noncomputable def co_classified_by (C: U₁ ⭢ᶜ U₂): CongruentBinaryPredicate U₂ U₂ :=
  let pred: U₂.Particular → CongruentUnaryPredicate U₂ := (b₁: U₂.Particular ↦ co_classified_with C b₁)
  let cong: ∀ (b₁: U₂.Particular), ∀ (b₁': U₂.Particular), ∀ (b₂: U₂.Particular),
    b₁ =₍U₂₎ b₁' → ((co_classified_with C b₁).pred b₂ ↔ (co_classified_with C b₁').pred b₂) := by forall_intro
    variable(b₁: U₂.Particular)
    variable(b₁': U₂.Particular)
    variable(b₂: U₂.Particular)
    assume(h₁: b₁ =₍U₂₎ b₁')

    -- Unfold ∃! for both b₁ and b₁'
    let P: U₁.Particular → Prop := (a: U₁.Particular ↦ b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
    let P': U₁.Particular → Prop := (a: U₁.Particular ↦ b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
    have eu_U₁: ∀ (Q: U₁.Particular → Prop), ExistsUnique U₁ Q ↔ (∃ (x: U₁.Particular), Q x ∧ (∀ (y: U₁.Particular), Q y → y =₍U₁₎ x)) := by forall_elim exists_unique_def, U₁
    have eu_P: ExistsUnique U₁ P ↔ (∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P
    have eu_P': ExistsUnique U₁ P' ↔ (∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P'

    have h₂: (co_classified_with C b₁).pred b₂ → (co_classified_with C b₁').pred b₂ := by
      assume(h₂₁: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have h₂₁': ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P h₂₁
      have ⟨(a: U₁.Particular), (h₂₂: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a))⟩ := exists_elim h₂₁'
      have h₂₃: P a := by and_elim h₂₂
      have h₂₃_unique: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by and_elim h₂₂
      have h₂₃a: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₃
      have h₂₄: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₃
      -- Transfer b₁ membership to b₁' via mem_def + .cong
      have h₂₅: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a}ₛₑₜ)
      have h₂₆: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁ := by forall_elim h₂₅, b₁
      have h₂₇: (C (↑{a}ₛₑₜ)).pred b₁ := PC₀.deductive_eq_l2r h₂₆ h₂₃a
      have h₂₈: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred y) := by forall_elim (C (↑{a}ₛₑₜ)).cong, b₁
      have h₂₉: b₁ =₍U₂₎ b₁' → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁') := by forall_elim h₂₈, b₁'
      have h₂₁₀: (C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by modus_ponens h₂₉, h₁
      have h₂₁₁: (C (↑{a}ₛₑₜ)).pred b₁' := PC₀.deductive_eq_l2r h₂₁₀ h₂₇
      have h₂₁₂: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by forall_elim h₂₅, b₁'
      have h₂₁₃: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₂₁₂ h₂₁₁
      have h₂₁₄: P' a := by and_intro h₂₁₃, h₂₄
      -- Transfer uniqueness
      have h₂₁₅: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by forall_intro
        variable(a': U₁.Particular)
        assume(h₂₁₅₁: P' a')
        have h₂₁₅₂: b₁' ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₂₁₅₁
        have h₂₁₅₃: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₂₁₅₁
        -- Transfer b₁' back to b₁ for a'
        have h₂₁₅₄: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a'}ₛₑₜ)
        have h₂₁₅₅: b₁' ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₁' := by forall_elim h₂₁₅₄, b₁'
        have h₂₁₅₆: (C (↑{a'}ₛₑₜ)).pred b₁' := PC₀.deductive_eq_l2r h₂₁₅₅ h₂₁₅₂
        have h₂₁₅₇: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((C (↑{a'}ₛₑₜ)).pred b₁ ↔ (C (↑{a'}ₛₑₜ)).pred y) := by forall_elim (C (↑{a'}ₛₑₜ)).cong, b₁
        have h₂₁₅₈: b₁ =₍U₂₎ b₁' → ((C (↑{a'}ₛₑₜ)).pred b₁ ↔ (C (↑{a'}ₛₑₜ)).pred b₁') := by forall_elim h₂₁₅₇, b₁'
        have h₂₁₅₉: (C (↑{a'}ₛₑₜ)).pred b₁ ↔ (C (↑{a'}ₛₑₜ)).pred b₁' := by modus_ponens h₂₁₅₈, h₁
        have h₂₁₅₁₀: (C (↑{a'}ₛₑₜ)).pred b₁ := PC₀.deductive_eq_r2l h₂₁₅₉ h₂₁₅₆
        have h₂₁₅₁₁: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₁ := by forall_elim h₂₁₅₄, b₁
        have h₂₁₅₁₂: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := PC₀.deductive_eq_r2l h₂₁₅₁₁ h₂₁₅₁₀
        have h₂₁₅₁₃: P a' := by and_intro h₂₁₅₁₂, h₂₁₅₃
        have h₂₁₅₁₄: P a' → a' =₍U₁₎ a := by forall_elim h₂₃_unique, a'
        have h₂₁₅₁₅: a' =₍U₁₎ a := by modus_ponens h₂₁₅₁₄, h₂₁₅₁₃
        iterate h₂₁₅₁₅
      -- Reconstruct ∃!
      have h₂₁₆: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a) := by and_intro h₂₁₄, h₂₁₅
      have h₂₁₇: ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := by exists_intro h₂₁₆, a
      have h₂₁₈: ∃!₍U₁₎ a, b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P' h₂₁₇
      iterate h₂₁₈

    have h₃: (co_classified_with C b₁').pred b₂ → (co_classified_with C b₁).pred b₂ := by
      assume(h₃₁: ∃!₍U₁₎ a, b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have h₃₁': ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P' h₃₁
      have ⟨(a: U₁.Particular), (h₃₂: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a))⟩ := exists_elim h₃₁'
      have h₃₃: P' a := by and_elim h₃₂
      have h₃₃_unique: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by and_elim h₃₂
      have h₃₃a: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₃
      have h₃₄: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₃
      -- Transfer b₁' membership to b₁ via mem_def + .cong
      have h₃₅: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a}ₛₑₜ)
      have h₃₆: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by forall_elim h₃₅, b₁'
      have h₃₇: (C (↑{a}ₛₑₜ)).pred b₁' := PC₀.deductive_eq_l2r h₃₆ h₃₃a
      have h₃₈: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred y) := by forall_elim (C (↑{a}ₛₑₜ)).cong, b₁
      have h₃₉: b₁ =₍U₂₎ b₁' → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁') := by forall_elim h₃₈, b₁'
      have h₃₁₀: (C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by modus_ponens h₃₉, h₁
      have h₃₁₁: (C (↑{a}ₛₑₜ)).pred b₁ := PC₀.deductive_eq_r2l h₃₁₀ h₃₇
      have h₃₁₂: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁ := by forall_elim h₃₅, b₁
      have h₃₁₃: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₃₁₂ h₃₁₁
      have h₃₁₄: P a := by and_intro h₃₁₃, h₃₄
      -- Transfer uniqueness
      have h₃₁₅: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by forall_intro
        variable(a': U₁.Particular)
        assume(h₃₁₅₁: P a')
        have h₃₁₅₂: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₃₁₅₁
        have h₃₁₅₃: b₂ ∈ₛₑₜ C (↑{a'}ₛₑₜ) := by and_elim h₃₁₅₁
        -- Transfer b₁ to b₁' for a'
        have h₃₁₅₄: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a'}ₛₑₜ)
        have h₃₁₅₅: b₁ ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₁ := by forall_elim h₃₁₅₄, b₁
        have h₃₁₅₆: (C (↑{a'}ₛₑₜ)).pred b₁ := PC₀.deductive_eq_l2r h₃₁₅₅ h₃₁₅₂
        have h₃₁₅₇: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((C (↑{a'}ₛₑₜ)).pred b₁ ↔ (C (↑{a'}ₛₑₜ)).pred y) := by forall_elim (C (↑{a'}ₛₑₜ)).cong, b₁
        have h₃₁₅₈: b₁ =₍U₂₎ b₁' → ((C (↑{a'}ₛₑₜ)).pred b₁ ↔ (C (↑{a'}ₛₑₜ)).pred b₁') := by forall_elim h₃₁₅₇, b₁'
        have h₃₁₅₉: (C (↑{a'}ₛₑₜ)).pred b₁ ↔ (C (↑{a'}ₛₑₜ)).pred b₁' := by modus_ponens h₃₁₅₈, h₁
        have h₃₁₅₁₀: (C (↑{a'}ₛₑₜ)).pred b₁' := PC₀.deductive_eq_l2r h₃₁₅₉ h₃₁₅₆
        have h₃₁₅₁₁: b₁' ∈ₛₑₜ C (↑{a'}ₛₑₜ) ↔ (C (↑{a'}ₛₑₜ)).pred b₁' := by forall_elim h₃₁₅₄, b₁'
        have h₃₁₅₁₂: b₁' ∈ₛₑₜ C (↑{a'}ₛₑₜ) := PC₀.deductive_eq_r2l h₃₁₅₁₁ h₃₁₅₁₀
        have h₃₁₅₁₃: P' a' := by and_intro h₃₁₅₁₂, h₃₁₅₃
        have h₃₁₅₁₄: P' a' → a' =₍U₁₎ a := by forall_elim h₃₃_unique, a'
        have h₃₁₅₁₅: a' =₍U₁₎ a := by modus_ponens h₃₁₅₁₄, h₃₁₅₁₃
        iterate h₃₁₅₁₅
      -- Reconstruct ∃!
      have h₃₁₆: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a) := by and_intro h₃₁₄, h₃₁₅
      have h₃₁₇: ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := by exists_intro h₃₁₆, a
      have h₃₁₈: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P h₃₁₇
      iterate h₃₁₈

    have h₄: (co_classified_with C b₁).pred b₂ ↔ (co_classified_with C b₁').pred b₂ := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

-- # Co-classification as a ternary predicate on (Correspondences, U₂, U₂)
-- The outer congruence in C uses apply_cong_first to transfer membership.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-04-04
noncomputable def co_classification_predicate: CongruentTernaryPredicate (U₁ ➞ᶜ U₂) U₂ U₂ :=
  let pred: (U₁ ⭢ᶜ U₂) → CongruentBinaryPredicate U₂ U₂ := (C: U₁ ⭢ᶜ U₂ ↦ co_classified_by C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    C₁ =→ᶜ C₂ → ((co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    variable(b₁: U₂.Particular)
    variable(b₂: U₂.Particular)
    assume(h₁: C₁ =→ᶜ C₂)

    -- Unfold ∃! for both C₁ and C₂
    let P: U₁.Particular → Prop := (a: U₁.Particular ↦ b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ))
    let P': U₁.Particular → Prop := (a: U₁.Particular ↦ b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ))
    have eu_U₁: ∀ (Q: U₁.Particular → Prop), ExistsUnique U₁ Q ↔ (∃ (x: U₁.Particular), Q x ∧ (∀ (y: U₁.Particular), Q y → y =₍U₁₎ x)) := by forall_elim exists_unique_def, U₁
    have eu_P: ExistsUnique U₁ P ↔ (∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P
    have eu_P': ExistsUnique U₁ P' ↔ (∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x)) := by forall_elim eu_U₁, P'

    -- From C₁ =→ᶜ C₂, for any set S: C₁ S =ₛₑₜ C₂ S
    have h₂: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂' S := by forall_elim apply_cong_first, C₁
    have h₃: C₁ =→ᶜ C₂ → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by forall_elim h₂, C₂
    have h₄: ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by modus_ponens h₃, h₁

    -- Forward: ∃! a, b₁ ∈ C₁({a}) ∧ b₂ ∈ C₁({a}) → ∃! a, b₁ ∈ C₂({a}) ∧ b₂ ∈ C₂({a})
    have h₅: (co_classified_with C₁ b₁).pred b₂ → (co_classified_with C₂ b₁).pred b₂ := by
      assume(h₅₁: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ))
      have h₅₁': ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P h₅₁
      have ⟨(a: U₁.Particular), (h₅₂: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a))⟩ := exists_elim h₅₁'
      have h₅₃: P a := by and_elim h₅₂
      have h₅₃_unique: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by and_elim h₅₂
      have h₅₃a: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by and_elim h₅₃
      have h₅₄: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by and_elim h₅₃
      -- Transfer via C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ)
      have h₅₅: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
      have h₅₆: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
      have h₅₇: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₅₆, C₂ (↑{a}ₛₑₜ)
      have h₅₈: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₇ h₅₅
      have h₅₉: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₅₈, b₁
      have h₅₁₀: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₅₈, b₂
      have h₅₁₁: b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₉ h₅₃a
      have h₅₁₂: b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₁₀ h₅₄
      have h₅₁₃: P' a := by and_intro h₅₁₁, h₅₁₂
      -- Transfer uniqueness
      have h₅₁₄: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by forall_intro
        variable(a': U₁.Particular)
        assume(h₅₁₄₁: P' a')
        have h₅₁₄₂: b₁ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by and_elim h₅₁₄₁
        have h₅₁₄₃: b₂ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by and_elim h₅₁₄₁
        -- Transfer back: C₂ → C₁ for a'
        have h₅₁₄₄: C₁ (↑{a'}ₛₑₜ) =ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by forall_elim h₄, (↑{a'}ₛₑₜ)
        have h₅₁₄₅: ∀ (R₂: Set U₂), C₁ (↑{a'}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a'}ₛₑₜ)
        have h₅₁₄₆: C₁ (↑{a'}ₛₑₜ) =ₛₑₜ C₂ (↑{a'}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ)) := by forall_elim h₅₁₄₅, C₂ (↑{a'}ₛₑₜ)
        have h₅₁₄₇: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₁₄₆ h₅₁₄₄
        have h₅₁₄₈: b₁ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ b₁ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by forall_elim h₅₁₄₇, b₁
        have h₅₁₄₉: b₂ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ b₂ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by forall_elim h₅₁₄₇, b₂
        have h₅₁₄₁₀: b₁ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) := PC₀.deductive_eq_r2l h₅₁₄₈ h₅₁₄₂
        have h₅₁₄₁₁: b₂ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) := PC₀.deductive_eq_r2l h₅₁₄₉ h₅₁₄₃
        have h₅₁₄₁₂: P a' := by and_intro h₅₁₄₁₀, h₅₁₄₁₁
        have h₅₁₄₁₃: P a' → a' =₍U₁₎ a := by forall_elim h₅₃_unique, a'
        have h₅₁₄₁₄: a' =₍U₁₎ a := by modus_ponens h₅₁₄₁₃, h₅₁₄₁₂
        iterate h₅₁₄₁₄
      -- Reconstruct ∃!
      have h₅₁₅: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a) := by and_intro h₅₁₃, h₅₁₄
      have h₅₁₆: ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := by exists_intro h₅₁₅, a
      have h₅₁₇: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P' h₅₁₆
      iterate h₅₁₇

    -- Backward: ∃! a, b₁ ∈ C₂({a}) ∧ b₂ ∈ C₂({a}) → ∃! a, b₁ ∈ C₁({a}) ∧ b₂ ∈ C₁({a})
    have h₆: (co_classified_with C₂ b₁).pred b₂ → (co_classified_with C₁ b₁).pred b₂ := by
      assume(h₆₁: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ))
      have h₆₁': ∃ (x: U₁.Particular), P' x ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ x) := PC₀.deductive_eq_l2r eu_P' h₆₁
      have ⟨(a: U₁.Particular), (h₆₂: P' a ∧ (∀ (y: U₁.Particular), P' y → y =₍U₁₎ a))⟩ := exists_elim h₆₁'
      have h₆₃: P' a := by and_elim h₆₂
      have h₆₃_unique: ∀ (y: U₁.Particular), P' y → y =₍U₁₎ a := by and_elim h₆₂
      have h₆₃a: b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by and_elim h₆₃
      have h₆₄: b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by and_elim h₆₃
      -- Transfer via C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ)
      have h₆₅: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
      have h₆₆: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
      have h₆₇: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₆₆, C₂ (↑{a}ₛₑₜ)
      have h₆₈: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₆₇ h₆₅
      have h₆₉: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆₈, b₁
      have h₆₁₀: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆₈, b₂
      have h₆₁₁: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₆₉ h₆₃a
      have h₆₁₂: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₆₁₀ h₆₄
      have h₆₁₃: P a := by and_intro h₆₁₁, h₆₁₂
      -- Transfer uniqueness
      have h₆₁₄: ∀ (y: U₁.Particular), P y → y =₍U₁₎ a := by forall_intro
        variable(a': U₁.Particular)
        assume(h₆₁₄₁: P a')
        have h₆₁₄₂: b₁ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) := by and_elim h₆₁₄₁
        have h₆₁₄₃: b₂ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) := by and_elim h₆₁₄₁
        -- Transfer: C₁ → C₂ for a'
        have h₆₁₄₄: C₁ (↑{a'}ₛₑₜ) =ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by forall_elim h₄, (↑{a'}ₛₑₜ)
        have h₆₁₄₅: ∀ (R₂: Set U₂), C₁ (↑{a'}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a'}ₛₑₜ)
        have h₆₁₄₆: C₁ (↑{a'}ₛₑₜ) =ₛₑₜ C₂ (↑{a'}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ)) := by forall_elim h₆₁₄₅, C₂ (↑{a'}ₛₑₜ)
        have h₆₁₄₇: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := PC₀.deductive_eq_l2r h₆₁₄₆ h₆₁₄₄
        have h₆₁₄₈: b₁ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ b₁ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by forall_elim h₆₁₄₇, b₁
        have h₆₁₄₉: b₂ ∈ₛₑₜ C₁ (↑{a'}ₛₑₜ) ↔ b₂ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := by forall_elim h₆₁₄₇, b₂
        have h₆₁₄₁₀: b₁ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := PC₀.deductive_eq_l2r h₆₁₄₈ h₆₁₄₂
        have h₆₁₄₁₁: b₂ ∈ₛₑₜ C₂ (↑{a'}ₛₑₜ) := PC₀.deductive_eq_l2r h₆₁₄₉ h₆₁₄₃
        have h₆₁₄₁₂: P' a' := by and_intro h₆₁₄₁₀, h₆₁₄₁₁
        have h₆₁₄₁₃: P' a' → a' =₍U₁₎ a := by forall_elim h₆₃_unique, a'
        have h₆₁₄₁₄: a' =₍U₁₎ a := by modus_ponens h₆₁₄₁₃, h₆₁₄₁₂
        iterate h₆₁₄₁₄
      -- Reconstruct ∃!
      have h₆₁₅: P a ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ a) := by and_intro h₆₁₃, h₆₁₄
      have h₆₁₆: ∃ (x: U₁.Particular), P x ∧ (∀ (y: U₁.Particular), P y → y =₍U₁₎ x) := by exists_intro h₆₁₅, a
      have h₆₁₇: ∃!₍U₁₎ a, b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l eu_P h₆₁₆
      iterate h₆₁₇

    have h₇: (co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂ := by iff_intro h₅, h₆
    iterate h₇
  { pred := pred, cong := cong }

end Correspondences

end Universe
