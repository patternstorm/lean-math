import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Operations.Unary.Application.Operation

/-!
# Co-Classification — Ternary Predicate

Co-classification is fundamentally a ternary predicate on (C, b₁, b₂):
two target particulars b₁, b₂ are co-classified by correspondence C iff
they belong to the same class in the basis — some source particular
co-classifies both of them.

```
(co_classified_with C b₁).pred b₂  ↔  ∃ a : U₁, b₁ ∈ₛₑₜ C(↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C(↑{a}ₛₑₜ)
```

The predicate is built in three layers:
- **Inner** (`co_classified_with C b₁`): congruent unary predicate on b₂
- **Middle** (`co_classified_by C`): congruent binary predicate on (b₁, b₂)
- **Outer** (`co_classification_predicate`): congruent ternary predicate on (C, b₁, b₂)
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Logic.ND
open Sets

-- # Inner congruent unary predicate
-- For fixed C and b₁, the predicate on b₂: ∃ a, b₁ ∈ C({a}) ∧ b₂ ∈ C({a}).
-- Congruence in b₂ uses mem_def and .cong of C(↑{a}ₛₑₜ).
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
noncomputable def co_classified_with (C: U₁ ⭢ᶜ U₂) (b₁: U₂.Particular): CongruentUnaryPredicate U₂ :=
  let pred := (b₂: U₂.Particular ↦ ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
  let cong: ∀ (b₂: U₂.Particular), ∀ (b₂': U₂.Particular), b₂ =₍U₂₎ b₂' → (pred b₂ ↔ pred b₂') := by forall_intro
    variable(b₂: U₂.Particular)
    variable(b₂': U₂.Particular)
    assume(h₁: b₂ =₍U₂₎ b₂')

    have h₂: pred b₂ → pred b₂' := by
      assume(h₂₁: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have ⟨(a: U₁.Particular), (h₂₂: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))⟩ := exists_elim h₂₁
      have h₂₃: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₂
      have h₂₄: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₂
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
      have h₂₁₄: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_intro h₂₃, h₂₁₃
      have h₂₁₅: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by exists_intro h₂₁₄, a
      iterate h₂₁₅

    have h₃: pred b₂' → pred b₂ := by
      assume(h₃₁: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have ⟨(a: U₁.Particular), (h₃₂: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ))⟩ := exists_elim h₃₁
      have h₃₃: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₂
      have h₃₄: b₂' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₂
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
      have h₃₁₄: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_intro h₃₃, h₃₁₃
      have h₃₁₅: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by exists_intro h₃₁₄, a
      iterate h₃₁₅

    have h₄: pred b₂ ↔ pred b₂' := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

-- # Co-classification binary predicate
-- Uses co_classified_with for each b₁, then proves cross-argument congruence in b₁.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
noncomputable def co_classified_by (C: U₁ ⭢ᶜ U₂): CongruentBinaryPredicate U₂ U₂ :=
  let pred := (b₁: U₂.Particular ↦ co_classified_with C b₁)
  let cong: ∀ (b₁: U₂.Particular), ∀ (b₁': U₂.Particular), ∀ (b₂: U₂.Particular),
    b₁ =₍U₂₎ b₁' → ((co_classified_with C b₁).pred b₂ ↔ (co_classified_with C b₁').pred b₂) := by forall_intro
    variable(b₁: U₂.Particular)
    variable(b₁': U₂.Particular)
    variable(b₂: U₂.Particular)
    assume(h₁: b₁ =₍U₂₎ b₁')

    have h₂: (co_classified_with C b₁).pred b₂ → (co_classified_with C b₁').pred b₂ := by
      assume(h₂₁: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have ⟨(a: U₁.Particular), (h₂₂: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))⟩ := exists_elim h₂₁
      have h₂₃: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₂
      have h₂₄: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₂₂
      -- Transfer b₁ membership to b₁' via mem_def + .cong
      have h₂₅: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a}ₛₑₜ)
      have h₂₆: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁ := by forall_elim h₂₅, b₁
      have h₂₇: (C (↑{a}ₛₑₜ)).pred b₁ := PC₀.deductive_eq_l2r h₂₆ h₂₃
      have h₂₈: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred y) := by forall_elim (C (↑{a}ₛₑₜ)).cong, b₁
      have h₂₉: b₁ =₍U₂₎ b₁' → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁') := by forall_elim h₂₈, b₁'
      have h₂₁₀: (C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by modus_ponens h₂₉, h₁
      have h₂₁₁: (C (↑{a}ₛₑₜ)).pred b₁' := PC₀.deductive_eq_l2r h₂₁₀ h₂₇
      have h₂₁₂: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by forall_elim h₂₅, b₁'
      have h₂₁₃: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₂₁₂ h₂₁₁
      have h₂₁₄: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_intro h₂₁₃, h₂₄
      have h₂₁₅: ∃ (a: U₁.Particular), b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by exists_intro h₂₁₄, a
      iterate h₂₁₅

    have h₃: (co_classified_with C b₁').pred b₂ → (co_classified_with C b₁).pred b₂ := by
      assume(h₃₁: ∃ (a: U₁.Particular), b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))
      have ⟨(a: U₁.Particular), (h₃₂: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ))⟩ := exists_elim h₃₁
      have h₃₃: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₂
      have h₃₄: b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_elim h₃₂
      -- Transfer b₁' membership to b₁ via mem_def + .cong
      have h₃₅: ∀ (x: U₂.Particular), x ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred x := by forall_elim mem_def, C (↑{a}ₛₑₜ)
      have h₃₆: b₁' ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by forall_elim h₃₅, b₁'
      have h₃₇: (C (↑{a}ₛₑₜ)).pred b₁' := PC₀.deductive_eq_l2r h₃₆ h₃₃
      have h₃₈: ∀ (y: U₂.Particular), b₁ =₍U₂₎ y → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred y) := by forall_elim (C (↑{a}ₛₑₜ)).cong, b₁
      have h₃₉: b₁ =₍U₂₎ b₁' → ((C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁') := by forall_elim h₃₈, b₁'
      have h₃₁₀: (C (↑{a}ₛₑₜ)).pred b₁ ↔ (C (↑{a}ₛₑₜ)).pred b₁' := by modus_ponens h₃₉, h₁
      have h₃₁₁: (C (↑{a}ₛₑₜ)).pred b₁ := PC₀.deductive_eq_r2l h₃₁₀ h₃₇
      have h₃₁₂: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ↔ (C (↑{a}ₛₑₜ)).pred b₁ := by forall_elim h₃₅, b₁
      have h₃₁₃: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₃₁₂ h₃₁₁
      have h₃₁₄: b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by and_intro h₃₁₃, h₃₄
      have h₃₁₅: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C (↑{a}ₛₑₜ) := by exists_intro h₃₁₄, a
      iterate h₃₁₅

    have h₄: (co_classified_with C b₁).pred b₂ ↔ (co_classified_with C b₁').pred b₂ := by iff_intro h₂, h₃
    iterate h₄
  { pred := pred, cong := cong }

-- # Co-classification as a ternary predicate on (Correspondences, U₂, U₂)
-- The outer congruence in C uses apply_cong_first to transfer membership.
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-03-22
noncomputable def co_classification_predicate: CongruentTernaryPredicate (U₁ ➞ᶜ U₂) U₂ U₂ :=
  let pred := (C: U₁ ⭢ᶜ U₂ ↦ co_classified_by C)
  let cong: ∀ (C₁: U₁ ⭢ᶜ U₂), ∀ (C₂: U₁ ⭢ᶜ U₂), ∀ (b₁: U₂.Particular), ∀ (b₂: U₂.Particular),
    C₁ =→ᶜ C₂ → ((co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂) := by forall_intro
    variable(C₁: U₁ ⭢ᶜ U₂)
    variable(C₂: U₁ ⭢ᶜ U₂)
    variable(b₁: U₂.Particular)
    variable(b₂: U₂.Particular)
    assume(h₁: C₁ =→ᶜ C₂)

    -- From C₁ =→ᶜ C₂, for any set S: C₁ S =ₛₑₜ C₂ S
    have h₂: ∀ (C₂': U₁ ⭢ᶜ U₂), C₁ =→ᶜ C₂' → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂' S := by forall_elim apply_cong_first, C₁
    have h₃: C₁ =→ᶜ C₂ → ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by forall_elim h₂, C₂
    have h₄: ∀ (S: Set U₁), C₁ S =ₛₑₜ C₂ S := by modus_ponens h₃, h₁

    -- Forward: ∃ a, b₁ ∈ C₁({a}) ∧ b₂ ∈ C₁({a}) → ∃ a, b₁ ∈ C₂({a}) ∧ b₂ ∈ C₂({a})
    have h₅: (co_classified_with C₁ b₁).pred b₂ → (co_classified_with C₂ b₁).pred b₂ := by
      assume(h₅₁: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ))
      have ⟨(a: U₁.Particular), (h₅₂: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ))⟩ := exists_elim h₅₁
      have h₅₃: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by and_elim h₅₂
      have h₅₄: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by and_elim h₅₂
      -- Transfer via C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ)
      have h₅₅: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
      have h₅₆: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
      have h₅₇: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₅₆, C₂ (↑{a}ₛₑₜ)
      have h₅₈: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₇ h₅₅
      have h₅₉: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₅₈, b₁
      have h₅₁₀: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₅₈, b₂
      have h₅₁₁: b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₉ h₅₃
      have h₅₁₂: b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₅₁₀ h₅₄
      have h₅₁₃: b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by and_intro h₅₁₁, h₅₁₂
      have h₅₁₄: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by exists_intro h₅₁₃, a
      iterate h₅₁₄

    -- Backward: ∃ a, b₁ ∈ C₂({a}) ∧ b₂ ∈ C₂({a}) → ∃ a, b₁ ∈ C₁({a}) ∧ b₂ ∈ C₁({a})
    have h₆: (co_classified_with C₂ b₁).pred b₂ → (co_classified_with C₁ b₁).pred b₂ := by
      assume(h₆₁: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ))
      have ⟨(a: U₁.Particular), (h₆₂: b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ))⟩ := exists_elim h₆₁
      have h₆₃: b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by and_elim h₆₂
      have h₆₄: b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by and_elim h₆₂
      -- Transfer via C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ)
      have h₆₅: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₄, (↑{a}ₛₑₜ)
      have h₆₆: ∀ (R₂: Set U₂), C₁ (↑{a}ₛₑₜ) =ₛₑₜ R₂ ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ R₂) := by forall_elim set_extensionality, C₁ (↑{a}ₛₑₜ)
      have h₆₇: C₁ (↑{a}ₛₑₜ) =ₛₑₜ C₂ (↑{a}ₛₑₜ) ↔ (∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ)) := by forall_elim h₆₆, C₂ (↑{a}ₛₑₜ)
      have h₆₈: ∀ (y: U₂.Particular), y ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ y ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := PC₀.deductive_eq_l2r h₆₇ h₆₅
      have h₆₉: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₁ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆₈, b₁
      have h₆₁₀: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ↔ b₂ ∈ₛₑₜ C₂ (↑{a}ₛₑₜ) := by forall_elim h₆₈, b₂
      have h₆₁₁: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₆₉ h₆₃
      have h₆₁₂: b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := PC₀.deductive_eq_r2l h₆₁₀ h₆₄
      have h₆₁₃: b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by and_intro h₆₁₁, h₆₁₂
      have h₆₁₄: ∃ (a: U₁.Particular), b₁ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) ∧ b₂ ∈ₛₑₜ C₁ (↑{a}ₛₑₜ) := by exists_intro h₆₁₃, a
      iterate h₆₁₄

    have h₇: (co_classified_with C₁ b₁).pred b₂ ↔ (co_classified_with C₂ b₁).pred b₂ := by iff_intro h₅, h₆
    iterate h₇
  { pred := pred, cong := cong }

end Correspondences

end Universe
