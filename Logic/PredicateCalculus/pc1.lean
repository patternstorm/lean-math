import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

open ND

theorem forall_comm {α: Type} {P: α → α → Prop}: (∀ x, ∀ y, P x y) ↔ (∀ y, ∀ x, P x y) := by
  have h₁: (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
    assume (h₁₁ : ∀ x, ∀ y, P x y)
    have h₁₁: ∀ y, ∀ x, P x y := by forall_intro
        variable (u: α)
        variable (v: α)
        have h₁₁₂: ∀ y, P v y := by forall_elim h₁₁, v
        have h₁₁₃: P v u := by forall_elim h₁₁₂, u
    iterate h₁₁
  have h₂: (∀ y, ∀ x, P x y) → (∀ x, ∀ y, P x y) := by
    assume (h₂₁ : ∀ y, ∀ x, P x y)
    have h₂₁: ∀ x, ∀ y, P x y := by forall_intro
        variable (u: α)
        variable (v: α)
        have h₂₁₂: ∀ x, P x v := by forall_elim h₂₁, v
        have h₂₁₃: P u v := by forall_elim h₂₁₂, u
    iterate h₂₁
  iff_intro h₁, h₂

theorem exists_comm {α: Type} {P: α → α → Prop}: (∃ x, ∃ y, P x y) ↔ (∃ y, ∃ x, P x y) := by
  have h₁: (∃ x, ∃ y, P x y) →  (∃ y, ∃ x, P x y) := by
    assume (h₁₁: ∃ x, ∃ y, P x y)
    have ⟨(a: α), (h₁₂: ∃ y, P a y)⟩ := exists_elim h₁₁
    have ⟨(b: α), (h₁₃: P a b)⟩ := exists_elim h₁₂
    have h₁₄: ∃ x, P x b := by exists_intro h₁₃, a
    have h₁₅: ∃ y, ∃ x, P x y := by exists_intro h₁₄, b
    iterate h₁₅
  have h₂: (∃ y, ∃ x, P x y) →  (∃ x, ∃ y, P x y) := by
    assume (h₂₁: ∃ y, ∃ x, P x y)
    have ⟨(a: α), (h₂₂: ∃ x, P x a)⟩ := exists_elim h₂₁
    have ⟨(b: α), (h₂₃: P b a)⟩ := exists_elim h₂₂
    have h₂₄: ∃ y, P b y := by exists_intro h₂₃, a
    have h₂₅: ∃ x, ∃ y, P x y := by exists_intro h₂₄, b
    iterate h₂₅
  iff_intro h₁, h₂

theorem diagonal_specialization {α: Type} {P: α → α → Prop}: (∀ x, ∀ y, P x y) → (∀ x, P x x) := by
  assume (h₁: ∀ x, ∀ y, P x y)
  have h₂: ∀ x, P x x := by forall_intro
    variable (u: α)
    have h₂₁: ∀ y, P u y := by forall_elim h₁, u
    have h₂₂: P u u := by forall_elim h₂₁, u
    iterate h₂₂
  iterate h₂

theorem diagonal_generalization {α: Type} {P: α → α → Prop}: (∃ x, P x x) → (∃ x, ∃ y, P x y) := by
  assume (h₁: ∃ x, P x x)
  have ⟨(a: α), (h₁₁: P a a)⟩ := exists_elim h₁
  have h₁₂: ∃ y, P a y := by exists_intro h₁₁, a
  have h₁₃: ∃ x, ∃ y, P x y := by exists_intro h₁₂, a
  iterate h₁₃

theorem forall_to_exists {α: Type} [Nonempty α] {P: α → Prop}: (∀ x, P x) → (∃ x, P x) := by
  assume (h₁: ∀ x, P x)
  constant (u: α)
  have h₂: P u := by forall_elim h₁, u
  have h₃: ∃ x, P x := by exists_intro h₂, u
  iterate h₃

theorem exists_forall_imp_forall_exists {α: Type} {P: α → α → Prop}: (∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y) := by
  assume(h₁: ∃ x, ∀ y, P x y)
  have h₂: ∀ y, ∃ x, P x y := by forall_intro
    variable (u: α)
    have ⟨(a: α), (h₂₂: ∀ y, P a y)⟩ := exists_elim h₁
    have h₂₃: P a u := by forall_elim h₂₂, u
    have h₂₄: ∃ x, P x u := by exists_intro h₂₃, a
    iterate h₂₄
  iterate h₂

theorem de_morgan_exists {α: Type} {P: α → Prop}: (¬(∃ x, P x)) ↔ (∀ x, ¬P x) := by
  have h₁: (¬(∃ x, P x)) → (∀ x, ¬P x) := by
    assume (h₁₁: ¬(∃ x, P x))
    have h₁₄: ∀ x, ¬P x := by forall_intro
      variable (u: α)
      have h₁₂: P u → False := by
        assume (h₁₂₁: P u)
        have h₁₂₂: ∃ x, P x := by exists_intro h₁₂₁, u
        contradiction h₁₂₂, h₁₁
      have h₁₃: ¬P u := by reductio_ad_absurdum h₁₂
      iterate h₁₃
    iterate h₁₄
  have h₂: (∀ x, ¬P x) → (¬(∃ x, P x)) := by
    assume (h₂₁: ∀ x, ¬P x)
    have h₂₂: (∃ x, P x) → False := by
      assume (h₂₂₁: ∃ x, P x)
      have ⟨(u: α), (h₂₂₂: P u)⟩  := exists_elim h₂₂₁
      have h₂₂₃: ¬P u := by forall_elim h₂₁, u
      contradiction h₂₂₂, h₂₂₃
    have h₂₃: ¬(∃ x, P x) := by reductio_ad_absurdum h₂₂
    iterate h₂₃
  iff_intro h₁, h₂

theorem de_morgan_forall {α: Type} {P: α → Prop}: (¬(∀ x, P x)) ↔ (∃ x, ¬P x) := by
  have h₁: (¬(∀ x, P x)) → (∃ x, ¬P x) := by
    assume (h₁₁: ¬(∀ x, P x))
    have h₁₂: (¬(∃ x, ¬P x)) → False := by
      assume (h₁₂₁: ¬(∃ x, ¬P x))
      have h₁₂₂: (¬(∃ x, ¬P x)) ↔ (∀ x, ¬¬P x)  := de_morgan_exists
      have h₁₂₃: ((¬(∃ x, ¬P x)) → (∀ x, ¬¬P x)) ∧ ((∀ x, ¬¬P x) → (¬(∃ x, ¬P x)) ) := by iff_elim h₁₂₂
      have h₁₂₄: (¬(∃ x, ¬P x)) → (∀ x, ¬¬P x) := by and_elim h₁₂₃
      have h₁₂₅: ∀ x, ¬¬P x := by modus_ponens h₁₂₄, h₁₂₁
      have h₁₂₆: ∀ x, P x := by forall_intro
        variable (u: α)
        have h₁₂₇: ¬¬P u := by forall_elim h₁₂₅, u
        have h₁₂₈: P u := by neg_elim h₁₂₇
      contradiction h₁₂₆, h₁₁
    have h₁₃: ¬¬(∃ x, ¬P x) := by reductio_ad_absurdum h₁₂
    neg_elim h₁₃
  have h₂: (∃ x, ¬P x) → (¬(∀ x, P x)) := by
    assume (h₂₁: ∃ x, ¬P x)
    have ⟨(a: α), (h₂₂₁: ¬P a)⟩ := exists_elim h₂₁
    have h₂₃: (∀ x, P x) -> False := by
      assume (h₂₃₁: ∀ x, P x)
      have h₂₃₂: P a := by forall_elim h₂₃₁, a
      contradiction h₂₃₂, h₂₂₁
    have h₂₄: ¬(∀ x, P x) := by reductio_ad_absurdum h₂₃
    iterate h₂₃
  iff_intro h₁, h₂

theorem forall_and_full_dist {α: Type} {P Q: α → Prop}: (∀ x, P x) ∧ (∀ x, Q x) ↔ (∀ x, P x ∧ Q x) := by
  have h₁: (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x) := by
    assume (h₁₁: (∀ x, P x) ∧ (∀ x, Q x))
    have h₁₂: ∀ x, P x := by and_elim h₁₁
    have h₁₃: ∀ x, Q x := by and_elim h₁₁
    have h₁₄: ∀ x, P x ∧ Q x := by forall_intro
      variable (u: α)
      have h₁₅: P u := by forall_elim h₁₂, u
      have h₁₆: Q u := by forall_elim h₁₃, u
      have h₁₇: P u ∧ Q u := by and_intro h₁₅, h₁₆
      iterate h₁₇
    iterate h₁₄
  have h₂: (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x) := by
    assume (h₂₁: ∀ x, P x ∧ Q x)
    have h₂₂: ∀ x, P x := by forall_intro
      variable (u: α)
      have h₂₃: P u ∧ Q u := by forall_elim h₂₁, u
      have h₂₄: P u := by and_elim h₂₃
      iterate h₂₄
    have h₂₅: ∀ x, Q x := by forall_intro
      variable (u: α)
      have h₂₆: P u ∧ Q u := by forall_elim h₂₁, u
      have h₂₇: Q u := by and_elim h₂₆
      iterate h₂₇
    have h₂₈: (∀ x, P x) ∧ (∀ x, Q x) := by and_intro h₂₂, h₂₅
    iterate h₂₈
  iff_intro h₁, h₂

theorem forall_or_partial_dist {α: Type} {P Q: α → Prop}: (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x) := by
  assume (h₁: (∀ x, P x) ∨ (∀ x, Q x))
  have h₂: (∀ x, P x) → (∀ x, P x ∨ Q x) := by
    assume (h₂₁: ∀ x, P x)
    have h₂₂: ∀ x, P x ∨ Q x := by forall_intro
      variable (u: α)
      have h₂₃: P u := by forall_elim h₂₁, u
      have h₂₄: P u ∨ Q u := by or_intro h₂₃
      iterate h₂₄
    iterate h₂₂
  have h₃: (∀ x, Q x) → (∀ x, P x ∨ Q x) := by
    assume (h₃₁: ∀ x, Q x)
    variable (u: α)
    have h₃₂: Q u := by forall_elim h₃₁, u
    have h₃₄: P u ∨ Q u := by or_intro h₃₂
    iterate h₃₄
  have h₄: ∀ x, P x ∨ Q x := by or_elimination h₁, h₂, h₃
  iterate h₄

theorem exists_or_full_dist {α: Type} {P Q: α → Prop}: (∃ x, P x) ∨ (∃ x, Q x) ↔ (∃ x, P x ∨ Q x) := by
  have h₁: (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x) := by
    assume (h₁₁: (∃ x, P x) ∨ (∃ x, Q x))
    have h₁₂: (∃ x, P x) → (∃ x, P x ∨ Q x) := by
      assume (h₁₂₁: ∃ x, P x)
      have ⟨(a: α), (h₁₂₂: P a)⟩ := exists_elim h₁₂₁
      have h₁₂₃: P a ∨ Q a := by or_intro h₁₂₂
      have h₁₂₄: ∃ x, P x ∨ Q x := by exists_intro h₁₂₃, a
      iterate h₁₂₄
    have h₁₃: (∃ x, Q x) → (∃ x, P x ∨ Q x) := by
      assume (h₁₃₁: ∃ x, Q x)
      have ⟨(a: α), (h₁₃₂: Q a)⟩ := exists_elim h₁₃₁
      have h₁₃₃: P a ∨ Q a := by or_intro h₁₃₂
      have h₁₃₄: ∃ x, P x ∨ Q x := by exists_intro h₁₃₃, a
      iterate h₁₃₄
    have h₁₄: ∃ x, P x ∨ Q x := by or_elimination h₁₁, h₁₂, h₁₃
    iterate h₁₄
  have h₂: (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) := by
    assume (h₂₁: ∃ x, P x ∨ Q x)
    have ⟨(a: α), (h₂₂: P a ∨ Q a)⟩ := exists_elim h₂₁
    have h₂₃: P a  → ((∃ x, P x) ∨ (∃ x, Q x)) := by
      assume (h₂₃₁: P a)
      have h₂₃₂: ∃ x, P x := by exists_intro h₂₃₁, a
      have h₂₃₃: (∃ x, P x) ∨ (∃ x, Q x) := by or_intro h₂₃₂
      iterate h₂₃₃
    have h₂₄: Q a  → ((∃ x, P x) ∨ (∃ x, Q x)) := by
      assume (h₂₄₁: Q a)
      have h₂₄₂: ∃ x, Q x := by exists_intro h₂₄₁, a
      have h₂₄₃: (∃ x, P x) ∨ (∃ x, Q x) := by or_intro h₂₄₂
      iterate h₂₄₃
    have h₂₅: ((∃ x, P x) ∨ (∃ x, Q x)) := by or_elimination h₂₂, h₂₃, h₂₄
    iterate h₂₅
  iff_intro h₁, h₂

theorem exists_and_partial_dist {α: Type} {P Q: α → Prop}: (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  assume (h₁: ∃ x, P x ∧ Q x)
  have ⟨(a: α), (h₁₁: P a ∧ Q a)⟩ := exists_elim h₁
  have h₁₂: P a := by and_elim h₁₁
  have h₁₃: Q a := by and_elim h₁₁
  have h₁₄: ∃ x, P x := by exists_intro h₁₂, a
  have h₁₅: ∃ x, Q x := by exists_intro h₁₃, a
  have h₁₆: (∃ x, P x) ∧ (∃ x, Q x) := by and_intro h₁₄, h₁₅
  iterate h₁₆

example {α : Type} {P Q R S: α → Prop} (h1: ∀ x, P x → Q x) (h2: ∃ x, R x ∧ S x) (h3: ∀ x, S x → P x): ∃ x, P x ∧ Q x := by
  have ⟨(a: α), (h4: R a ∧ S a)⟩ :=  exists_elim h2
  have h5: ∃ y, R y ∧ S y := by exists_intro h4, a
  sorry

end PC₁

end Logic
