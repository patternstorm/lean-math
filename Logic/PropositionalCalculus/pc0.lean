import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₀

theorem identity_principle {P: Prop}: P → P := by
  assume (h₁ : P)
  implication_intro h₁, h₁

theorem deductive_eq_l2r {P Q: Prop} (h₁: P ↔ Q) (h₂: P) : Q := by
  have h₃: P → Q := by iff_elim_l2r h₁
  modus_ponens h₃, h₂

theorem deductive_eq_r2l {P Q: Prop} (h₁: P ↔ Q) (h₂: Q) : P := by
  have h₃: Q → P := by iff_elim_r2l h₁
  modus_ponens h₃, h₂

theorem excluded_middle {P: Prop} : P ∨ ¬P := by
  have h₁: ¬(P ∨ ¬P) → False := by
    assume (h₁₁: ¬(P ∨ ¬P))
    have h₁₂: P → False := by
      assume (h₁₂₁: P)
      have h₁₂₂: P ∨ ¬P := by or_intro h₁₂₁
      contradiction h₁₂₂, h₁₁
    have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
    have h₁₄: ¬P → False := by
      assume (h₁₄₁: ¬P)
      have h₁₄₂: P ∨ ¬P := by or_intro h₁₄₁
      contradiction h₁₄₂, h₁₁
    have h₁₅: ¬¬P := by reductio_ad_absurdum h₁₄
    contradiction h₁₃, h₁₅
  have h₂: ¬¬(P ∨ ¬P) := by reductio_ad_absurdum h₁
  neg_elim h₂

theorem non_contradiction {P: Prop} : ¬(P ∧ ¬P) := by
  have h₁: P ∧ ¬P → False := by
    assume (h₁₁: P ∧ ¬P)
    have h₁₂: P := by and_elim h₁₁
    have h₁₃: ¬P := by and_elim h₁₁
    contradiction h₁₂, h₁₃
  reductio_ad_absurdum h₁

theorem hypothetical_syllogism {P Q R: Prop} (h1: P → Q) (h2: Q → R): P → R := by
  have h3: P → R := by
    assume (h3_1: P)
    have h3_2: Q := by modus_ponens h1, h3_1
    have h3_3: R := by modus_ponens h2, h3_2
    implication_intro h3_1, h3_3
  iterate h3

theorem quodlibet_seqitur {P Q: Prop} (h₁: P) (h₂: ¬P): Q := by
  have h₃: ¬Q → False := by
    assume (h₃₁: ¬Q)
    contradiction h₁, h₂
  have h₄: ¬¬Q := by reductio_ad_absurdum h₃
  neg_elim h₄

theorem disjunctive_syllogism {P Q: Prop} (h₁: P ∨ Q) (h₂: ¬P): Q := by
  have h₃: P → Q := by
    assume (h₃₁: P)
    have h₃₂: Q := quodlibet_seqitur h₃₁ h₂
    implication_intro h₃₁, h₃₂
  have h₄: Q → Q := identity_principle
  or_elimination h₁, h₃, h₄

theorem modus_tollens {P Q: Prop} (h₁: P → Q) (h₂: ¬Q): ¬P := by
  have h₃: P → False := by
    assume (h₃₁: P)
    have h₃₂: Q := by modus_ponens h₁, h₃₁
    contradiction h₃₂, h₂
  reductio_ad_absurdum h₃

theorem double_neg_intro {P: Prop} (h₁: P) : ¬¬P := by
  have h₂: ¬P → False := by
    assume (h₂₁: ¬P)
    contradiction h₁, h₂₁
  reductio_ad_absurdum h₂

theorem medieval_resolution {P Q R: Prop} (h₁: P → Q) (h₂: ¬P → R): Q ∨ R := by
  have h₃: P ∨ ¬P := excluded_middle
  have h₄: P → Q ∨ R := by
    assume (h₄₁: P)
    have h₄₂: Q := by modus_ponens h₁, h₄₁
    have h₄₃: Q ∨ R := by or_intro h₄₂
    iterate h₄₃
  have h₅: ¬P → Q ∨ R := by
    assume (h₅₁: ¬P)
    have h₅₂: R := by modus_ponens h₂, h₅₁
    have h₅₃: Q ∨ R := by or_intro h₅₂
    iterate h₅₃
  or_elimination h₃, h₄, h₅

theorem resolution_non_constructive {P Q R: Prop} (h₁: ¬P ∨ Q) (h₂: P ∨ R): Q ∨ R := by
  have h₃: P ∨ ¬P := excluded_middle
  have h₄: P → Q ∨ R := by
    assume (h₄₁: P)
    have h₄₂: ¬P → Q := by
      assume (h₄₂₁: ¬P)
      have h₄₃: Q := quodlibet_seqitur h₄₁ h₄₂₁
      iterate h₄₃
    have h₄₃: Q → Q := identity_principle
    have h₄₄: Q := by or_elimination h₁, h₄₂, h₄₃
    have h₄₅: Q ∨ R := by or_intro h₄₄
    iterate h₄₅
  have h₅: ¬P → Q ∨ R := by
    assume (h₅₁: ¬P)
    have h₅₂: P → R := by
      assume (h₅₂₁: P)
      have h₅₃: R := quodlibet_seqitur h₅₂₁ h₅₁
      iterate h₅₃
    have h₅₃: R → R := identity_principle
    have h₅₄: R := by or_elimination h₂, h₅₂, h₅₃
    have h₅₅: Q ∨ R := by or_intro h₅₄
    iterate h₅₅
  or_elimination h₃, h₄, h₅

theorem resolution_constructive {P Q R: Prop} (h₁: ¬P ∨ Q) (h₂: P ∨ R): Q ∨ R := by
  have h₃: ¬P → Q ∨ R := by
    assume (h₃₁: ¬P)
    have h₃₂: P → Q ∨ R := by
      assume (h₃₂₁: P)
      have h₃₂₂: Q := quodlibet_seqitur h₃₂₁ h₃₁
      have h₃₂₃: Q ∨ R := by or_intro h₃₂₂
      iterate h₃₂₃
    have h₃₃: R → Q ∨ R := by
      assume (h₃₃₁: R)
      have h₃₃₂: Q ∨ R := by or_intro h₃₃₁
      iterate h₃₃₂
    or_elimination h₂, h₃₂, h₃₃
  have h₄: Q → Q ∨ R := by
    assume (h₄₁: Q)
    have h₄₂: Q ∨ R := by or_intro h₄₁
    iterate h₄₂
  or_elimination h₁, h₃, h₄

theorem incompatbility {P Q: Prop} (h₁: ¬(P ∧ Q)) (h₂: P): ¬Q := by
  have h₃: Q → False := by
    assume (h₃₁: Q)
    have h₃₂: P ∧ Q := by and_intro h₂, h₃₁
    contradiction h₃₂, h₁
  reductio_ad_absurdum h₃

theorem positive_paradox {P Q: Prop}: P → (Q → P) := by
  assume (h₁: P)
  assume (h₂: Q)
  have h₃: P := by iterate h₁
  implication_intro h₂, h₃

theorem material_implication {P Q: Prop}: P → Q ↔ ¬P ∨ Q := by
  have h₁: (P → Q) → (¬P ∨ Q) := by
    assume (h₁₁: P → Q)
    have h₁₂: P ∨ ¬P := excluded_middle
    have h₁₃: P → (¬P ∨ Q) := by
      assume (h₁₃₁: P)
      have h₁₃₂: Q := by modus_ponens h₁₁, h₁₃₁
      have h₁₃₃: ¬P ∨ Q := by or_intro h₁₃₂
      iterate h₁₃₃
    have h₁₄: ¬P → (¬P ∨ Q) := by
      assume (h₁₄₁: ¬P)
      have h₁₄₂: ¬P ∨ Q := by or_intro h₁₄₁
      iterate h₁₄₂
    or_elimination h₁₂, h₁₃, h₁₄
  have h₂: (¬P ∨ Q) → (P → Q) := by
    assume (h₂₁ : ¬P ∨ Q)
    have h₂₂: ¬P → (P → Q) := by
      assume (h₂₂₁: ¬P)
      assume (h₂₂₂: P)
      have h₂₃: Q := quodlibet_seqitur h₂₂₂ h₂₂₁
      iterate h₂₃
    have h₂₃: Q → (P → Q) := positive_paradox
    or_elimination h₂₁, h₂₂, h₂₃
  iff_intro h₁, h₂

theorem de_morgan_disjunction {P Q: Prop}: ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  have h₁: ¬(P ∨ Q) →  (¬P ∧ ¬Q) := by
    assume (h₁₁: ¬(P ∨ Q))
    have h₁₂: P → False := by
      assume (h₁₂₁: P)
      have h₁₂₂: P ∨ Q := by or_intro h₁₂₁
      contradiction h₁₂₂, h₁₁
    have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
    have h₁₄: Q → False := by
      assume (h₁₄₁: Q)
      have h₁₄₂: P ∨ Q := by or_intro h₁₄₁
      contradiction h₁₄₂, h₁₁
    have h₁₅: ¬Q := by reductio_ad_absurdum h₁₄
    and_intro h₁₃, h₁₅
  have h₂: (¬P ∧ ¬Q) → ¬(P ∨ Q) := by
    assume (h₂₁: ¬P ∧ ¬Q)
    have h₂₂: (P ∨ Q) → False := by
      assume (h₂₂₁: P ∨ Q)
      have h₂₂₂: ¬P := by and_elim h₂₁
      have h₂₂₃: Q := disjunctive_syllogism h₂₂₁ h₂₂₂
      have h₂₂₄: ¬Q := by and_elim h₂₁
      contradiction h₂₂₃, h₂₂₄
    reductio_ad_absurdum h₂₂
  iff_intro h₁, h₂

theorem de_morgan_conjunction {P Q: Prop}: ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  have h₁: ¬(¬P ∨ ¬Q) ↔ (¬¬P ∧ ¬¬Q) := de_morgan_disjunction
  have h₂: ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
    assume (h₂₁: ¬(P ∧ Q))
    have h₂₂: P → ¬Q := by
      assume (h₂₂₁: P)
      have h₂₂₂: Q → False := by
        assume (h₂₂₂₁ : Q)
        have h₂₂₂₂: P ∧ Q := by and_intro h₂₂₁, h₂₂₂₁
        contradiction h₂₂₂₂, h₂₁
      reductio_ad_absurdum h₂₂₂
    have h₂₃: (P → ¬Q) ↔ (¬P ∨ ¬Q) := material_implication
    have h₂₃: ((P → ¬Q) → (¬P ∨ ¬Q)) ∧ ((¬P ∨ ¬Q) → (P → ¬Q)) := by iff_elim h₂₃
    have h₂₄: (P → ¬Q) → (¬P ∨ ¬Q) := by and_elim h₂₃
    modus_ponens h₂₄, h₂₂
  have h₃: (¬P ∨ ¬Q) → ¬(P ∧ Q) := by
    assume (h₃₁: ¬P ∨ ¬Q)
    have h₃₂: (P ∧ Q) → False := by
      assume (h₃₂₁: P ∧ Q)
      have h₃₂₂: P := by and_elim h₃₂₁
      have h₃₂₃: ¬¬P := double_neg_intro h₃₂₂
      have h₃₂₄: ¬Q := disjunctive_syllogism h₃₁ h₃₂₃
      have h₃₂₅: Q := by and_elim h₃₂₁
      contradiction h₃₂₅, h₃₂₄
    reductio_ad_absurdum h₃₂
  iff_intro h₂, h₃

  theorem implication_reversibility {P Q: Prop}: (P → Q) ↔ (¬Q → ¬P) := by
    have h₁: (P → Q) → (¬Q → ¬P) := by
      assume( h₁: P → Q)
      assume (h₁₁: ¬Q)
      have h₁₂: P → False := by
        assume (h₁₂₁: P)
        have h₁₂₂: Q := by modus_ponens h₁, h₁₂₁
        contradiction h₁₂₂, h₁₁
      have h₁₃: ¬P := by reductio_ad_absurdum h₁₂
      implication_intro h₁₁, h₁₃
    have h₂: (¬Q → ¬P) → (P → Q) := by
      assume (h₂₁: ¬Q → ¬P)
      assume (h₂₂: P)
      have h₂₃: ¬Q → False := by
        assume (h₂₃₁: ¬Q)
        have h₂₃₂: ¬P := by modus_ponens h₂₁, h₂₃₁
        contradiction h₂₂, h₂₃₂
      have h₂₄: ¬¬Q := by reductio_ad_absurdum h₂₃
      have h₂₅: Q := by neg_elim h₂₄
      implication_intro h₂₂, h₂₅
    iff_intro h₁, h₂

theorem iff_comm {P Q: Prop}: (P ↔ Q) ↔ (Q ↔ P) := by
  have h₁: (P ↔ Q) → (Q ↔ P) := by
    assume(h₁₁: P ↔ Q)
    have h₁₂: Q → P := by
      assume(h₁₂₁: Q)
      have h₁₂₂: P := deductive_eq_r2l h₁₁ h₁₂₁
      iterate h₁₂₂
    have h₁₃: P → Q := by
      assume(h₁₃₁: P)
      have h₁₃₂: Q := deductive_eq_l2r h₁₁ h₁₃₁
      iterate h₁₃₂
    have h₁₄: Q ↔ P := by iff_intro h₁₂, h₁₃
    iterate h₁₄
  have h₂: (Q ↔ P) → (P ↔ Q) := by
    assume(h₂₁: Q ↔ P)
    have h₁₂: P → Q := by
      assume(h₁₂₁: P)
      have h₁₂₂: Q := deductive_eq_r2l h₂₁ h₁₂₁
      iterate h₁₂₂
    have h₁₃: Q → P := by
      assume(h₁₃₁: Q)
      have h₁₃₂: P := deductive_eq_l2r h₂₁ h₁₃₁
      iterate h₁₃₂
    have h₁₄: P ↔ Q := by iff_intro h₁₂, h₁₃
    iterate h₁₄
  have h₃: (P ↔ Q) ↔ (Q ↔ P) := by iff_intro h₁, h₂
  iterate h₃

theorem iff_contrapositiveness {P Q: Prop}: (P ↔ Q) ↔ (¬P ↔ ¬Q) := by
  have h₁: (P ↔ Q) → (¬P ↔ ¬Q) := by
    assume (h₁₁: P ↔ Q)
    have h₁₁₁: ¬Q → ¬P := by
      have h₁₁₁₁: P → Q := by iff_elim_l2r h₁₁
      have h₁₁₁₂: ¬Q →  ¬P := deductive_eq_l2r implication_reversibility h₁₁₁₁
      iterate h₁₁₁₂
    have h₁₁₂: ¬P → ¬Q := by
      have h₁₁₂₁: Q → P := by iff_elim_r2l h₁₁
      have h₁₁₂₂: ¬P →  ¬Q := deductive_eq_l2r implication_reversibility h₁₁₂₁
      iterate h₁₁₂₂
    iff_intro h₁₁₂, h₁₁₁
  have h₂: (¬P ↔ ¬Q) → (P ↔ Q) := by
    assume (h₂₁: ¬P ↔ ¬Q)
    have h₂₂: (P → Q) := by
      have h₂₂₁: ¬Q → ¬P := by iff_elim_r2l h₂₁
      have h₂₂₂: P → Q := deductive_eq_r2l implication_reversibility h₂₂₁
      iterate h₂₂₂
    have h₂₃: (Q → P) := by
      have h₂₃₁: ¬P → ¬Q := by iff_elim_l2r h₂₁
      have h₂₃₂: Q → P := deductive_eq_r2l implication_reversibility h₂₃₁
      iterate h₂₃₂
    iff_intro h₂₂, h₂₃
  iff_intro h₁, h₂

theorem currying {P Q R: Prop}: (P → (Q → R)) ↔ (P ∧ Q → R) := by
  have h₁: (P → (Q → R)) → (P ∧ Q → R) := by
    assume (h₁₁: P → (Q → R))
    assume (h₁₂: P ∧ Q)
    have h₁₃: P := by and_elim h₁₂
    have h₁₄: Q → R := by modus_ponens h₁₁, h₁₃
    have h₁₅: Q := by and_elim h₁₂
    have h₁₆: R := by modus_ponens h₁₄, h₁₅
    implication_intro h₁₂, h₁₆
  have h₂: (P ∧ Q → R) → (P → (Q → R)) := by
    assume (h₂₁: P ∧ Q → R)
    assume (h₂₂: P)
    have h₂₆: Q → R := by
      assume (h₂₃: Q)
      have h₂₄: P ∧ Q := by and_intro h₂₂, h₂₃
      modus_ponens h₂₁, h₂₄
    implication_intro h₂₂, h₂₆
  iff_intro h₁, h₂

example {P Q R S: Prop} (h₁: P ∧ Q → R) (h₂: (¬P ∧ ¬Q) → S) (h₃: P ↔ Q): R ∨ S := by
  have h₄: P ∨ ¬P := excluded_middle
  have h₅: (P → Q) ∧ (Q → P) := by iff_elim h₃
  have h₆: P → R ∨ S := by
    assume (h₆₁: P)
    have h₆₂: P → Q := by and_elim h₅
    have h₆₃: Q := by modus_ponens h₆₂, h₆₁
    have h₆₄: P ∧ Q := by and_intro h₆₁, h₆₃
    have h₆₅: R := by modus_ponens h₁, h₆₄
    have h₆₆: R ∨ S := by or_intro h₆₅
    iterate h₆₆
  have h₇ : ¬P → R ∨ S := by
    assume (h₇₁: ¬P)
    have h₇₂: Q → P := by and_elim h₅
    have h₇₃: (Q → P) ↔ (¬P → ¬Q) := implication_reversibility
    have h₇₄: ((Q → P) → (¬P → ¬Q)) ∧ ((¬P → ¬Q) → (Q → P)) := by iff_elim h₇₃
    have h₇₅: (Q → P) → (¬P → ¬Q) := by and_elim h₇₄
    have h₇₆: ¬P → ¬Q := by modus_ponens h₇₅, h₇₂
    have h₇₇: ¬Q := by modus_ponens h₇₆, h₇₁
    have h₇₈: ¬P ∧ ¬Q := by and_intro h₇₁, h₇₇
    have h₇₉: S := by modus_ponens h₂, h₇₈
    have h₇₁₀: R ∨ S := by or_intro h₇₉
    iterate h₇₁₀
  or_elimination h₄, h₆, h₇

end PC₀

end Logic
