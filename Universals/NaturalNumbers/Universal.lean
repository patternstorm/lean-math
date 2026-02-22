import Universe
import Logic
import Universals.NaturalNumbers.Particular

/-!
# Natural Numbers — Universal

Bundles the natural number type and its equality into a Universal.
The equality =ₙₐₜ is proved to be an equivalence relation in two phases:
(1) Reflexivity uses only the constructor axioms (zero_refl, succ_cong)
    and eq_refl_induction — no Leibniz equality needed.
(2) Symmetry and transitivity require case analysis on the inner variables
    via exhaustiveness, using Leibniz substitution to convert the resulting
    Leibniz equalities into facts about =ₙₐₜ.
-/

namespace Universe

namespace NaturalNumbers

open Logic
open Logic.PC₁
open Logic.ND

-- # =ₙₐₜ is an equivalence relation

-- ## =ₙₐₜ is reflexive
theorem eq_refl: ∀ (n: ℕ), n =ₙₐₜ n := by
  have h₁: 𝟬 =ₙₐₜ 𝟬 := zero_refl
  have h₂: ∀ (n: ℕ), n =ₙₐₜ n → 𝚜 n =ₙₐₜ 𝚜 n := by forall_intro
    variable(a: ℕ)
    assume(h₂₁: a =ₙₐₜ a)
    have h₂₂: ∀ (m: ℕ), (𝚜 a) =ₙₐₜ (𝚜 m) ↔ a =ₙₐₜ m := by forall_elim succ_cong, a
    have h₂₃: (𝚜 a) =ₙₐₜ (𝚜 a) ↔ a =ₙₐₜ a := by forall_elim h₂₂, a
    have h₂₄: a =ₙₐₜ a → (𝚜 a) =ₙₐₜ (𝚜 a) := by iff_elim_r2l h₂₃
    have h₂₅: 𝚜 a =ₙₐₜ 𝚜 a := by modus_ponens h₂₄, h₂₁
    iterate h₂₅
  have h₃: (𝟬 =ₙₐₜ 𝟬) ∧ ∀ (n: ℕ), n =ₙₐₜ n → 𝚜 n =ₙₐₜ 𝚜 n := by and_intro h₁, h₂
  have h₄: ∀ (n: ℕ), n =ₙₐₜ n := by modus_ponens eq_refl_induction, h₃
  iterate h₄

-- ## =ₙₐₜ is symmetric
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-22
theorem eq_sym: ∀ (n: ℕ), ∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n := by
  -- Base case: ∀ m, 𝟬 =ₙₐₜ m → m =ₙₐₜ 𝟬
  have h₁: ∀ (m: ℕ), 𝟬 =ₙₐₜ m → m =ₙₐₜ 𝟬 := by forall_intro
    variable(b: ℕ)
    have h₁₁: b 🟰 𝟬 ∨ (∃ (k: ℕ), b 🟰 𝚜 k) := by forall_elim exhaustiveness, b
    let pred := (x: ℕ ↦ 𝟬 =ₙₐₜ x → x =ₙₐₜ 𝟬)
    -- Case b 🟰 𝟬: pred 𝟬 = (𝟬 =ₙₐₜ 𝟬 → 𝟬 =ₙₐₜ 𝟬), trivially true
    have h₁₂: b 🟰 𝟬 → pred b := by
      assume(h₁₂₁: b 🟰 𝟬)
      have h₁₂₂: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
      have h₁₂₃: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₁₂₂, b
      have h₁₂₄: b 🟰 𝟬 → (pred b ↔ pred 𝟬) := by forall_elim h₁₂₃, 𝟬
      have h₁₂₅: pred b ↔ pred 𝟬 := by modus_ponens h₁₂₄, h₁₂₁
      have h₁₂₆: 𝟬 =ₙₐₜ 𝟬 → 𝟬 =ₙₐₜ 𝟬 := by
        assume(h₁₂₆₁: 𝟬 =ₙₐₜ 𝟬)
        iterate h₁₂₆₁
      have h₁₂₇: 𝟬 =ₙₐₜ b → b =ₙₐₜ 𝟬 := PC₀.deductive_eq_r2l h₁₂₅ h₁₂₆
      iterate h₁₂₇
    -- Case ∃ k, b 🟰 𝚜 k: pred (𝚜 c) = (𝟬 =ₙₐₜ 𝚜 c → 𝚜 c =ₙₐₜ 𝟬), vacuously true
    have h₁₃: (∃ (k: ℕ), b 🟰 𝚜 k) → pred b := by
      assume(h₁₃₁: ∃ (k: ℕ), b 🟰 𝚜 k)
      have ⟨(c: ℕ), (h₁₃₂: b 🟰 𝚜 c)⟩ := exists_elim h₁₃₁
      have h₁₃₃: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
      have h₁₃₄: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₁₃₃, b
      have h₁₃₅: b 🟰 𝚜 c → (pred b ↔ pred (𝚜 c)) := by forall_elim h₁₃₄, 𝚜 c
      have h₁₃₆: pred b ↔ pred (𝚜 c) := by modus_ponens h₁₃₅, h₁₃₂
      have h₁₃₇: 𝟬 =ₙₐₜ 𝚜 c → 𝚜 c =ₙₐₜ 𝟬 := by
        assume(h₁₃₇₁: 𝟬 =ₙₐₜ 𝚜 c)
        have h₁₃₇₂: ¬(𝟬 =ₙₐₜ 𝚜 c) := by forall_elim zero_is_not_succ, c
        have h₁₃₇₃: 𝚜 c =ₙₐₜ 𝟬 := by contradiction h₁₃₇₁, h₁₃₇₂
        iterate h₁₃₇₃
      have h₁₃₈: pred b := PC₀.deductive_eq_r2l h₁₃₆ h₁₃₇
      iterate h₁₃₈
    have h₁₄: pred b := by or_elimination h₁₁, h₁₂, h₁₃
    iterate h₁₄
  -- Inductive step: ∀ n, (∀ m, n =ₙₐₜ m → m =ₙₐₜ n) → (∀ m, 𝚜 n =ₙₐₜ m → m =ₙₐₜ 𝚜 n)
  have h₂: ∀ (n: ℕ), (∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n) → (∀ (m: ℕ), (𝚜 n) =ₙₐₜ m → m =ₙₐₜ (𝚜 n)) := by forall_intro
    variable(a: ℕ)
    assume(h₂₁: ∀ (m: ℕ), a =ₙₐₜ m → m =ₙₐₜ a)
    have h₂₂: ∀ (m: ℕ), (𝚜 a) =ₙₐₜ m → m =ₙₐₜ (𝚜 a) := by forall_intro
      variable(b: ℕ)
      have h₂₂₁: b 🟰 𝟬 ∨ (∃ (k: ℕ), b 🟰 𝚜 k) := by forall_elim exhaustiveness, b
      let pred := (x: ℕ ↦ (𝚜 a) =ₙₐₜ x → x =ₙₐₜ (𝚜 a))
      -- Case b 🟰 𝟬: pred 𝟬 = (𝚜 a =ₙₐₜ 𝟬 → 𝟬 =ₙₐₜ 𝚜 a), vacuously true
      have h₂₂₂: b 🟰 𝟬 → pred b := by
        assume(h₂₂₂₁: b 🟰 𝟬)
        have h₂₂₂₂: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
        have h₂₂₂₃: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₂₂₂₂, b
        have h₂₂₂₄: b 🟰 𝟬 → (pred b ↔ pred 𝟬) := by forall_elim h₂₂₂₃, 𝟬
        have h₂₂₂₅: pred b ↔ pred 𝟬 := by modus_ponens h₂₂₂₄, h₂₂₂₁
        have h₂₂₂₆: (𝚜 a) =ₙₐₜ 𝟬 → 𝟬 =ₙₐₜ (𝚜 a) := by
          assume(h₂₂₂₆₁: (𝚜 a) =ₙₐₜ 𝟬)
          have h₂₂₂₆₂: ¬((𝚜 a) =ₙₐₜ 𝟬) := by forall_elim succ_is_not_zero, a
          have h₂₂₂₆₃: 𝟬 =ₙₐₜ (𝚜 a) := by contradiction h₂₂₂₆₁, h₂₂₂₆₂
          iterate h₂₂₂₆₃
        have h₂₂₂₇: pred b := PC₀.deductive_eq_r2l h₂₂₂₅ h₂₂₂₆
        iterate h₂₂₂₇
      -- Case ∃ k, b 🟰 𝚜 k: use succ_cong (both directions) + IH
      have h₂₂₃: (∃ (k: ℕ), b 🟰 𝚜 k) → pred b := by
        assume(h₂₂₃₁: ∃ (k: ℕ), b 🟰 𝚜 k)
        have ⟨(c: ℕ), (h₂₂₃₂: b 🟰 𝚜 c)⟩ := exists_elim h₂₂₃₁
        have h₂₂₃₃: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
        have h₂₂₃₄: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₂₂₃₃, b
        have h₂₂₃₅: b 🟰 𝚜 c → (pred b ↔ pred (𝚜 c)) := by forall_elim h₂₂₃₄, 𝚜 c
        have h₂₂₃₆: pred b ↔ pred (𝚜 c) := by modus_ponens h₂₂₃₅, h₂₂₃₂
        -- pred (𝚜 c) = ((𝚜 a) =ₙₐₜ 𝚜 c → 𝚜 c =ₙₐₜ (𝚜 a))
        -- From 𝚜 a =ₙₐₜ 𝚜 c, by succ_cong (l→r): a =ₙₐₜ c, by IH: c =ₙₐₜ a, by succ_cong (r→l): 𝚜 c =ₙₐₜ 𝚜 a
        have h₂₂₃₇: (𝚜 a) =ₙₐₜ 𝚜 c → 𝚜 c =ₙₐₜ (𝚜 a) := by
          assume(h₂₂₃₇₁: (𝚜 a) =ₙₐₜ 𝚜 c)
          have h₂₂₃₇₂: ∀ (m: ℕ), (𝚜 a) =ₙₐₜ (𝚜 m) ↔ a =ₙₐₜ m := by forall_elim succ_cong, a
          have h₂₂₃₇₃: (𝚜 a) =ₙₐₜ (𝚜 c) ↔ a =ₙₐₜ c := by forall_elim h₂₂₃₇₂, c
          have h₂₂₃₇₄: a =ₙₐₜ c := PC₀.deductive_eq_l2r h₂₂₃₇₃ h₂₂₃₇₁
          have h₂₂₃₇₅: a =ₙₐₜ c → c =ₙₐₜ a := by forall_elim h₂₁, c
          have h₂₂₃₇₆: c =ₙₐₜ a := by modus_ponens h₂₂₃₇₅, h₂₂₃₇₄
          have h₂₂₃₇₇: ∀ (m: ℕ), (𝚜 c) =ₙₐₜ (𝚜 m) ↔ c =ₙₐₜ m := by forall_elim succ_cong, c
          have h₂₂₃₇₈: (𝚜 c) =ₙₐₜ (𝚜 a) ↔ c =ₙₐₜ a := by forall_elim h₂₂₃₇₇, a
          have h₂₂₃₇₉: 𝚜 c =ₙₐₜ 𝚜 a := PC₀.deductive_eq_r2l h₂₂₃₇₈ h₂₂₃₇₆
          iterate h₂₂₃₇₉
        have h₂₂₃₈: pred b := PC₀.deductive_eq_r2l h₂₂₃₆ h₂₂₃₇
        iterate h₂₂₃₈
      have h₂₂₄: pred b := by or_elimination h₂₂₁, h₂₂₂, h₂₂₃
      iterate h₂₂₄
    iterate h₂₂
  have h₃: (∀ (m: ℕ), 𝟬 =ₙₐₜ m → m =ₙₐₜ 𝟬) ∧
      (∀ (n: ℕ), (∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n) →
          (∀ (m: ℕ), (𝚜 n) =ₙₐₜ m → m =ₙₐₜ (𝚜 n))) := by and_intro h₁, h₂
  have h₄: ∀ (n: ℕ), ∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n := by modus_ponens eq_sym_induction, h₃
  iterate h₄

-- ## =ₙₐₜ is transitive
-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-22
theorem eq_trans: ∀ (n: ℕ), ∀ (m: ℕ), ∀ (p: ℕ), n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p := by
  -- Base case: ∀ m p, 𝟬 =ₙₐₜ m ∧ m =ₙₐₜ p → 𝟬 =ₙₐₜ p
  have h₁: ∀ (m: ℕ), ∀ (p: ℕ), 𝟬 =ₙₐₜ m ∧ m =ₙₐₜ p → 𝟬 =ₙₐₜ p := by forall_intro
    variable(b: ℕ)
    variable(c: ℕ)
    have h₁₁: b 🟰 𝟬 ∨ (∃ (k: ℕ), b 🟰 𝚜 k) := by forall_elim exhaustiveness, b
    let pred := (x: ℕ ↦ 𝟬 =ₙₐₜ x ∧ x =ₙₐₜ c → 𝟬 =ₙₐₜ c)
    -- Case b 🟰 𝟬: pred 𝟬 = (𝟬 =ₙₐₜ 𝟬 ∧ 𝟬 =ₙₐₜ c → 𝟬 =ₙₐₜ c), trivially true
    have h₁₂: b 🟰 𝟬 → pred b := by
      assume(h₁₂₁: b 🟰 𝟬)
      have h₁₂₂: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
      have h₁₂₃: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₁₂₂, b
      have h₁₂₄: b 🟰 𝟬 → (pred b ↔ pred 𝟬) := by forall_elim h₁₂₃, 𝟬
      have h₁₂₅: pred b ↔ pred 𝟬 := by modus_ponens h₁₂₄, h₁₂₁
      have h₁₂₆: 𝟬 =ₙₐₜ 𝟬 ∧ 𝟬 =ₙₐₜ c → 𝟬 =ₙₐₜ c := by
        assume(h₁₂₆₁: 𝟬 =ₙₐₜ 𝟬 ∧ 𝟬 =ₙₐₜ c)
        have h₁₂₆₂: 𝟬 =ₙₐₜ c := by and_elim h₁₂₆₁
        iterate h₁₂₆₂
      have h₁₂₇: pred b := PC₀.deductive_eq_r2l h₁₂₅ h₁₂₆
      iterate h₁₂₇
    -- Case b 🟰 𝚜 d: vacuously true via zero_is_not_succ
    have h₁₃: (∃ (k: ℕ), b 🟰 𝚜 k) → pred b := by
      assume(h₁₃₁: ∃ (k: ℕ), b 🟰 𝚜 k)
      have ⟨(d: ℕ), (h₁₃₂: b 🟰 𝚜 d)⟩ := exists_elim h₁₃₁
      have h₁₃₃: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
      have h₁₃₄: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₁₃₃, b
      have h₁₃₅: b 🟰 𝚜 d → (pred b ↔ pred (𝚜 d)) := by forall_elim h₁₃₄, 𝚜 d
      have h₁₃₆: pred b ↔ pred (𝚜 d) := by modus_ponens h₁₃₅, h₁₃₂
      have h₁₃₇: 𝟬 =ₙₐₜ 𝚜 d ∧ 𝚜 d =ₙₐₜ c → 𝟬 =ₙₐₜ c := by
        assume(h₁₃₇₁: 𝟬 =ₙₐₜ 𝚜 d ∧ 𝚜 d =ₙₐₜ c)
        have h₁₃₇₂: 𝟬 =ₙₐₜ 𝚜 d := by and_elim h₁₃₇₁
        have h₁₃₇₃: ¬(𝟬 =ₙₐₜ 𝚜 d) := by forall_elim zero_is_not_succ, d
        have h₁₃₇₄: 𝟬 =ₙₐₜ c := by contradiction h₁₃₇₂, h₁₃₇₃
        iterate h₁₃₇₄
      have h₁₃₈: pred b := PC₀.deductive_eq_r2l h₁₃₆ h₁₃₇
      iterate h₁₃₈
    have h₁₄: pred b := by or_elimination h₁₁, h₁₂, h₁₃
    iterate h₁₄
  -- Inductive step
  have h₂: ∀ (n: ℕ), (∀ (m: ℕ), ∀ (p: ℕ), n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p) →
      (∀ (m: ℕ), ∀ (p: ℕ), (𝚜 n) =ₙₐₜ m ∧ m =ₙₐₜ p → (𝚜 n) =ₙₐₜ p) := by forall_intro
    variable(a: ℕ)
    assume(h₂₁: ∀ (m: ℕ), ∀ (p: ℕ), a =ₙₐₜ m ∧ m =ₙₐₜ p → a =ₙₐₜ p)
    have h₂₂: ∀ (m: ℕ), ∀ (p: ℕ), (𝚜 a) =ₙₐₜ m ∧ m =ₙₐₜ p → (𝚜 a) =ₙₐₜ p := by forall_intro
      variable(b: ℕ)
      variable(c: ℕ)
      have h₂₂₁: b 🟰 𝟬 ∨ (∃ (k: ℕ), b 🟰 𝚜 k) := by forall_elim exhaustiveness, b
      let pred := (x: ℕ ↦ (𝚜 a) =ₙₐₜ x ∧ x =ₙₐₜ c → (𝚜 a) =ₙₐₜ c)
      -- Case b 🟰 𝟬: vacuously true via succ_is_not_zero
      have h₂₂₂: b 🟰 𝟬 → pred b := by
        assume(h₂₂₂₁: b 🟰 𝟬)
        have h₂₂₂₂: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
        have h₂₂₂₃: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₂₂₂₂, b
        have h₂₂₂₄: b 🟰 𝟬 → (pred b ↔ pred 𝟬) := by forall_elim h₂₂₂₃, 𝟬
        have h₂₂₂₅: pred b ↔ pred 𝟬 := by modus_ponens h₂₂₂₄, h₂₂₂₁
        have h₂₂₂₆: (𝚜 a) =ₙₐₜ 𝟬 ∧ 𝟬 =ₙₐₜ c → (𝚜 a) =ₙₐₜ c := by
          assume(h₂₂₂₆₁: (𝚜 a) =ₙₐₜ 𝟬 ∧ 𝟬 =ₙₐₜ c)
          have h₂₂₂₆₂: (𝚜 a) =ₙₐₜ 𝟬 := by and_elim h₂₂₂₆₁
          have h₂₂₂₆₃: ¬((𝚜 a) =ₙₐₜ 𝟬) := by forall_elim succ_is_not_zero, a
          have h₂₂₂₆₄: (𝚜 a) =ₙₐₜ c := by contradiction h₂₂₂₆₂, h₂₂₂₆₃
          iterate h₂₂₂₆₄
        have h₂₂₂₇: pred b := PC₀.deductive_eq_r2l h₂₂₂₅ h₂₂₂₆
        iterate h₂₂₂₇
      -- Case b 🟰 𝚜 d: succ_cong + case analysis on c + IH
      have h₂₂₃: (∃ (k: ℕ), b 🟰 𝚜 k) → pred b := by
        assume(h₂₂₃₁: ∃ (k: ℕ), b 🟰 𝚜 k)
        have ⟨(d: ℕ), (h₂₂₃₂: b 🟰 𝚜 d)⟩ := exists_elim h₂₂₃₁
        have h₂₂₃₃: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
        have h₂₂₃₄: ∀ (y: ℕ), b 🟰 y → (pred b ↔ pred y) := by forall_elim h₂₂₃₃, b
        have h₂₂₃₅: b 🟰 𝚜 d → (pred b ↔ pred (𝚜 d)) := by forall_elim h₂₂₃₄, 𝚜 d
        have h₂₂₃₆: pred b ↔ pred (𝚜 d) := by modus_ponens h₂₂₃₅, h₂₂₃₂
        -- pred (𝚜 d) = ((𝚜 a) =ₙₐₜ 𝚜 d ∧ 𝚜 d =ₙₐₜ c → (𝚜 a) =ₙₐₜ c)
        have h₂₂₃₇: (𝚜 a) =ₙₐₜ 𝚜 d ∧ 𝚜 d =ₙₐₜ c → (𝚜 a) =ₙₐₜ c := by
          assume(h₂₂₃₇₁: (𝚜 a) =ₙₐₜ 𝚜 d ∧ 𝚜 d =ₙₐₜ c)
          have h₂₂₃₇₂: (𝚜 a) =ₙₐₜ 𝚜 d := by and_elim h₂₂₃₇₁
          have h₂₂₃₇₃: 𝚜 d =ₙₐₜ c := by and_elim h₂₂₃₇₁
          -- Extract a =ₙₐₜ d via succ_cong (l→r)
          have h₂₂₃₇₄: ∀ (m: ℕ), (𝚜 a) =ₙₐₜ (𝚜 m) ↔ a =ₙₐₜ m := by forall_elim succ_cong, a
          have h₂₂₃₇₅: (𝚜 a) =ₙₐₜ (𝚜 d) ↔ a =ₙₐₜ d := by forall_elim h₂₂₃₇₄, d
          have h₂₂₃₇₆: a =ₙₐₜ d := PC₀.deductive_eq_l2r h₂₂₃₇₅ h₂₂₃₇₂
          -- Case analysis on c
          have h₂₂₃₇₇: c 🟰 𝟬 ∨ (∃ (k: ℕ), c 🟰 𝚜 k) := by forall_elim exhaustiveness, c
          let pred₂ := (x: ℕ ↦ 𝚜 d =ₙₐₜ x → (𝚜 a) =ₙₐₜ x)
          -- Case c 🟰 𝟬: vacuously true via succ_is_not_zero
          have h₂₂₃₇₈: c 🟰 𝟬 → pred₂ c := by
            assume(h₂₂₃₇₈₁: c 🟰 𝟬)
            have h₂₂₃₇₈₂: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
            have h₂₂₃₇₈₃: ∀ (y: ℕ), c 🟰 y → (pred₂ c ↔ pred₂ y) := by forall_elim h₂₂₃₇₈₂, c
            have h₂₂₃₇₈₄: c 🟰 𝟬 → (pred₂ c ↔ pred₂ 𝟬) := by forall_elim h₂₂₃₇₈₃, 𝟬
            have h₂₂₃₇₈₅: pred₂ c ↔ pred₂ 𝟬 := by modus_ponens h₂₂₃₇₈₄, h₂₂₃₇₈₁
            have h₂₂₃₇₈₆: 𝚜 d =ₙₐₜ 𝟬 → (𝚜 a) =ₙₐₜ 𝟬 := by
              assume(h₂₂₃₇₈₆₁: 𝚜 d =ₙₐₜ 𝟬)
              have h₂₂₃₇₈₆₂: ¬(𝚜 d =ₙₐₜ 𝟬) := by forall_elim succ_is_not_zero, d
              have h₂₂₃₇₈₆₃: (𝚜 a) =ₙₐₜ 𝟬 := by contradiction h₂₂₃₇₈₆₁, h₂₂₃₇₈₆₂
              iterate h₂₂₃₇₈₆₃
            have h₂₂₃₇₈₇: pred₂ c := PC₀.deductive_eq_r2l h₂₂₃₇₈₅ h₂₂₃₇₈₆
            iterate h₂₂₃₇₈₇
          -- Case c 🟰 𝚜 e: succ_cong (both directions) + IH
          have h₂₂₃₇₉: (∃ (k: ℕ), c 🟰 𝚜 k) → pred₂ c := by
            assume(h₂₂₃₇₉₁: ∃ (k: ℕ), c 🟰 𝚜 k)
            have ⟨(e: ℕ), (h₂₂₃₇₉₂: c 🟰 𝚜 e)⟩ := exists_elim h₂₂₃₇₉₁
            have h₂₂₃₇₉₃: ∀ (x: ℕ), ∀ (y: ℕ), x 🟰 y → (pred₂ x ↔ pred₂ y) := by forall_elim leibniz_eq_subs, pred₂
            have h₂₂₃₇₉₄: ∀ (y: ℕ), c 🟰 y → (pred₂ c ↔ pred₂ y) := by forall_elim h₂₂₃₇₉₃, c
            have h₂₂₃₇₉₅: c 🟰 𝚜 e → (pred₂ c ↔ pred₂ (𝚜 e)) := by forall_elim h₂₂₃₇₉₄, 𝚜 e
            have h₂₂₃₇₉₆: pred₂ c ↔ pred₂ (𝚜 e) := by modus_ponens h₂₂₃₇₉₅, h₂₂₃₇₉₂
            -- pred₂ (𝚜 e) = (𝚜 d =ₙₐₜ 𝚜 e → 𝚜 a =ₙₐₜ 𝚜 e)
            -- From 𝚜 d =ₙₐₜ 𝚜 e, succ_cong (l→r): d =ₙₐₜ e. IH with (d, e): a =ₙₐₜ e. succ_cong (r→l): 𝚜 a =ₙₐₜ 𝚜 e.
            have h₂₂₃₇₉₇: 𝚜 d =ₙₐₜ 𝚜 e → (𝚜 a) =ₙₐₜ 𝚜 e := by
              assume(h₂₂₃₇₉₇₁: 𝚜 d =ₙₐₜ 𝚜 e)
              have h₂₂₃₇₉₇₂: ∀ (m: ℕ), (𝚜 d) =ₙₐₜ (𝚜 m) ↔ d =ₙₐₜ m := by forall_elim succ_cong, d
              have h₂₂₃₇₉₇₃: (𝚜 d) =ₙₐₜ (𝚜 e) ↔ d =ₙₐₜ e := by forall_elim h₂₂₃₇₉₇₂, e
              have h₂₂₃₇₉₇₄: d =ₙₐₜ e := PC₀.deductive_eq_l2r h₂₂₃₇₉₇₃ h₂₂₃₇₉₇₁
              have h₂₂₃₇₉₇₅: ∀ (p: ℕ), a =ₙₐₜ d ∧ d =ₙₐₜ p → a =ₙₐₜ p := by forall_elim h₂₁, d
              have h₂₂₃₇₉₇₆: a =ₙₐₜ d ∧ d =ₙₐₜ e → a =ₙₐₜ e := by forall_elim h₂₂₃₇₉₇₅, e
              have h₂₂₃₇₉₇₇: a =ₙₐₜ d ∧ d =ₙₐₜ e := by and_intro h₂₂₃₇₆, h₂₂₃₇₉₇₄
              have h₂₂₃₇₉₇₈: a =ₙₐₜ e := by modus_ponens h₂₂₃₇₉₇₆, h₂₂₃₇₉₇₇
              have h₂₂₃₇₉₇₉: (𝚜 a) =ₙₐₜ (𝚜 e) ↔ a =ₙₐₜ e := by forall_elim h₂₂₃₇₄, e
              have h₂₂₃₇₉₇₁₀: (𝚜 a) =ₙₐₜ 𝚜 e := PC₀.deductive_eq_r2l h₂₂₃₇₉₇₉ h₂₂₃₇₉₇₈
              iterate h₂₂₃₇₉₇₁₀
            have h₂₂₃₇₉₈: pred₂ c := PC₀.deductive_eq_r2l h₂₂₃₇₉₆ h₂₂₃₇₉₇
            iterate h₂₂₃₇₉₈
          have h₂₂₃₇₁₀: pred₂ c := by or_elimination h₂₂₃₇₇, h₂₂₃₇₈, h₂₂₃₇₉
          have h₂₂₃₇₁₁: (𝚜 a) =ₙₐₜ c := by modus_ponens h₂₂₃₇₁₀, h₂₂₃₇₃
          iterate h₂₂₃₇₁₁
        have h₂₂₃₈: pred b := PC₀.deductive_eq_r2l h₂₂₃₆ h₂₂₃₇
        iterate h₂₂₃₈
      have h₂₂₄: pred b := by or_elimination h₂₂₁, h₂₂₂, h₂₂₃
      iterate h₂₂₄
    iterate h₂₂
  have h₃: (∀ (m: ℕ), ∀ (p: ℕ), 𝟬 =ₙₐₜ m ∧ m =ₙₐₜ p → 𝟬 =ₙₐₜ p) ∧
      (∀ (n: ℕ), (∀ (m: ℕ), ∀ (p: ℕ), n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p) →
          (∀ (m: ℕ), ∀ (p: ℕ), (𝚜 n) =ₙₐₜ m ∧ m =ₙₐₜ p → (𝚜 n) =ₙₐₜ p)) := by and_intro h₁, h₂
  have h₄: ∀ (n: ℕ), ∀ (m: ℕ), ∀ (p: ℕ), n =ₙₐₜ m ∧ m =ₙₐₜ p → n =ₙₐₜ p := by modus_ponens eq_trans_induction, h₃
  iterate h₄

-- # =ₙₐₜ Equality
def equality: Equality ℕ :=
  let pred: ℕ → ℕ → Prop := eq
  let refl: ∀ (x: ℕ), pred x x := eq_refl
  let sym: ∀ (x: ℕ), ∀ (y: ℕ), pred x y → pred y x := eq_sym
  let trans: ∀ (x: ℕ), ∀ (y: ℕ), ∀ (z: ℕ), pred x y ∧ pred y z → pred x z := eq_trans
  { pred := pred, refl := refl, sym := sym, trans := trans }

-- # Natural Numbers Universal
def NaturalNumbersUniversal: Universal := {
  Particular := ℕ
  eq := equality
}
notation "𝐍𝐚𝐭" => NaturalNumbersUniversal

end NaturalNumbers

end Universe
