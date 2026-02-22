import Universe
import Logic
import Universals.Sets
import Universals.NaturalNumbers.Universal

open Universe
open Sets
open Logic
open Logic.PC₁
open Logic.ND


-- # Natural Numbers induction
axiom induction : ∀ (S : Set 𝐍𝐚𝐭),
    ((𝟬 ∈ₛₑₜ S) ∧
    (∀ (n: ℕ), n ∈ₛₑₜ S → (𝚜 n) ∈ₛₑₜ S)) →
    (∀ (n: ℕ), n ∈ₛₑₜ S)

-- # Natural Numbers operations

-- ## Addition
axiom add : ℕ → ℕ → ℕ
notation "(" n "+ₙₐₜ" m ")" => add n m

axiom add_zero_def : ∀ (n: ℕ), (𝟬 +ₙₐₜ n) =ₙₐₜ n
axiom add_succ_def : ∀ (n: ℕ), ∀ (m: ℕ), (𝚜 n +ₙₐₜ m) =ₙₐₜ 𝚜 (n +ₙₐₜ m)

-- ## Addition congruence
axiom add_cong_right: ∀ (n: ℕ), ∀ (n₁: ℕ), ∀ (n₂: ℕ), (n₁ =ₙₐₜ n₂) → (n +ₙₐₜ n₁) =ₙₐₜ (n +ₙₐₜ n₂)
axiom add_cong_left: ∀ (n: ℕ), ∀ (n₁: ℕ), ∀ (n₂: ℕ), (n₁ =ₙₐₜ n₂) → (n₁ +ₙₐₜ n) =ₙₐₜ (n₂ +ₙₐₜ n)

-- # Theorems

-- ## Addition properties

theorem add_zero_right: ∀ (n: ℕ), (n +ₙₐₜ 𝟬) =ₙₐₜ n := by
  have h₁: ∀ (n: ℕ), (n +ₙₐₜ 𝟬) =ₙₐₜ n := by forall_intro
    let A: Set 𝐍𝐚𝐭 := { n: ℕ | (n +ₙₐₜ 𝟬) =ₙₐₜ n }
    variable (a: ℕ)
    have h₁₁: 𝟬 ∈ₛₑₜ A := by
      have h₁₁₁: (𝟬 +ₙₐₜ 𝟬) =ₙₐₜ 𝟬 := by forall_elim add_zero_def, 𝟬
      have h₁₁₂: ∀ (n: ℕ), n ∈ₛₑₜ A ↔ A n := by forall_elim Sets.mem_def, A
      have h₁₁₃: 𝟬 ∈ₛₑₜ A ↔ A 𝟬 := by forall_elim h₁₁₂, 𝟬
      have h₁₁₄: 𝟬 ∈ₛₑₜ A := pc₀.deductive_eq_r2l h₁₁₃ h₁₁₁
      iterate h₁₁₄
    have h₁₂: ∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A := by forall_intro
      variable (a: ℕ)
      assume(h₁₂₁: a ∈ₛₑₜ A)
      have h₁₂₂: ∀ (n: ℕ), n ∈ₛₑₜ A ↔ A n := by forall_elim Sets.mem_def, A
      have h₁₂₃: a ∈ₛₑₜ A ↔ A a := by forall_elim h₁₂₂, a
      have h₁₂₄: (a +ₙₐₜ 𝟬) =ₙₐₜ a := pc₀.deductive_eq_l2r h₁₂₃ h₁₂₁
      have h₁₂₅: (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ (𝚜 a) := by
        have h₁₂₅₁: (∀ (n: ℕ), ∀ (m: ℕ), (𝚜 n +ₙₐₜ m) =ₙₐₜ 𝚜 (n +ₙₐₜ m)) ↔ (∀ (m: ℕ), ∀ (n: ℕ), (𝚜 n +ₙₐₜ m) =ₙₐₜ 𝚜 (n +ₙₐₜ m)) := pc₁.forall_comm
        have h₁₂₅₂: ∀ (m: ℕ), ∀ (n: ℕ), (𝚜 n +ₙₐₜ m) =ₙₐₜ 𝚜 (n +ₙₐₜ m) := pc₀.deductive_eq_l2r h₁₂₅₁ add_succ_def
        have h₁₂₅₃: ∀ (n: ℕ), (𝚜 n +ₙₐₜ 𝟬) =ₙₐₜ 𝚜 (n +ₙₐₜ 𝟬) := by forall_elim h₁₂₅₂, 𝟬
        have h₁₂₅₄: (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ 𝚜 (a +ₙₐₜ 𝟬) := by forall_elim h₁₂₅₃, a
        have h₁₂₅₅: 𝚜 (a +ₙₐₜ 𝟬) =ₙₐₜ 𝚜 a := by
          have h₁₂₅₅₁: ∀ (m: ℕ), ((a +ₙₐₜ 𝟬) =ₙₐₜ m) → (𝚜 (a +ₙₐₜ 𝟬)) =ₙₐₜ (𝚜 m) := by forall_elim succ_cong, (a +ₙₐₜ 𝟬)
          have h₁₂₅₅₂: ((a +ₙₐₜ 𝟬) =ₙₐₜ a) → (𝚜 (a +ₙₐₜ 𝟬)) =ₙₐₜ (𝚜 a) := by forall_elim h₁₂₅₅₁, a
          modus_ponens h₁₂₅₅₂, h₁₂₄
        have h₁₂₅₆: (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ (𝚜 a) := by
          have h₁₂₅₆₁: ∀ (n₂: ℕ), ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ n₃ := by forall_elim eq_trans, (𝚜 a +ₙₐₜ 𝟬)
          have h₁₂₅₆₂: ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ (𝚜 (a +ₙₐₜ 𝟬)) ∧ (𝚜 (a +ₙₐₜ 𝟬)) =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ n₃ := by forall_elim h₁₂₅₆₁, (𝚜 (a +ₙₐₜ 𝟬))
          have h₁₂₅₆₃: (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ (𝚜 (a +ₙₐₜ 𝟬)) ∧ (𝚜 (a +ₙₐₜ 𝟬)) =ₙₐₜ (𝚜 a) → (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ (𝚜 a) := by forall_elim h₁₂₅₆₂, (𝚜 a)
          have h₁₂₅₆₄: (𝚜 a +ₙₐₜ 𝟬) =ₙₐₜ (𝚜 (a +ₙₐₜ 𝟬)) ∧ (𝚜 (a +ₙₐₜ 𝟬)) =ₙₐₜ (𝚜 a) := by and_intro h₁₂₅₄, h₁₂₅₅
          modus_ponens h₁₂₅₆₃, h₁₂₅₆₄
        iterate h₁₂₅₆
      have h₁₂₆: (𝚜 a) ∈ₛₑₜ A ↔ A (𝚜 a) := by forall_elim h₁₂₂, 𝚜 a
      have h₁₂₇: (𝚜 a) ∈ₛₑₜ A := pc₀.deductive_eq_r2l h₁₂₆ h₁₂₅
      iterate h₁₂₇
    have h₁₃: (𝟬 ∈ₛₑₜ A) ∧ (∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A) := by and_intro h₁₁, h₁₂
    have h₁₄: (𝟬 ∈ₛₑₜ A) ∧ (∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A) → (∀ (n: ℕ), n ∈ₛₑₜ A) := by forall_elim induction, A
    have h₁₅: ∀ (n: ℕ), n ∈ₛₑₜ A := by modus_ponens h₁₄, h₁₃
    have h₁₆: a ∈ₛₑₜ A := by forall_elim h₁₅, a
    have h₁₇: ∀ (n: ℕ), n ∈ₛₑₜ A ↔ A n := by forall_elim Sets.mem_def, A
    have h₁₈: a ∈ₛₑₜ A ↔ A a := by forall_elim h₁₇, a
    have h₁₉: (a +ₙₐₜ 𝟬) =ₙₐₜ a := pc₀.deductive_eq_l2r h₁₈ h₁₆
    iterate h₁₉
  iterate h₁

theorem add_suc_right: ∀ (n: ℕ), ∀ (m: ℕ), (n +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (n +ₙₐₜ m) := by
  let A := { n: ℕ | ∀ (m : ℕ), (n +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (n +ₙₐₜ m) }
  have h₀: ∀ (n: ℕ), n ∈ₛₑₜ A ↔ A n := by forall_elim Sets.mem_def, A
  have h₁: 𝟬 ∈ₛₑₜ A := by
    have h₁₁: ∀ (m: ℕ), (𝟬 +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 m := by forall_intro
      variable(a: ℕ)
      have h₁₁₁: (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ 𝚜 a := by forall_elim add_zero_def, (𝚜 a)
      iterate h₁₁₁
    have h₁₂: ∀ (m: ℕ), 𝚜 (𝟬 +ₙₐₜ m) =ₙₐₜ 𝚜 m := by forall_intro
      variable(a: ℕ)
      have h₁₂₁: (𝟬 +ₙₐₜ a) =ₙₐₜ a := by forall_elim add_zero_def, a
      have h₁₂₂: ∀ (m: ℕ), (𝟬 +ₙₐₜ a) =ₙₐₜ m → 𝚜 (𝟬 +ₙₐₜ a) =ₙₐₜ 𝚜 m := by forall_elim succ_cong, (𝟬 +ₙₐₜ a)
      have h₁₂₃: (𝟬 +ₙₐₜ a) =ₙₐₜ a → 𝚜 (𝟬 +ₙₐₜ a) =ₙₐₜ 𝚜 a := by forall_elim h₁₂₂, a
      modus_ponens h₁₂₃, h₁₂₁
    have h₁₃: ∀ (m: ℕ), (𝟬 +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (𝟬 +ₙₐₜ m) := by forall_intro
      variable(a: ℕ)
      have h₁₃₁: (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ 𝚜 a := by forall_elim h₁₁, a
      have h₁₃₂: 𝚜 (𝟬 +ₙₐₜ a) =ₙₐₜ 𝚜 a := by forall_elim h₁₂, a
      have h₁₃₃: ∀ (m: ℕ), (𝚜 (𝟬 +ₙₐₜ a)) =ₙₐₜ m → m =ₙₐₜ 𝚜 (𝟬 +ₙₐₜ a) := by forall_elim eq_sym, (𝚜 (𝟬 +ₙₐₜ a))
      have h₁₃₄: (𝚜 (𝟬 +ₙₐₜ a)) =ₙₐₜ 𝚜 a → 𝚜 a =ₙₐₜ 𝚜 (𝟬 +ₙₐₜ a) := by forall_elim h₁₃₃, (𝚜 a)
      have h₁₃₅: 𝚜 a =ₙₐₜ 𝚜 (𝟬 +ₙₐₜ a) := by modus_ponens h₁₃₄, h₁₃₂
      have h₁₃₆: ∀ (n₂: ℕ), ∀ (n₃: ℕ), (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ n₃ := by forall_elim eq_trans, (𝟬 +ₙₐₜ 𝚜 a)
      have h₁₃₇: ∀ (n₃: ℕ), (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ (𝚜 a) ∧ (𝚜 a) =ₙₐₜ n₃ → (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ n₃ := by forall_elim h₁₃₆, (𝚜 a)
      have h₁₃₈: (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ (𝚜 a) ∧ (𝚜 a) =ₙₐₜ (𝚜 (𝟬 +ₙₐₜ a)) → (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ (𝚜 (𝟬 +ₙₐₜ a)) := by forall_elim h₁₃₇, (𝚜 (𝟬 +ₙₐₜ a))
      have h₁₃₉: (𝟬 +ₙₐₜ 𝚜 a) =ₙₐₜ (𝚜 a) ∧ (𝚜 a) =ₙₐₜ (𝚜 (𝟬 +ₙₐₜ a)) := by and_intro h₁₃₁, h₁₃₅
      modus_ponens h₁₃₈, h₁₃₉
    have h₁₄: 𝟬 ∈ₛₑₜ A ↔ A 𝟬 := by forall_elim h₀, 𝟬
    have h₁₅: 𝟬 ∈ₛₑₜ A := pc₀.deductive_eq_r2l h₁₄ h₁₃
    iterate h₁₅
  have h₂: ∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A := by forall_intro
    variable(a: ℕ)
    assume(h₂₁: a ∈ₛₑₜ A)
    have h₂₂: a ∈ₛₑₜ A ↔ A a := by forall_elim h₀, a
    have h₂₃: ∀ (m: ℕ), (a +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (a +ₙₐₜ m) := pc₀.deductive_eq_l2r h₂₂ h₂₁
    have h₂₄: ∀ (m: ℕ), (𝚜 a +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (𝚜 a +ₙₐₜ m) := by forall_intro
      variable(b: ℕ)
      have h₂₄₁: (a +ₙₐₜ 𝚜 b) =ₙₐₜ 𝚜 (a +ₙₐₜ b) := by forall_elim h₂₃, b
      have h₂₄₂: ∀ (m: ℕ), (𝚜 a +ₙₐₜ m) =ₙₐₜ 𝚜 (a +ₙₐₜ m) := by forall_elim add_succ_def, a
      have h₂₄₃: (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ 𝚜 (a +ₙₐₜ 𝚜 b) := by forall_elim h₂₄₂, (𝚜 b)
      have h₂₄₄: ∀ (m: ℕ), (𝚜 a +ₙₐₜ m) =ₙₐₜ 𝚜 (a +ₙₐₜ m) := by forall_elim add_succ_def, a
      have h₂₄₅: (𝚜 a +ₙₐₜ b) =ₙₐₜ 𝚜 (a +ₙₐₜ b) := by forall_elim h₂₄₄, b
      have h₂₄₆: ∀ (m: ℕ), (𝚜 a +ₙₐₜ b) =ₙₐₜ m → m =ₙₐₜ (𝚜 a +ₙₐₜ b) := by forall_elim eq_sym, (𝚜 a +ₙₐₜ b)
      have h₂₄₇: (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (a +ₙₐₜ b)) → (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 a +ₙₐₜ b) := by forall_elim h₂₄₆, (𝚜 (a +ₙₐₜ b))
      have h₂₄₈: (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 a +ₙₐₜ b) := by modus_ponens h₂₄₇, h₂₄₅
      have h₂₄₉: ∀ (n₂: ℕ), ∀ (n₃: ℕ), (a +ₙₐₜ 𝚜 b) =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → (a +ₙₐₜ 𝚜 b) =ₙₐₜ n₃ := by forall_elim eq_trans, (a +ₙₐₜ 𝚜 b)
      have h₂₄₁₀: ∀ (n₃: ℕ), (a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (a +ₙₐₜ b)) ∧ (𝚜 (a +ₙₐₜ b)) =ₙₐₜ n₃ → (a +ₙₐₜ 𝚜 b) =ₙₐₜ n₃ := by forall_elim h₂₄₉, (𝚜 (a +ₙₐₜ b))
      have h₂₄₁₁: (a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (a +ₙₐₜ b)) ∧ (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 a +ₙₐₜ b) → (a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 a +ₙₐₜ b) := by forall_elim h₂₄₁₀, (𝚜 a +ₙₐₜ b)
      have h₂₄₁₂: (a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (a +ₙₐₜ b)) ∧ (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 a +ₙₐₜ b) := by and_intro h₂₄₁, h₂₄₈
      have h₂₄₁₃: (a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 a +ₙₐₜ b) := by modus_ponens h₂₄₁₁, h₂₄₁₂
      have h₂₄₁₄: ∀ (m: ℕ), ((a +ₙₐₜ 𝚜 b) =ₙₐₜ m) → (𝚜 (a +ₙₐₜ 𝚜 b)) =ₙₐₜ (𝚜 m) := by forall_elim succ_cong, (a +ₙₐₜ 𝚜 b)
      have h₂₄₁₅: ((a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 a +ₙₐₜ b) → (𝚜 (a +ₙₐₜ 𝚜 b)) =ₙₐₜ (𝚜 (𝚜 a +ₙₐₜ b))) := by forall_elim h₂₄₁₄, (𝚜 a +ₙₐₜ b)
      have h₂₄₁₆: (𝚜 (a +ₙₐₜ 𝚜 b)) =ₙₐₜ (𝚜 (𝚜 a +ₙₐₜ b)) := by  modus_ponens h₂₄₁₅, h₂₄₁₃
      have h₂₄₁₇: ∀ (n₂: ℕ), ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ n₃ := by forall_elim eq_trans, (𝚜 a +ₙₐₜ 𝚜 b)
      have h₂₄₁₈: ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (a +ₙₐₜ 𝚜 b)) ∧ (𝚜 (a +ₙₐₜ 𝚜 b)) =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ n₃ := by forall_elim h₂₄₁₇, (𝚜 (a +ₙₐₜ 𝚜 b))
      have h₂₄₁₉: (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (a +ₙₐₜ 𝚜 b)) ∧ (𝚜 (a +ₙₐₜ 𝚜 b)) =ₙₐₜ (𝚜 (𝚜 a +ₙₐₜ b)) → (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (𝚜 a +ₙₐₜ b)) := by forall_elim h₂₄₁₈, (𝚜 (𝚜 a +ₙₐₜ b))
      have h₂₄₁₁₀: (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (a +ₙₐₜ 𝚜 b)) ∧ (𝚜 (a +ₙₐₜ 𝚜 b)) =ₙₐₜ (𝚜 (𝚜 a +ₙₐₜ b)) := by and_intro h₂₄₃, h₂₄₁₆
      have h₂₄₁₁₁: (𝚜 a +ₙₐₜ 𝚜 b) =ₙₐₜ (𝚜 (𝚜 a +ₙₐₜ b)) := by modus_ponens h₂₄₁₉, h₂₄₁₁₀
      iterate h₂₄₁₁₁
    have h₂₅: 𝚜 a ∈ₛₑₜ A ↔ A (𝚜 a) := by forall_elim h₀, (𝚜 a)
    have h₂₆: 𝚜 a ∈ₛₑₜ A := pc₀.deductive_eq_r2l h₂₅ h₂₄
    iterate h₂₆
  have h₃: ((𝟬 ∈ₛₑₜ A) ∧ (∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A)) → (∀ (n: ℕ), n ∈ₛₑₜ A) := by forall_elim induction, A
  have h₄: 𝟬 ∈ₛₑₜ A ∧ (∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A) := by and_intro h₁, h₂
  have h₅: ∀ (n: ℕ), n ∈ₛₑₜ A := by modus_ponens h₃, h₄
  have h₆: ∀ (n: ℕ), ∀ (m: ℕ), (n +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (n +ₙₐₜ m) := by forall_intro
    variable(a: ℕ)
    have h₆₁: a ∈ₛₑₜ A := by forall_elim h₅, a
    have h₆₂: a ∈ₛₑₜ A ↔ A a := by forall_elim h₀, a
    have h₆₃: ∀ (m: ℕ), (a +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (a +ₙₐₜ m) := pc₀.deductive_eq_l2r h₆₂ h₆₁
    iterate h₆₃
  iterate h₆

-- ### Addition commutativity
theorem add_commutativity: ∀ (n: ℕ), ∀ (m: ℕ), (n +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ n) := by
  have h₁: ∀ (n: ℕ), ∀ (m: ℕ), (n +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ n) := by forall_intro
    let A: Set ℕ := { n: ℕ | ∀ (m : ℕ), (n +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ n) }
    have h₁₁: 𝟬 ∈ₛₑₜ A := by
      have h₁₁₁: ∀ (m : ℕ), (𝟬 +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ 𝟬) := by forall_intro
        variable(a: ℕ)
        have h₁₁₁₁: (𝟬 +ₙₐₜ a) =ₙₐₜ a := by forall_elim add_zero_def, a
        have h₁₁₁₂: (a +ₙₐₜ 𝟬) =ₙₐₜ a := by forall_elim add_zero_right, a
        have h₁₁₁₃: ∀ (n₂: ℕ), ∀ (n₃: ℕ), (𝟬 +ₙₐₜ a) =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → (𝟬 +ₙₐₜ a) =ₙₐₜ n₃ := by forall_elim eq_trans, (𝟬 +ₙₐₜ a)
        have h₁₁₁₄: ∀ (n₃: ℕ), (𝟬 +ₙₐₜ a) =ₙₐₜ a ∧ a =ₙₐₜ n₃ → (𝟬 +ₙₐₜ a) =ₙₐₜ n₃ := by forall_elim h₁₁₁₃, a
        have h₁₁₁₅: (𝟬 +ₙₐₜ a) =ₙₐₜ a ∧ a =ₙₐₜ (a +ₙₐₜ 𝟬) → (𝟬 +ₙₐₜ a) =ₙₐₜ (a +ₙₐₜ 𝟬) := by forall_elim h₁₁₁₄, (a +ₙₐₜ 𝟬)
        have h₁₁₁₆: a =ₙₐₜ (a +ₙₐₜ 𝟬) := by
          have h₁₁₁₆₁: ∀ (m: ℕ), (a +ₙₐₜ 𝟬) =ₙₐₜ m → m =ₙₐₜ (a +ₙₐₜ 𝟬) := by forall_elim eq_sym, (a +ₙₐₜ 𝟬)
          have h₁₁₁₆₂: (a +ₙₐₜ 𝟬) =ₙₐₜ a → a =ₙₐₜ (a +ₙₐₜ 𝟬) := by forall_elim h₁₁₁₆₁, a
          modus_ponens h₁₁₁₆₂, h₁₁₁₂
        have h₁₁₁₇: (𝟬 +ₙₐₜ a) =ₙₐₜ a ∧ a =ₙₐₜ (a +ₙₐₜ 𝟬) := by and_intro h₁₁₁₁, h₁₁₁₆
        modus_ponens h₁₁₁₅, h₁₁₁₇
      have h₁₁₂: ∀ (x: ℕ), x ∈ₛₑₜ A ↔ A x := by forall_elim Sets.mem_def, A
      have h₁₁₃: 𝟬 ∈ₛₑₜ A ↔ A 𝟬 := by forall_elim h₁₁₂, 𝟬
      have h₁₁₄: 𝟬 ∈ₛₑₜ A := pc₀.deductive_eq_r2l h₁₁₃ h₁₁₁
      iterate h₁₁₄
    have h₁₂: ∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A := by forall_intro
      variable(a: ℕ)
      assume(h₁₂₁: a ∈ₛₑₜ A)
      have h₁₂₂: ∀ (x: ℕ), x ∈ₛₑₜ A ↔ A x := by forall_elim Sets.mem_def, A
      have h₁₂₃: a ∈ₛₑₜ A ↔ A a := by forall_elim h₁₂₂, a
      have h₁₂₄: ∀ (m : ℕ), (a +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ a) := pc₀.deductive_eq_l2r h₁₂₃ h₁₂₁
      have h₁₂₅: ∀ (m: ℕ), (𝚜 a +ₙₐₜ m) =ₙₐₜ 𝚜 (a +ₙₐₜ m) := by forall_elim add_succ_def, a
      have h₁₂₆: ∀ (m: ℕ), (𝚜 a +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ 𝚜 a) := by forall_intro
        variable(b: ℕ)
        have h₁₂₆₁: 𝚜 (a +ₙₐₜ b) =ₙₐₜ 𝚜 (b +ₙₐₜ a) := by
            have h₁₂₆₂: (a +ₙₐₜ b) =ₙₐₜ (b +ₙₐₜ a) := by forall_elim h₁₂₄, b
            have h₁₂₆₃: ∀ (m: ℕ), ((a +ₙₐₜ b) =ₙₐₜ m) → (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 m) := by forall_elim succ_cong, (a +ₙₐₜ b)
            have h₁₂₆₄: ((a +ₙₐₜ b) =ₙₐₜ (b +ₙₐₜ a)) → (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 (b +ₙₐₜ a)) := by forall_elim h₁₂₆₃, (b +ₙₐₜ a)
            modus_ponens h₁₂₆₄, h₁₂₆₂
        have h₁₂₆₂: (𝚜 a +ₙₐₜ b) =ₙₐₜ (b +ₙₐₜ 𝚜 a) := by
          have h₁₂₆₂₂: (𝚜 a +ₙₐₜ b) =ₙₐₜ 𝚜 (a +ₙₐₜ b) := by forall_elim h₁₂₅, b
          have h₁₂₆₂₄: 𝚜 (b +ₙₐₜ a) =ₙₐₜ (b +ₙₐₜ 𝚜 a) := by
            have h₁₂₆₂₄₁: ∀ (m: ℕ), (b +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (b +ₙₐₜ m) := by forall_elim add_suc_right, b
            have h₁₂₆₂₄₂: (b +ₙₐₜ 𝚜 a) =ₙₐₜ 𝚜 (b +ₙₐₜ a) := by forall_elim h₁₂₆₂₄₁, a
            have h₁₂₆₂₄₃: ∀ (m: ℕ), (b +ₙₐₜ 𝚜 a) =ₙₐₜ m → m =ₙₐₜ (b +ₙₐₜ 𝚜 a) := by forall_elim eq_sym, (b +ₙₐₜ 𝚜 a)
            have h₁₂₆₂₄₄: (b +ₙₐₜ 𝚜 a) =ₙₐₜ 𝚜 (b +ₙₐₜ a) → (𝚜 (b +ₙₐₜ a)) =ₙₐₜ (b +ₙₐₜ 𝚜 a) := by forall_elim h₁₂₆₂₄₃, (𝚜 (b +ₙₐₜ a))
            modus_ponens h₁₂₆₂₄₄, h₁₂₆₂₄₂
          have h₁₂₆₂₅: ∀ (n₂: ℕ), ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ b) =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ b) =ₙₐₜ n₃ := by forall_elim eq_trans, (𝚜 a +ₙₐₜ b)
          have h₁₂₆₂₆: ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (a +ₙₐₜ b)) ∧ (𝚜 (a +ₙₐₜ b)) =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ b) =ₙₐₜ n₃ := by forall_elim h₁₂₆₂₅, (𝚜 (a +ₙₐₜ b))
          have h₁₂₆₂₇: (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (a +ₙₐₜ b)) ∧ (𝚜 (a +ₙₐₜ b)) =ₙₐₜ (𝚜 (b +ₙₐₜ a)) → (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (b +ₙₐₜ a)) := by forall_elim h₁₂₆₂₆, (𝚜 (b +ₙₐₜ a))
          have h₁₂₆₂₈: (𝚜 a +ₙₐₜ b) =ₙₐₜ 𝚜 (a +ₙₐₜ b) ∧ (𝚜 (a +ₙₐₜ b) =ₙₐₜ 𝚜 (b +ₙₐₜ a)) := by and_intro h₁₂₆₂₂, h₁₂₆₁
          have h₁₂₆₂₉: (𝚜 a +ₙₐₜ b) =ₙₐₜ 𝚜 (b +ₙₐₜ a) := by modus_ponens h₁₂₆₂₇, h₁₂₆₂₈
          have h₁₂₆₂₁₁: ∀ (n₃: ℕ), (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (b +ₙₐₜ a)) ∧ (𝚜 (b +ₙₐₜ a)) =ₙₐₜ n₃ → (𝚜 a +ₙₐₜ b) =ₙₐₜ n₃ := by forall_elim h₁₂₆₂₅, (𝚜 (b +ₙₐₜ a))
          have h₁₂₆₂₁₂: (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (b +ₙₐₜ a)) ∧ (𝚜 (b +ₙₐₜ a)) =ₙₐₜ (b +ₙₐₜ 𝚜 a) → (𝚜 a +ₙₐₜ b) =ₙₐₜ (b +ₙₐₜ 𝚜 a) := by forall_elim h₁₂₆₂₁₁, (b +ₙₐₜ 𝚜 a)
          have h₁₂₆₂₁₃: (𝚜 a +ₙₐₜ b) =ₙₐₜ (𝚜 (b +ₙₐₜ a)) ∧ (𝚜 (b +ₙₐₜ a)) =ₙₐₜ (b +ₙₐₜ 𝚜 a) := by and_intro h₁₂₆₂₉, h₁₂₆₂₄
          modus_ponens h₁₂₆₂₁₂, h₁₂₆₂₁₃
      have h₁₂₇: (𝚜 a) ∈ₛₑₜ A ↔ A (𝚜 a) := by forall_elim h₁₂₂, (𝚜 a)
      have h₁₂₈: (𝚜 a) ∈ₛₑₜ A := pc₀.deductive_eq_r2l h₁₂₇ h₁₂₆
      iterate h₁₂₈
    have h₁₃: (𝟬 ∈ₛₑₜ A) ∧ (∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A) := by and_intro h₁₁, h₁₂
    have h₁₄: ((𝟬 ∈ₛₑₜ A) ∧ (∀ (n: ℕ), n ∈ₛₑₜ A → (𝚜 n) ∈ₛₑₜ A)) → (∀ (n: ℕ), n ∈ₛₑₜ A) := by forall_elim induction, A
    have h₁₅: ∀ (n: ℕ), n ∈ₛₑₜ A := by modus_ponens h₁₄, h₁₃
    variable (a: ℕ)
    have h₁₆: a ∈ₛₑₜ A := by forall_elim h₁₅, a
    have h₁₇: ∀ (x: ℕ), x ∈ₛₑₜ A ↔ A x := by forall_elim Sets.mem_def, A
    have h₁₈: a ∈ₛₑₜ A ↔ A a := by forall_elim h₁₇, a
    have h₁₉: ∀ (m : ℕ), (a +ₙₐₜ m) =ₙₐₜ (m +ₙₐₜ a) := pc₀.deductive_eq_l2r h₁₈ h₁₆
    iterate h₁₉
  iterate h₁
