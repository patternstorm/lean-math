import Core.NaturalDeduction
import Core.Universe
import Core.Sets

open Universe
open Sets

axiom NaturalNumber : Type
notation "ℕ" => NaturalNumber

-- # Natural Numbers constructors
axiom zero : ℕ
notation "𝟬" => zero

axiom succ : ℕ → ℕ
prefix:max "𝚜" => succ

-- # Natural Numbers equality
axiom eq: ℕ → ℕ → Prop
notation:50 A:51 " =ₙₐₜ " B:51 => eq A B

axiom eq_refl: ∀ (n: ℕ), n =ₙₐₜ n
axiom eq_poly_eq : ∀ (n: ℕ), ∀ (m: ℕ), n =ₙₐₜ m ↔ n =ₚ m
-- NOTE, we should be able to derive these
axiom eq_sym: ∀ (n: ℕ), ∀ (m: ℕ), n =ₙₐₜ m → m =ₙₐₜ n
axiom eq_trans: ∀ (n₁: ℕ), ∀ (n₂: ℕ), ∀ (n₃: ℕ), n₁ =ₙₐₜ n₂ ∧ n₂ =ₙₐₜ n₃ → n₁ =ₙₐₜ n₃

-- Natural Numbers induction
axiom induction : ∀ (S : Set ℕ),
    (𝟬 ∈ₛₑₜ S) ∧
    (∀ (n: ℕ), n ∈ₛₑₜ S → (𝚜 n) ∈ₛₑₜ S) →
    (∀ (n: ℕ), n ∈ₛₑₜ S)

-- # Natural Numbers operations
axiom add : ℕ → ℕ → ℕ
notation "(" n "+ₙₐₜ" m ")" => add n m

axiom add_zero_def : ∀ (n: ℕ), (n +ₙₐₜ 𝟬) =ₙₐₜ n
axiom add_succ_def : ∀ (n: ℕ), ∀ (m: ℕ), (n +ₙₐₜ 𝚜 m) =ₙₐₜ 𝚜 (n +ₙₐₜ m)



-- Demonstrates that succ zero is a natural number
noncomputable def succ_zero_is_natural : ℕ := succ (succ (succ (succ zero)))

theorem kk (n : ℕ) : n =ₙₐₜ n := by forall_elim eq_refl, n

theorem kk2 (n : ℕ) : n = n := by
  have h1 := kk (succ (succ (succ (succ zero))))
  rfl
