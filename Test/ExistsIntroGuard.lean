import Lean
import Universals.NaturalNumbers.Particular

/-!
# Sandbox: Testing exists_intro guard against postulated axiom witnesses

Tests whether we can detect and reject direct use of postulated axiom
constructors as witnesses in exists_intro, while accepting legitimate
witnesses (local variables from exists_elim, defs, etc.).
-/

namespace Test.ExistsIntroGuard

open Lean Meta Elab Tactic
open Logic
open Logic.PC₁
open Logic.ND
open Universe.NaturalNumbers

-- # Guarded exists_intro (test version)
-- Same as exists_intro but rejects witnesses whose head symbol is an axiom.

syntax "exists_intro_guarded" term "," term: tactic

elab_rules : tactic
  | `(tactic| exists_intro_guarded $h, $w) => do
      withMainContext do
        -- Elaborate the witness to inspect its structure
        let wExpr ← Term.elabTerm w none
        -- Strip applications to find the head symbol
        let head := wExpr.getAppFn
        -- Check if the head is a constant declared as an axiom
        match head with
        | .const name _ =>
          let env ← getEnv
          match env.find? name with
          | some (.axiomInfo _) =>
            throwError "exists_intro_guarded: witness '{w}' uses postulated axiom '{name}' directly. Use the corresponding existence axiom to extract a variable witness instead."
          | _ => pure ()
        | _ => pure ()
        -- If we passed the check, proceed with normal exists_intro behavior
        evalTactic (← `(tactic| exact ⟨$w, $h⟩))

-- ===================================================================
-- ACCEPT tests — these should compile
-- ===================================================================

-- ## TEST 1: Variable from exists_elim (zero), used in proof style
theorem test_accept_zero_var : ∀ (n: ℕ), n 🟰 𝟬 → (∃ (k: ℕ), k 🟰 𝟬) := by forall_intro
  variable(a: ℕ)
  assume(h₁: a 🟰 𝟬)
  have h₂: ∃ (n: ℕ), n 🟰 𝟬 := zero_existence
  have ⟨(z: ℕ), (h₃: z 🟰 𝟬)⟩ := exists_elim h₂
  have h₄: ∃ (k: ℕ), k 🟰 𝟬 := by exists_intro_guarded h₃, z
  iterate h₄

-- ## TEST 2: Variable from exists_elim (succ), used in proof style
theorem test_accept_succ_var : ∀ (n: ℕ), ∃ (m: ℕ), m 🟰 𝚜 n := by forall_intro
  variable(a: ℕ)
  have h₁: ∃ (m: ℕ), m 🟰 𝚜 a := by forall_elim succ_existence, a
  have ⟨(s: ℕ), (h₂: s 🟰 𝚜 a)⟩ := exists_elim h₁
  have h₃: ∃ (m: ℕ), m 🟰 𝚜 a := by exists_intro_guarded h₂, s
  iterate h₃

-- ===================================================================
-- REJECT tests — these should produce errors (uncomment one at a time)
-- ===================================================================

-- ## TEST 3: Should REJECT — 𝟬 is axiom `zero`
-- theorem test_reject_zero : ∀ (n: ℕ), n 🟰 𝟬 → (∃ (k: ℕ), k 🟰 𝟬) := by forall_intro
--   variable(a: ℕ)
--   assume(h₁: a 🟰 𝟬)
--   have h₂: 𝟬 🟰 𝟬 := by forall_elim leibniz_eq_refl, 𝟬
--   have h₃: ∃ (k: ℕ), k 🟰 𝟬 := by exists_intro_guarded h₂, 𝟬
--   iterate h₃

-- ## TEST 4: Should REJECT — 𝚜 n is axiom `succ` applied
-- theorem test_reject_succ : ∀ (n: ℕ), ∃ (m: ℕ), m 🟰 𝚜 n := by forall_intro
--   variable(a: ℕ)
--   have h₁: 𝚜 a 🟰 𝚜 a := by forall_elim leibniz_eq_refl, 𝚜 a
--   have h₂: ∃ (m: ℕ), m 🟰 𝚜 a := by exists_intro_guarded h₁, 𝚜 a
--   iterate h₂

end Test.ExistsIntroGuard
