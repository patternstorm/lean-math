import Universe
import Logic
import Test.VariableArityPredicates

namespace Universe
namespace ProofTest

open Logic
open Logic.PC₁
open Logic.ND

variable {U : Universal}

-- A binary predicate typed as PredCons — testing that our Pred definition works in proofs
axiom R: PredCons U.Particular
axiom R_sym: ∀ (x: U.Particular), ∀ (y: U.Particular), R x y → R y x
axiom R_trans: ∀ (x: U.Particular), ∀ (y: U.Particular), ∀ (z: U.Particular),
  R x y ∧ R y z → R x z

-- Proof by Claude Opus 4.6 (claude-opus-4-6), 2026-02-26
-- If R is symmetric and transitive, then R(a,b) → R(a,a)
theorem R_reflexive_from_related:
    ∀ (a: U.Particular), ∀ (b: U.Particular), R a b → R a a := by forall_intro
  variable (a: U.Particular)
  variable (b: U.Particular)
  assume (h₁: R a b)
  have h₂: ∀ (y: U.Particular), R a y → R y a := by forall_elim R_sym, a
  have h₃: R a b → R b a := by forall_elim h₂, b
  have h₄: R b a := by modus_ponens h₃, h₁
  have h₅: ∀ (y: U.Particular), ∀ (z: U.Particular), R a y ∧ R y z → R a z := by forall_elim R_trans, a
  have h₆: ∀ (z: U.Particular), R a b ∧ R b z → R a z := by forall_elim h₅, b
  have h₇: R a b ∧ R b a → R a a := by forall_elim h₆, a
  have h₈: R a b ∧ R b a := by and_intro h₁, h₄
  have h₉: R a a := by modus_ponens h₇, h₈
  iterate h₉

end ProofTest
end Universe
