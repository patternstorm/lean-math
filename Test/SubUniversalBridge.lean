import Universals.Sets.Definitions.SetsAsUniversals.Definition
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Relations.Universal
import Universals.Relations.Predicates.Unary.Reflexive.Predicate
import Universals.Dyads.Definitions.Uncurry.Definition

/-!
# Sub-Universal Quantifier Bridge Test

Minimal test: can we go between sub-universal quantification and
guarded parent-universal quantification using our ND tactics?
-/

namespace Universe
namespace Test

open Logic
open Logic.PC₁
open Logic.ND
open Sets
open Dyads
open Relations

variable {U: Universal}

-- Test 1: Guarded U-quantifier → Sub-universal quantifier
theorem test_guarded_to_sub (S: Set U) (R: Rel U U):
  (∀ (x: U.Particular), x ∈ₛₑₜ S → R.pred (x ⋈ x)) →
  (∀ (v: (set_as_universal S).Particular), R.pred (v.val ⋈ v.val)) := by forall_intro
  assume(h: ∀ (x: U.Particular), x ∈ₛₑₜ S → R.pred (x ⋈ x))
  variable(v: (set_as_universal S).Particular)
  have h₁: ∀ (x: U.Particular), x ∈ₛₑₜ S ↔ S.pred x := by forall_elim mem_def, S
  have h₂: v.val ∈ₛₑₜ S ↔ S.pred v.val := by forall_elim h₁, v.val
  have h₃: v.val ∈ₛₑₜ S := PC₀.deductive_eq_r2l h₂ v.property
  have h₄: v.val ∈ₛₑₜ S → R.pred (v.val ⋈ v.val) := by forall_elim h, v.val
  have h₅: R.pred (v.val ⋈ v.val) := by modus_ponens h₄, h₃
  iterate h₅

-- Test 2: Sub-universal quantifier → Guarded U-quantifier
theorem test_sub_to_guarded (S: Set U) (R: Rel U U):
  (∀ (v: (set_as_universal S).Particular), R.pred (v.val ⋈ v.val)) →
  (∀ (x: U.Particular), x ∈ₛₑₜ S → R.pred (x ⋈ x)) := by forall_intro
  assume(h: ∀ (v: (set_as_universal S).Particular), R.pred (v.val ⋈ v.val))
  variable(x: U.Particular)
  assume(hx: x ∈ₛₑₜ S)
  have h₁: ∀ (x': U.Particular), x' ∈ₛₑₜ S ↔ S.pred x' := by forall_elim mem_def, S
  have h₂: x ∈ₛₑₜ S ↔ S.pred x := by forall_elim h₁, x
  have h₃: S.pred x := PC₀.deductive_eq_l2r h₂ hx
  let v: (set_as_universal S).Particular := ⟨x, h₃⟩
  have h₄: R.pred (v.val ⋈ v.val) := by forall_elim h, v
  iterate h₄

end Test
end Universe
