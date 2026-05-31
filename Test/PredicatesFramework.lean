import Logic.PredicateCalculus.Schemas.Predicates
import Logic.PredicateCalculus.Definitions.Predicates

/-!
# Smoke test for the integrated `UnaryPredicate` / `BinaryPredicate` framework.

Verifies that:
- The structures exist and are reachable from the top-level barrels.
- The macros `unary_predicate` and `binary_predicate` work end-to-end via the
  explicit `with` clause.
- Dot-notation `.def` and `.cong` are exposed.
- CoeFun lets us apply the named predicate directly.
- The inherited `toCongruent*Predicate` projection is available.

Auto-cong inference for bodies involving `=₍U₎` is **not** tested here — it
currently fails because `congruent_equal_to` / `congruent_equal_from` were
deleted in the `Equals/Instance.lean` refactor. That's an orthogonal issue
tracked separately; this test only verifies the framework wiring.
-/

namespace Test.PredicatesFramework

open Logic
open Logic.PC₁

variable {U : Universal}

-- ─────────────────────────────────────────────────────────────────
-- Unary: explicit-cong path
-- ─────────────────────────────────────────────────────────────────

unary_predicate trivially_true : (x : U.Particular ↦ True)
  with by forall_intro
    variable(a: U.Particular)
    variable(b: U.Particular)
    assume(h₁: a =₍U₎ b)
    have h₂: True → True := by
      assume(h₂₁: True)
      iterate h₂₁
    have h₃: True ↔ True := by iff_intro h₂, h₂
    iterate h₃

#check @trivially_true                            -- UnaryPredicate U …
#check @trivially_true.def                        -- propositional bridge
#check @trivially_true.cong                       -- derived congruence
#check @trivially_true.toCongruentUnaryPredicate  -- inherited projection

-- Apply via CoeFun:
example (x : U.Particular) : Prop := trivially_true x

-- Opacity: the bridge is propositional, not definitional.
example (x : U.Particular) (h : trivially_true x) : True :=
  PC₀.deductive_eq_l2r (trivially_true.def x) h

-- ─────────────────────────────────────────────────────────────────
-- Binary: explicit-cong path
-- ─────────────────────────────────────────────────────────────────

binary_predicate trivially_true_binary : (x : U.Particular, y : U.Particular ↦ True)
  with by forall_intro
    variable(a₁: U.Particular)
    variable(a₂: U.Particular)
    variable(b₁: U.Particular)
    variable(b₂: U.Particular)
    assume(h₁: a₁ =₍U₎ a₂)
    assume(h₂: b₁ =₍U₎ b₂)
    have h₃: True → True := by
      assume(h₃₁: True)
      iterate h₃₁
    have h₄: True ↔ True := by iff_intro h₃, h₃
    iterate h₄

#check @trivially_true_binary
#check @trivially_true_binary.def
#check @trivially_true_binary.cong
#check @trivially_true_binary.toCongruentBinaryPredicate

example (x y : U.Particular) : Prop := trivially_true_binary x y

example (x y : U.Particular) (h : trivially_true_binary x y) : True :=
  PC₀.deductive_eq_l2r (trivially_true_binary.def x y) h

end Test.PredicatesFramework
