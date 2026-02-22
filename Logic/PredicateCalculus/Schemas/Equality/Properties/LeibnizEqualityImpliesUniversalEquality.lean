import Logic.PredicateCalculus.Schemas.Universal
import Logic.PredicateCalculus.Schemas.Equality.Instances.LeibnizEquality


namespace Logic

namespace PC₁


-- Leibniz equality implies Universal equality: for any Universal U, if two terms
-- are syntactically identical (🟰), they are equal under U's equality (=₍U₎).
--
-- This theorem requires an already-constructed Universal (since it uses U's
-- reflexivity). It is therefore NOT used during the bootstrap — proving that
-- a type's equality is an equivalence relation proceeds in two phases:
-- (1) Reflexivity is proved first, using only the constructor axioms and
--     induction — no Leibniz equality needed.
-- (2) Symmetry and transitivity require case analysis on the inner variables,
--     which comes from exhaustiveness induction axioms. These produce Leibniz
--     equalities (🟰), and Leibniz substitution (leibniz_eq_subs) converts
--     them into useful facts by substituting 🟰-equal terms inside any
--     predicate — including predicates involving the type's own equality —
--     without requiring a Universal to exist yet.
--
-- Once the Universal is constructed, this theorem provides a convenient
-- shortcut for later proofs (e.g. about operations) that need case analysis
-- via exhaustiveness: instead of setting up a Leibniz substitution proof each
-- time, one can directly convert the Leibniz equalities produced by
-- exhaustiveness (e.g. n 🟰 𝟬 or n 🟰 𝚜 k) into Universal equalities (=₍U₎).
--
-- The proof relies only on Leibniz substitution and the reflexivity of U's
-- equality, so it works for every Universal.
theorem leibniz_eq_implies_universal_eq(U: Universal): ∀ (x: U.Particular), ∀ (y: U.Particular), x 🟰 y → x =₍U₎ y := by forall_intro
  variable(a: U.Particular)
  variable(b: U.Particular)
  assume(h₁: a 🟰 b)
  let pred := (x: U.Particular ↦ a =₍U₎ x)
  have h₂: ∀ (x: U.Particular), ∀ (y: U.Particular), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
  have h₃: ∀ (y: U.Particular), a 🟰 y → (pred a ↔ pred y) := by forall_elim h₂, a
  have h₄: a 🟰 b → (pred a ↔ pred b) := by forall_elim h₃, b
  have h₅: pred a ↔ pred b := by modus_ponens h₄, h₁
  have h₆: a =₍U₎ a := U.eq.refl a
  have h₇: a =₍U₎ b := PC₀.deductive_eq_l2r h₅ h₆
  iterate h₇

end PC₁
end Logic
