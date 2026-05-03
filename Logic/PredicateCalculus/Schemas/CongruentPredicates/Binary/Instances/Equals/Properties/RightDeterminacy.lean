import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals.Instance
import Logic.NaturalDeduction.Rules

namespace Logic

namespace PC₁

-- # universal equality right determinacy — every particular is at most equal to another particular, i.e. itself

-- Proof by Claude Opus 4.7 Max, 2026-05-02
theorem equals_right_determinacy:
  ∀ (x: U.Particular), ∀ (y₁: U.Particular), ∀ (y₂: U.Particular), x =₍U₎ y₁ ∧ x =₍U₎ y₂ → y₁ =₍U₎ y₂ := by forall_intro
  variable(a: U.Particular)
  variable(b: U.Particular)
  variable(c: U.Particular)
  assume(h₁: a =₍U₎ b ∧ a =₍U₎ c)
  have h₂: a =₍U₎ b := by and_elim h₁
  have h₃: a =₍U₎ c := by and_elim h₁
  -- Sym on h₂: a =₍U₎ b → b =₍U₎ a
  have h₄: a =₍U₎ b → b =₍U₎ a := by forall_elim U.eq.sym, a, b
  have h₅: b =₍U₎ a := by modus_ponens h₄, h₂
  -- Trans on h₅, h₃: b =₍U₎ a, a =₍U₎ c → b =₍U₎ c
  have h₆: b =₍U₎ a ∧ a =₍U₎ c := by and_intro h₅, h₃
  have h₇: b =₍U₎ a ∧ a =₍U₎ c → b =₍U₎ c := by forall_elim U.eq.trans, b, a, c
  have h₈: b =₍U₎ c := by modus_ponens h₇, h₆
  iterate h₈

end PC₁

end Logic
