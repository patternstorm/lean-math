import Universals.Sets

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- # Regression test: auto-cong fires on `=₍U₎` and `=ₛₑₜ` bodies via the
-- standard generic machinery — no bridge instances required.
--
-- After the notation move, `a =₍U₎ b` expands to `@equals U a b` (with `equals
-- : CongruentBinaryPredicate U U`), which via `CoeFun` becomes `equals.pred a
-- b`. The standard `fiber_*_binary_congruent_unary equals a` instances
-- pattern-match against that shape directly, so auto-cong fires uniformly
-- through the generic chain (`congruent_*` for connectives → fiber
-- preservation → CBP).
--
-- Per-Universal aliases like `=ₛₑₜ` reduce to the same shape because they are
-- defined to expand via `=₍SetsUniversal _₎`. The unifier sees `equals` with
-- the correct Universal pinned and the same auto-cong chain fires.

-- Test A: body `(x ↦ equals.pred x a)` — fix second arg, vary first.
-- Should fire via `fiber_second_binary_congruent_unary equals a`.
example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ equals.pred x a) := inferInstance

-- Test B: body `(x ↦ equals.pred a x)` — fix first arg, vary second.
-- Should fire via `fiber_first_binary_congruent_unary equals a`.
example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ equals.pred a x) := inferInstance

-- Test C: via CoeFun shorthand `equals x a` (no `.pred`).
-- This is what `=₍U₎` expands to.
example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ equals x a) := inferInstance

-- Test D: composition. Body `(x ↦ equals.pred x a ∨ equals.pred x b)`.
-- Should compose `congruent_disjunction` with `fiber_second_binary_congruent_unary`.
example {U: Universal} (a b: U.Particular) : CongruentUnary U (x: U.Particular ↦ equals.pred x a ∨ equals.pred x b) := inferInstance

-- Test E: a more complex composition.
-- `(x ↦ ∀ y, equals.pred x y → equals.pred y a)` — peels ∀, →, then fiber.
example {U: Universal} (a: U.Particular) :
    CongruentUnary U (x: U.Particular ↦ ∀ y, equals.pred x y → equals.pred y a) := inferInstance


-- # `=₍U₎` notation tests

-- Test F: body `(x ↦ x =₍U₎ a)` — fix RHS, vary LHS.
example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ x =₍U₎ a) := inferInstance

-- Test G: body `(x ↦ a =₍U₎ x)` — fix LHS, vary RHS.
example {U: Universal} (a: U.Particular) : CongruentUnary U (x: U.Particular ↦ a =₍U₎ x) := inferInstance

-- Test H: composition with disjunction.
example {U: Universal} (a b: U.Particular) :
    CongruentUnary U (x: U.Particular ↦ x =₍U₎ a ∨ x =₍U₎ b) := inferInstance

-- Test I: deep composition — ∀, →, fiber via the real notation.
-- Same shape as Test E but via the user-facing notation.
example {U: Universal} (a: U.Particular) :
    CongruentUnary U (x: U.Particular ↦ ∀ y, x =₍U₎ y → y =₍U₎ a) := inferInstance


-- # `=ₛₑₜ` alias tests
--
-- `=ₛₑₜ` is defined as `A =ₛₑₜ B  =>  A =₍SetsUniversal _₎ B`, so it
-- elaborates through the same `equals` machinery, just with `SetsUniversal _`
-- pinned as the Universal.

-- Test J: body `(S ↦ S =ₛₑₜ A)` — fix RHS, vary LHS.
example {U: Universal} (A: Set U) : CongruentUnary (𝐒𝐞𝐭 U) (S: Set U ↦ S =ₛₑₜ A) := inferInstance

-- Test K: body `(S ↦ A =ₛₑₜ S)` — fix LHS, vary RHS.
example {U: Universal} (A: Set U) : CongruentUnary (𝐒𝐞𝐭 U) (S: Set U ↦ A =ₛₑₜ S) := inferInstance

-- Test L: composition with disjunction.
example {U: Universal} (A B: Set U) :
    CongruentUnary (𝐒𝐞𝐭 U) (S: Set U ↦ S =ₛₑₜ A ∨ S =ₛₑₜ B) := inferInstance


end Sets

end Universe
