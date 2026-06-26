import Universals.Sets
import Universals.Sets.Predicates.Unary.Singleton.Predicate
import Universals.Sets.Universals.Singleton.Universal

namespace Test

open Universe Universe.Sets Logic Logic.PC₁

-- (1) ↑A with fully-specified target — works:
noncomputable example {U: Universal} (A: SingletonSet U): Set U := A

-- (2) ↑A where target is `(𝐒𝐞𝐭 ?).Particular` (metavariable) — fails:
example {U: Universal} (A: SingletonSet U): Prop := is_singleton (A : Set U)

-- (3) Pin the target via explicit type ascription on the upcast itself:
example {U: Universal} (A: SingletonSet U): Prop := is_singleton (A : Set U)

-- (4) Pin is_singleton's U explicitly so the target is no longer a metavariable:
example {U: Universal} (A: SingletonSet U): Prop := is_singleton (U:=U) A

-- (5) The user's failing form:
example {U: Universal} (A: SingletonSet U):
    is_singleton (U:=U) A ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ A := by forall_elim is_singleton.def, (A : Set U)

-- (6) The forall_elim with explicit type-ascribed upcast:
example {U: Universal} (A: SingletonSet U):
    is_singleton (U:=U) (↑A : Set U) ↔ ∃!₍U₎ (x: U.Particular), x ∈ₛₑₜ (↑A : Set U) := by forall_elim is_singleton.def, (↑A : Set U)

end Test
