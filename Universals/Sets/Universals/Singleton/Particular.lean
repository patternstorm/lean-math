import Universe
import Logic
import Universals.Sets.Universal
import Universals.Sets.Predicates.Unary.Singleton.Predicate
import Universals.Sets.Universals.Singleton.Universal

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- # Constructing a particular of the Singleton Universal
--
-- `as_singleton X h` packages a set `X : Set U` together with a proof
-- `h : is_singleton X` into a `SingletonSet U`. This is the framework-named
-- constructor; consumers should call it instead of writing `⟨X, h⟩` directly,
-- which would reach into Lean's `Subtype.mk` plumbing.
--
-- Marked `@[reducible]` so that `(as_singleton X h).val` unfolds to `X`
-- definitionally — needed for the `CoeDep` upcast `SingletonSet U → Set U`
-- to compose transparently with downstream predicates like
-- `singleton_of_graph_pred`.
--
-- Definition by Claude Opus 4.7 (claude-opus-4-7), 2026-06-26
@[reducible] def as_singleton {U: Universal} (X: Set U) (h: is_singleton X): SingletonSet U := ⟨X, h⟩


end Sets

end Universe
