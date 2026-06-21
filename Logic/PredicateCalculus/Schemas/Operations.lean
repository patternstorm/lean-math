import Logic.PredicateCalculus.Schemas.Operations.Unary
import Logic.PredicateCalculus.Schemas.Operations.Binary
import Logic.PredicateCalculus.Schemas.Operations.Constant

/-!
# Operations — why they live under `Logic/PredicateCalculus/`

Introducing an operation is a logic-layer act. It extends the FOL
theory signature with a new (syntactic) term in the codomain Universal,
together with a rule (the satisfies axiom) that identifies it with a
specific particular of that codomain. The act introduces a new "thing"
we can speak about that denotes a particular of the codomain Universal.

Logic allows us to define the "things" we want to talk about and
provides a means to talk about them, for instance, to classify those things,
giving rise to mathematical objects/structures.

Therefore, organizing operations themselves inside a mathematical
structure is perfectly fine. A Universal whose particulars are operations of a given arity
— a Universal of total functions, as refined universal of `𝐑𝐞𝐥` — is a
perfectly legitimate math-layer construction. But it
is a *different act*: collecting operations as objects to reason about,
compose, and quantify over.
-/
