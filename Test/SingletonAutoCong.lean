import Universals.Sets
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Universals.Singleton.Predicates.Binary.Definitions.SingletonElemGraphPredicate
import Universals.Sets.Universals.Singleton.Universal

namespace Test

open Universe Universe.Sets Logic Logic.PC₁

-- Diagnostic: drill into the synthesis chain for the combined binary cong.

-- (1) Fiber-second of mem at a SingletonSet value (via embedding).
example {U: Universal} (S: SingletonSet U):
    CongruentUnary U (fun y => mem.pred y (SubUniversal.embedding.op S)) := inferInstance

-- (2) Fiber-first of mem at a fixed particular, lifted through the embedding.
example {U: Universal} (y: U.Particular):
    CongruentUnary (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) (fun S => mem.pred y (SubUniversal.embedding.op S)) := inferInstance

-- (3) Both fibers as ∀-quantified — what `congruent_binary_from_fibers` needs.
example {U: Universal}: ∀ S: SingletonSet U,
    CongruentUnary U (fun y => mem.pred y (SubUniversal.embedding.op S)) := fun _ => inferInstance
example {U: Universal}: ∀ y: U.Particular,
    CongruentUnary (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) (fun S => mem.pred y (SubUniversal.embedding.op S)) := fun _ => inferInstance

-- (4) Combined binary cong.
example {U: Universal}:
    CongruentBinary (𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U) U (fun S y => mem.pred y (SubUniversal.embedding.op S)) := inferInstance

end Test
