import Universe
import Logic
import Universals.Sets.Universal

namespace Universe

namespace Sets

open Logic.PC₁

-- Notation to define `Sets` from `Predicates` with free variables
-- Allows writing: { x : T | body } with <prrof of congruence for T>
def set_from (P : CongruentUnaryPredicate U) : (Set U).Particular := P
macro "{" x:ident ":" t:term "|" body:term "}" " with " cong:term  : term => do
  `(set_from
      { pred := fun $x : $t => $body
        cong := $cong })

end Sets

end Universe
