import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Definitions.SetComprehension.Definition

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- The `Universal Set`
def universal_set: Set U := { x: U.Particular | True } with (true U).cong
notation "Uₛₑₜ" => universal_set

end Sets

end Universe
