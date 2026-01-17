import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Definitions.SetComprehension.Definition

namespace Universe

namespace Sets

open Logic
open Logic.PC₁

-- The `Empty Set`.
def empty_set : (Set U).Particular := { x: U.Particular | False } with (false U).cong
notation "∅ₛₑₜ" => empty_set

end Sets

end Universe
