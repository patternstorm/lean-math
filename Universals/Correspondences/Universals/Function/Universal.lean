import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Predicates.Unary.Functional.Predicate

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁

-- # Function Universal
-- The refined universal of Corr U₁ U₂ whose particulars are functional correspondences.
def FunctionUniversal (U₁: Universal) (U₂: Universal): Universal := (CorrespondenceUniversal U₁ U₂) ↾ (functional_predicate U₁ U₂)

notation "𝐅𝐮𝐧𝐜" => FunctionUniversal
notation:35 U₁:36 " ➔ " U₂:36 => FunctionUniversal U₁ U₂

abbrev Func (U₁: Universal) (U₂: Universal): Type := (FunctionUniversal U₁ U₂).Particular
notation:35 U₁:36 " ⭢ " U₂:36 => Func U₁ U₂

def func_eq (f₁: Func U₁ U₂) (f₂: Func U₁ U₂): Prop := f₁ =₍FunctionUniversal U₁ U₂₎ f₂
notation:50 a:51 " =→ " b:51 => func_eq a b

end Correspondences

end Universe
