import Universe
import Logic
import Universals.Correspondences.Universal
import Universals.Correspondences.Predicates.Unary.Functional.Predicate

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁

-- # Function Universal
-- The sub-universal of Corr U₁ U₂ whose particulars are functional correspondences.
def FunctionUniversal (U₁: Universal) (U₂: Universal): Universal := sub_universal (CorrespondenceUniversal U₁ U₂) (functional_predicate U₁ U₂)
notation:35 U₁:36 " ⭢ " U₂:36 => FunctionUniversal U₁ U₂

def Function (U₁: Universal) (U₂: Universal): Type := (FunctionUniversal U₁ U₂).Particular

def func_eq (f₁: Function U₁ U₂) (f₂: Function U₁ U₂): Prop := f₁ =₍FunctionUniversal U₁ U₂₎ f₂
notation:50 a:51 " =→ " b:51 => func_eq a b

end Correspondences

end Universe
