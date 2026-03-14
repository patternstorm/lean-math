import Universe
import Logic
import Universals.Correspondences.Particular

/-!
# Correspondence Universal

Correspondences over U₁ and U₂ form their own Universal, with set equality
inherited from the underlying arrow sets. This makes correspondences
first-class: they can be quantified over, collected into sets, and subjected
to the same predicate/set machinery as any other particulars.
-/

namespace Universe

namespace Correspondences

open Logic
open Logic.PC₁
open Sets
open Arrows

-- # Correspondence equality is set equality over arrow sets
def eq (C₁: Correspondences.Particular U₁ U₂) (C₂: Correspondences.Particular U₁ U₂): Prop := C₁ =ₛₑₜ C₂

def equality (U₁: Universal) (U₂: Universal): Equality (Correspondences.Particular U₁ U₂) := Sets.equality

-- # Correspondence Universal
def CorrespondenceUniversal (U₁: Universal) (U₂: Universal): Universal := {
  Particular := Correspondences.Particular U₁ U₂
  eq := equality U₁ U₂
}
notation "𝐂𝐨𝐫𝐫" => CorrespondenceUniversal
notation:35 U₁:36 " ➞ᶜ " U₂:36 => CorrespondenceUniversal U₁ U₂
notation:50 a:51 " =→ᶜ  " b:51 => eq a b
abbrev Corr U₁ U₂ := (CorrespondenceUniversal U₁ U₂).Particular
notation:35 U₁:36 " ⭢ᶜ " U₂:36 => Corr U₁ U₂

end Correspondences

end Universe
