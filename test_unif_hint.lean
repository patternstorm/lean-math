-- Test: does defining Set as the projection help the unifier?
import Logic

open Logic.PC₁

-- Approach A: Set defined independently (current design)
namespace TestA
  def RawSet (U : Universal) : Type := CongruentUnaryPredicate U
  def equality : Equality (RawSet U) := sorry
  def SetsUniv (U : Universal) : Universal := { Particular := RawSet U, eq := equality }
  def Set (U : Universal) : Type := RawSet U

  axiom myArrow {U₁ U₂ : Universal} : U₁.Particular → U₂.Particular → Prop
  axiom myApply (U₁ U₂ : Universal) : U₁.Particular → Set U₂

  variable (U₁ U₂ : Universal) (a : U₁.Particular)
  #check myArrow a (myApply U₁ U₂ a)  -- A: does this fail?
end TestA

-- Approach B: Set defined AS the projection
namespace TestB
  def RawSet (U : Universal) : Type := CongruentUnaryPredicate U
  def equality : Equality (RawSet U) := sorry
  def SetsUniv (U : Universal) : Universal := { Particular := RawSet U, eq := equality }
  abbrev Set (U : Universal) : Type := (SetsUniv U).Particular

  axiom myArrow {U₁ U₂ : Universal} : U₁.Particular → U₂.Particular → Prop
  axiom myApply (U₁ U₂ : Universal) : U₁.Particular → Set U₂

  variable (U₁ U₂ : Universal) (a : U₁.Particular)
  #check myArrow a (myApply U₁ U₂ a)  -- B: does this work?
end TestB
