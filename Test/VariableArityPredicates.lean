import Universe
import Logic

-- Test: Variable-arity predicates via recursive type definition

-- Approach 1: Direct recursive definition
-- Pred = T → Prop, and P : Pred → T → Pred
section Approach1

variable (T : Type)

def Pred := T → Prop

-- A "predicate constructor" that takes a Pred and a T and returns a Pred
-- This is: (T → Prop) → T → (T → Prop)
def PredCons := T → Pred T

-- Pred Nat = Nat → Prop (unary)
example : Pred Nat := fun n => n > 0

-- PredCons Nat = Nat → Nat → Prop (binary — one more arg prepended)
example : PredCons Nat := fun x y => x > y

-- Ternary: T → PredCons T = T → T → T → Prop
def PredCons2 := T → PredCons T
example : PredCons2 Nat := fun x y z => x + y > z

end Approach1


-- Approach 2: Inductive type for variable arity
section Approach2

inductive VPred (T : Type) : Type 1 where
  | base : Prop → VPred T
  | ext  : (T → VPred T) → VPred T

-- Can we evaluate a VPred?
def VPred.eval : VPred T → Prop
  | .base p => p
  | .ext f => ∀ (x : T), (f x).eval

-- Unary predicate: ∀ x, x > 0
def unary_pred : VPred Nat := .ext (fun n => .base (n > 0))

-- Binary predicate: ∀ x y, x > y
def binary_pred : VPred Nat := .ext (fun x => .ext (fun y => .base (x > y)))

-- Ternary: ∀ x y z, x + y > z
def ternary_pred : VPred Nat := .ext (fun x => .ext (fun y => .ext (fun z => .base (x + y > z))))

-- Check that eval works
#check unary_pred.eval    -- Prop
-- #eval won't work (Prop isn't decidable), but it type-checks

end Approach2


-- Approach 3: Type-level arity via natural numbers
section Approach3

def NPred (T : Type) : Nat → Type
  | 0     => Prop
  | n + 1 => T → NPred T n

-- Unary: T → Prop
example : NPred Nat 1 := fun n => n > 0

-- Binary: T → T → Prop
example : NPred Nat 2 := fun x y => x > y

-- Ternary: T → T → T → Prop
example : NPred Nat 3 := fun x y z => x + y > z

end Approach3
