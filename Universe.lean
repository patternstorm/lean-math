import Logic

/-!
# Universe

We want to reason about things by constructing verifiable statements - called *Predicates* - about them.
These things - called *Particulars* - can be any entities we choose to consider.

Crucially, we represent *Particulars* through well-defined syntactic entities - called *Terms* -,
constructed by precise formation rules we call *Types*. Each *Type* defines what counts as
a well-formed *Particular* representation (valid *Term*).

The *Universe* of our discourse is completely determined by the *Type* that
constructs representations, i.e. *Terms*, of the *Particulars* we want to consider.
-/

namespace Universe

/-! The *Polypomphic Equality* of *Particulars* in our *Universe*
def equality : Equality X :=
  let eq : X → X → Prop := eq_poly
  let refl : ∀ (x : X), x =ₚ x := by forall_intro
    variable(u: X)
    have h₁: u =ₚ u := by forall_elim eq_poly_refl, u
    iterate h₁
  let sym : ∀ (x y : X), x =ₚ y → y =ₚ x := by forall_intro
    variable(u: X)
    variable(v: X)
    have h₁: ∀ (y: X), u =ₚ y → y =ₚ u := by forall_elim eq_poly_sym, u
    have h₂: u =ₚ v → v =ₚ u := by forall_elim h₁, v
    iterate h₂
  let trans : ∀ (x y z : X), x =ₚ y ∧ y =ₚ z → x =ₚ z := by forall_intro
    variable(u: X)
    variable(v: X)
    variable(w: X)
    have h₁: ∀ (y: X), ∀ (z: X), u =ₚ y ∧ y =ₚ z → u =ₚ z := by forall_elim eq_poly_trans, u
    have h₂: ∀ (z: X), u =ₚ v ∧ v =ₚ z → u =ₚ z := by forall_elim h₁, v
    have h₃: u =ₚ v ∧ v =ₚ w → u =ₚ w := by forall_elim h₂, w
    iterate h₃
  { pred := eq
    refl := refl
    sym := sym
    trans := trans }

def Universe: Universal := {
  Particular := X
  eq := equality X
}
-/

end Universe
