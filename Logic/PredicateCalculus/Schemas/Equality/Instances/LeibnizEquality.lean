import Logic.NaturalDeduction
import Logic.PredicateCalculus.Definitions
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁


-- # Leibniz Equality
-- Syntactic identity of terms: the fundamental notion of equality from first-order logic,
-- distinct from Universal-specific equalities (=ₙₐₜ, =ₛₑₜ, etc.).
--
-- Leibniz equality is axiomatized by two principles. Reflexivity is the foundation:
-- it introduces equality by declaring that a term is the same as itself. This
-- sameness is what allows formulating the second principle, substitutability: equal
-- terms can replace each other in any predicate. Symmetry and transitivity are then
-- derived from these two axioms alone. In our framework, where objects are
-- syntactically constructed terms, this sameness is syntactic identity.
--
-- Note that Leibniz equality is typed (both arguments must belong to the same
-- type X). This is intentional: even if two terms from different types happen to
-- share the same syntactic representation, they are not considered equal.
--
-- In the framework, Leibniz equality plays two roles:
-- (1) It is used in exhaustiveness induction axioms to establish proof by cases
--     for opaque axiom types (whose constructors are axioms, not Lean inductives).
-- (2) It bootstraps Universal equalities: proving that the constructor axioms
--     (impurifier equations) of an ADT yield an equivalence relation requires
--     case analysis with substitution power. Without Leibniz equality, the proofs
--     of symmetry and transitivity for a Universal equality like =ₙₐₜ are circular
--     — they need to substitute constructor forms into formulas, which is exactly
--     what Leibniz substitution provides.
--
-- The quantifications over X : Type and P : X → Prop are NOT second-order logic.
-- These are axiom schemas: X and P are schema parameters. Each concrete type and
-- concrete predicate produces a first-order axiom instance. Lean's ∀ is type-theoretic
-- machinery encoding what would be syntactic substitution on paper. This is how equality
-- is standardly defined in first-order logic.
axiom leibniz_eq {X: Type}: X → X → Prop
notation:50 a:51 " 🟰 " b:51 => leibniz_eq a b

axiom leibniz_eq_refl: ∀ {X: Type}, ∀ (x: X), x 🟰 x

axiom leibniz_eq_subs: ∀ {X: Type}, ∀ (P: X → Prop), ∀ (x: X), ∀ (y: X), x 🟰 y → (P x ↔ P y)

theorem leibniz_eq_sym: ∀ {X: Type}, ∀ (x: X), ∀ (y: X), x 🟰 y → y 🟰 x := by forall_intro
  variable(X: Type)
  variable(a: X)
  variable(b: X)
  let pred: X → Prop := (x: X ↦ b 🟰 x)
  have h₁: ∀ (x: X), ∀ (y: X), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
  have h₂: ∀ (y: X), a 🟰 y → (pred a ↔ pred y) := by forall_elim h₁, a
  have h₃: a 🟰 b → (b 🟰 a ↔ b 🟰 b) := by forall_elim h₂, b
  assume(h₄: a 🟰 b)
  have h₅: (b 🟰 a) ↔ (b 🟰 b) := by modus_ponens h₃, h₄
  have h₆: b 🟰 b := by forall_elim leibniz_eq_refl, b
  have h₇: b 🟰 a := PC₀.deductive_eq_r2l h₅ h₆
  iterate h₇

theorem leibniz_eq_trans: ∀ {X: Type}, ∀ (x: X), ∀ (y: X), ∀ (z: X), x 🟰 y ∧ y 🟰 z → x 🟰 z := by forall_intro
  variable(X: Type)
  variable(a: X)
  variable(b: X)
  variable(c: X)
  let pred: X → Prop := (x: X ↦ x 🟰 c)
  have h₁: ∀ (x: X), ∀ (y: X), x 🟰 y → (pred x ↔ pred y) := by forall_elim leibniz_eq_subs, pred
  have h₂: ∀ (y: X), a 🟰 y → (a 🟰 c ↔ y 🟰 c) := by forall_elim h₁, a
  have h₃: a 🟰 b → (a 🟰 c ↔ b 🟰 c) := by forall_elim h₂, b
  assume(h₄: a 🟰 b ∧ b 🟰 c)
  have h₅: b 🟰 c := by and_elim h₄
  have h₆: a 🟰 b := by and_elim h₄
  have h₇: a 🟰 c ↔ b 🟰 c := by modus_ponens h₃, h₆
  have h₈: a 🟰 c := PC₀.deductive_eq_r2l h₇ h₅
  iterate h₈

def leibniz_equality (X: Type) : Equality X :=
  { pred := leibniz_eq,
    refl := leibniz_eq_refl,
    sym := leibniz_eq_sym,
    trans := leibniz_eq_trans }

end PC₁
end Logic
