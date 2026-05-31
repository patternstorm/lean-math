import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Properties
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Ternary.Properties

/-!
# Phase 1 verification: flat `CongruentBinaryPredicate` / `CongruentTernaryPredicate`

Each section sets up a test predicate (axioms + manual typeclass instances) and
then exercises one specific piece of the new schema/properties. Layout:

  1. Binary — typeclass coercion plumbing
  2. Binary — fiber → `CongruentUnary` auto-inference
  3. Binary — `CoeFun` chains `P x y`
  4. Binary — `congruent_binary_from_unary` derives the typeclass from per-arg unary
  5. Ternary — typeclass coercion plumbing
  6. Ternary — fiber (fix first) → `CongruentBinary` auto-inference
  7. Ternary — fiber (fix first two) → `CongruentUnary` auto-inference
  8. Ternary — `CoeFun` chains `P x y z`
  9. Ternary — `congruent_ternary_from_unary` derives the typeclass
 10. Unary — sanity: existing auto-cong (conjunction) is unaffected
 11. Composition — explicit construction of fiber values via the preservation theorems

If everything below compiles, the foundation is sound. Downstream consumers
of `CongruentBinaryPredicate` / `CongruentTernaryPredicate` will compile or
break in predictable, known ways (Phase 2-3 mechanical migration).
-/

namespace Test.FlatSchemas

open Logic
open Logic.PC₁

variable {U U₁ U₂ U₃ : Universal}

-- ═══════════════════════════════════════════════════════════════════
-- Section 1 — Binary: typeclass coercion plumbing
-- ═══════════════════════════════════════════════════════════════════
-- Setup: a binary predicate with manual inner+outer cong, registered as
-- an instance of `[CongruentBinary U₁ U₂]`.

axiom binP : U₁.Particular → U₂.Particular → Prop
axiom binP_inner_cong : ∀ (x: U₁.Particular), ∀ (y₁ y₂: U₂.Particular),
    y₁ =₍U₂₎ y₂ → (binP x y₁ ↔ binP x y₂)
axiom binP_outer_cong : ∀ (x₁ x₂: U₁.Particular), ∀ (z: U₂.Particular),
    x₁ =₍U₁₎ x₂ → (binP x₁ z ↔ binP x₂ z)

instance binP_congruent : CongruentBinary U₁ U₂ binP where
  inner_cong := binP_inner_cong
  outer_cong := binP_outer_cong

-- The typeclass synthesizes:
example : CongruentBinary U₁ U₂ binP := inferInstance

-- `combined_from_inner_outer` glues inner+outer into the combined cong shape
-- the structure expects. This is what the coercion uses internally.
example : CongruentBinaryPredicate U₁ U₂ :=
  { pred := binP, cong := binary_congruence_from_congruent_fibers binP_inner_cong binP_outer_cong }

-- ═══════════════════════════════════════════════════════════════════
-- Section 2 — Binary: fiber → CongruentUnary auto-inference
-- ═══════════════════════════════════════════════════════════════════
-- For any `P : CongruentBinaryPredicate U₁ U₂` and any `x : U₁.Particular`,
-- the unary body `fun y => P.pred x y` should be auto-inferred as `CongruentUnary`.

example (P : CongruentBinaryPredicate U₁ U₂) (x : U₁.Particular) :
    CongruentUnary U₂ (fun y => P.pred x y) := inferInstance

-- ═══════════════════════════════════════════════════════════════════
-- Section 3 — Binary: CoeFun chains `P x y`
-- ═══════════════════════════════════════════════════════════════════

example (P : CongruentBinaryPredicate U₁ U₂) (x : U₁.Particular) (y : U₂.Particular) : Prop := P x y

-- ═══════════════════════════════════════════════════════════════════
-- Section 4 — Binary: typeclass derivation from per-arg unary
-- ═══════════════════════════════════════════════════════════════════
-- Setup: a binary predicate whose fiber predicates (per-arg) are unary congruent.
-- The `congruent_binary_from_unary` instance derives `CongruentBinary` from these.

section
axiom Q1 : U₁.Particular → U₂.Particular → Prop
axiom Q1_per_x : ∀ (x : U₁.Particular), CongruentUnary U₂ (Q1 x)
axiom Q1_per_z : ∀ (z : U₂.Particular), CongruentUnary U₁ (fun x => Q1 x z)
attribute [instance] Q1_per_x Q1_per_z

example : CongruentBinary U₁ U₂ Q1 := inferInstance
end

-- ═══════════════════════════════════════════════════════════════════
-- Section 5 — Ternary: typeclass coercion plumbing
-- ═══════════════════════════════════════════════════════════════════

axiom terP : U₁.Particular → U₂.Particular → U₃.Particular → Prop
axiom terP_cong₁ : ∀ (x₁ x₂ : U₁.Particular), ∀ (y : U₂.Particular), ∀ (z : U₃.Particular),
    x₁ =₍U₁₎ x₂ → (terP x₁ y z ↔ terP x₂ y z)
axiom terP_cong₂ : ∀ (x : U₁.Particular), ∀ (y₁ y₂ : U₂.Particular), ∀ (z : U₃.Particular),
    y₁ =₍U₂₎ y₂ → (terP x y₁ z ↔ terP x y₂ z)
axiom terP_cong₃ : ∀ (x : U₁.Particular), ∀ (y : U₂.Particular), ∀ (z₁ z₂ : U₃.Particular),
    z₁ =₍U₃₎ z₂ → (terP x y z₁ ↔ terP x y z₂)

instance terP_congruent : CongruentTernary U₁ U₂ U₃ terP where
  cong₁ := terP_cong₁
  cong₂ := terP_cong₂
  cong₃ := terP_cong₃

example : CongruentTernary U₁ U₂ U₃ terP := inferInstance

example : CongruentTernaryPredicate U₁ U₂ U₃ :=
  { pred := terP, cong := ternary_cong_from_fibers terP_cong₁ terP_cong₂ terP_cong₃ }

-- ═══════════════════════════════════════════════════════════════════
-- Section 6 — Ternary: fiber (fix first) → CongruentBinary auto-inference
-- ═══════════════════════════════════════════════════════════════════

example (P : CongruentTernaryPredicate U₁ U₂ U₃) (x : U₁.Particular) :
    CongruentBinary U₂ U₃ (fun y z => P.pred x y z) := inferInstance

-- ═══════════════════════════════════════════════════════════════════
-- Section 7 — Ternary: fiber (fix first two) → CongruentUnary auto-inference
-- ═══════════════════════════════════════════════════════════════════

example (P : CongruentTernaryPredicate U₁ U₂ U₃) (x : U₁.Particular) (y : U₂.Particular) :
    CongruentUnary U₃ (fun z => P.pred x y z) := inferInstance

-- ═══════════════════════════════════════════════════════════════════
-- Section 8 — Ternary: CoeFun chains `P x y z`
-- ═══════════════════════════════════════════════════════════════════

example (P : CongruentTernaryPredicate U₁ U₂ U₃)
    (x : U₁.Particular) (y : U₂.Particular) (z : U₃.Particular) : Prop := P x y z

-- ═══════════════════════════════════════════════════════════════════
-- Section 9 — Ternary: typeclass derivation from per-arg unary
-- ═══════════════════════════════════════════════════════════════════

section
axiom Q2 : U₁.Particular → U₂.Particular → U₃.Particular → Prop
axiom Q2_per_yz : ∀ (y : U₂.Particular), ∀ (z : U₃.Particular),
    CongruentUnary U₁ (x : U₁.Particular ↦ Q2 x y z)
axiom Q2_per_xz : ∀ (x : U₁.Particular), ∀ (z : U₃.Particular),
    CongruentUnary U₂ (y : U₂.Particular ↦ Q2 x y z)
axiom Q2_per_xy : ∀ (x : U₁.Particular), ∀ (y : U₂.Particular),
    CongruentUnary U₃ (Q2 x y)
attribute [instance] Q2_per_yz Q2_per_xz Q2_per_xy

example : CongruentTernary U₁ U₂ U₃ Q2 := inferInstance
end

-- ═══════════════════════════════════════════════════════════════════
-- Section 10 — Unary: sanity check, existing auto-cong is unaffected
-- ═══════════════════════════════════════════════════════════════════
-- We did not touch `Unary/Schema.lean` or its `Properties/` files. The
-- existing structural auto-cong instances (conjunction, disjunction,
-- existential, negation) should still derive `CongruentUnary` typeclass
-- instances from compositions of congruent unary bodies. Quick sanity:
-- the conjunction of two congruent unary predicates is congruent.

section
axiom uP : U.Particular → Prop
axiom uQ : U.Particular → Prop
axiom uP_cong : CongruentUnary U uP
axiom uQ_cong : CongruentUnary U uQ
attribute [instance] uP_cong uQ_cong

-- Conjunction auto-cong:
example : CongruentUnary U (x : U.Particular ↦ uP x ∧ uQ x) := inferInstance
end

-- ═══════════════════════════════════════════════════════════════════
-- Section 11 — Composition: explicit fiber construction
-- ═══════════════════════════════════════════════════════════════════
-- The preservation theorems are public so consumers can construct a fiber as
-- a `CongruentBinaryPredicate` / `CongruentUnaryPredicate` value explicitly
-- when they want the structural view (e.g. for composing with unary tooling).

example (P : CongruentBinaryPredicate U₁ U₂) (x : U₁.Particular) : CongruentUnaryPredicate U₂ :=
  { pred := fun y => P.pred x y, cong := fiber_first_preserves_binary_congruence P x }

example (P : CongruentTernaryPredicate U₁ U₂ U₃) (x : U₁.Particular) : CongruentBinaryPredicate U₂ U₃ :=
  { pred := fun y z => P.pred x y z, cong := fiber_first_preserves_congruence P x }

example (P : CongruentTernaryPredicate U₁ U₂ U₃) (x : U₁.Particular) (y : U₂.Particular) : CongruentUnaryPredicate U₃ :=
  { pred := fun z => P.pred x y z, cong := fiber_first_two_preserves_congruence P x y }

end Test.FlatSchemas
