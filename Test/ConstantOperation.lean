import Logic

/-!
# Smoke test for the `constant` macro

Exercises the constant-operation framework end-to-end on a stub graph,
confirming:
  1. The macro elaborates without error.
  2. The generated `_sym`, `_satisfies`, and noncomputable def are accessible.
  3. The `Coe` instance fires at use sites where `U.Particular` is expected.
  4. The graph's fields (`.pred`, `.cong`, `.ltot`, `.rdet`) are
     reachable via the generated operation.
  5. The derived `.def` and `.cong` theorems on the operation are accessible.

The stub Universal and stub characterizing predicate are introduced as
axioms purely to give the macro something to chew on — no mathematical
content is intended.

Type-level checks use `noncomputable example` because some examples produce
values of type `U.Particular` (a Type, not Prop), which Lean's code
generator otherwise tries to compile and chokes on the underlying axioms.
-/

namespace Test

namespace ConstantOperationSmoke

open Logic
open Logic.PC₁

-- Stub Universal and stub characterizing predicate.
axiom U : Universal
axiom stub_pred : U.Particular → Prop
axiom stub_cong : ∀ (c₁: U.Particular), ∀ (c₂: U.Particular),
                    c₁ =₍U₎ c₂ → (stub_pred c₁ ↔ stub_pred c₂)
axiom stub_existence : ∃ (c: U.Particular), stub_pred c
axiom stub_uniqueness : ∀ (c₁: U.Particular), ∀ (c₂: U.Particular),
                          stub_pred c₁ ∧ stub_pred c₂ → c₁ =₍U₎ c₂

-- Build the graph via the smart constructor.
noncomputable def stub_graph : ConstantOperationGraph U :=
  ConstantOperationGraph.fromCongPred
    { pred := stub_pred, cong := stub_cong }
    stub_existence
    stub_uniqueness

-- Apply the macro.
constant stub_const : U from stub_graph

-- (1) Generated axioms are accessible.
noncomputable example : U.Particular := stub_const_sym
example : stub_graph.pred stub_const_sym := stub_const_satisfies

-- (2) The noncomputable def is a ConstantOperation.
noncomputable example : ConstantOperation U := stub_const

-- (3) Coe fires — stub_const usable wherever U.Particular is expected.
noncomputable example : U.Particular := stub_const
noncomputable example : U.Particular := ↑stub_const

-- (4) Field access through the operation.
noncomputable example : ConstantOperationGraph U := stub_const.graph
noncomputable example : U.Particular := stub_const.op
example : stub_const.graph.pred stub_const.op := stub_const.satisfies

-- (5) Graph fields (pred, ltot, rdet) reachable through the op.
example : U.Particular → Prop := stub_const.graph.pred
example : ∃ (c: U.Particular), stub_const.graph.pred c := stub_const.graph.ltot
example : ∀ (c₁: U.Particular), ∀ (c₂: U.Particular),
            stub_const.graph.pred c₁ ∧ stub_const.graph.pred c₂ → c₁ =₍U₎ c₂ :=
  stub_const.graph.rdet

-- (6) Derived cong theorem on the operation (0-arity collapse to reflexivity).
example : stub_const.op =₍U₎ stub_const.op := stub_const.cong

-- (7) Derived def theorem on the operation (recovers the iff form).
example : ∀ (c: U.Particular), (stub_const.op =₍U₎ c) ↔ stub_const.graph.pred c :=
  stub_const.«def»

end ConstantOperationSmoke

end Test
