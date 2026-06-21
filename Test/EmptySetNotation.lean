import Universals.Sets
import Universals.Sets.Predicates.Unary.EmptySetGraph
import Universals.Sets.Operations.Constants.EmptySet.Constant

/-!
# Summary of findings

The current notation `notation "∅ₛₑₜ" => empty_set.op` fixed point-use
inference (where one side of an operator provides the Universal). The
two remaining proof-side ergonomic issues are FUNDAMENTAL Lean elaboration
limitations, not notation problems.

## Issue 1: `∅ₛₑₜ =ₛₑₜ ∅ₛₑₜ` — UNFIXABLE BY NOTATION

`=ₛₑₜ` expands to `_ =₍SetsUniversal _₎ _`. With both arguments being `∅ₛₑₜ`
(implicit U) and no surrounding context to pin U, Lean has zero handles to
infer the Universal. No notation tweak can manufacture context that isn't
there. The user-side fix `=₍𝐒𝐞𝐭 U₎` is the right answer — and it's only
needed when both sides of an equality are U-less constants.

## Issue 2: `empty_set_graph.pred ∅ₛₑₜ` — UNFIXABLE WITHOUT FRAMEWORK CHANGE

`empty_set_graph.pred` desugars to a chain of projections:
  `@CongruentUnaryPredicate.pred (𝐒𝐞𝐭 ?m₁)
     (@ConstantOperationGraph.toCongruentUnaryPredicate (𝐒𝐞𝐭 ?m₂) empty_set_graph)
     empty_set.op`

The implicit `?m₁` and `?m₂` (and the U in `empty_set.op`) are SUPPOSED to all
unify with the iff's pinned-U on the LHS. They don't, because Lean's
goal-elaboration of `(LHS =₍𝐒𝐞𝐭 U₎ ...) ↔ <RHS with implicit Us>` doesn't
flow constraints from LHS to RHS reliably. Direct use of
`empty_set_graph_pred (U := U)` sidesteps the projection chain entirely.

This isn't `∅ₛₑₜ`'s fault. The same issue would arise with `empty_set.op`
notation, `∅ₛₑₜ.graph.pred` shorthand, or any expression that goes through
multiple structure projections with implicit-U fields.

## What CAN'T help (verified)

| Notation tweak | Does it help? |
|---|---|
| `@empty_set _` instead of `empty_set` | No |
| `(empty_set : (𝐒𝐞𝐭 _).Particular)` | No |
| `(empty_set.op : (𝐒𝐞𝐭 _).Particular)` | No |
| Custom `=ₛₑₜ` alias | No |

## What CAN help — three options, none ideal

**Option A** (current — what the user is doing): live with `=₍𝐒𝐞𝐭 U₎`
and `empty_set_graph_pred (U := U)` in proofs that touch self-symmetric
constant equalities or direct graph.pred projections. Verbose but correct.

**Option B** (framework change): change the `constant` macro to ALSO
emit a precomputed `<name>_satisfies : <name>_graph.pred <name>_sym`
theorem. The macro proves it once (where U is in scope and inferrable
from the named arguments) and consumers use `forall_elim <name>_satisfies`
instead of unfolding via the iff + reflexivity dance. Eliminates the
recurrence the user is worried about.

**Option C** (different framework change): change the macro's def axiom
to NOT reference `$graph.pred` directly but instead reference the raw
predicate body. Requires the macro to accept the raw `graph_pred` def
name as a separate argument (since it can't unfold the graph at expansion
time). Larger API change.

## Recommendation

**Option B** — add a precomputed satisfaction theorem to the `constant`
macro output. Justification:
- Eliminates the `empty_set_graph_pred (U := U)` pattern from every
  consumer proof.
- Doesn't break the existing macro API.
- Pattern generalizes to unary/binary operations too (where the
  consumer often wants `<name>.graph.pred (arguments) (<name> arguments)`
  by reflexivity).
- The `=ₛₑₜ` issue remains, but it's rare in practice (only matters
  when two sides of the equality are the same U-less constant).
-/

namespace Test

namespace Findings

open Universe Universe.Sets Logic Logic.PC₁


-- # PROOF OF CONCEPT for Option B
-- A precomputed "empty_set_satisfies" theorem. With U in scope at definition
-- time and the named-arg pattern, U is inferrable.
example {U: Universal}: empty_set_graph_pred (U := U) ∅ₛₑₜ := by
  have h₁: ∀ (c: (𝐒𝐞𝐭 U).Particular), (empty_set.op =₍𝐒𝐞𝐭 U₎ c) ↔ empty_set_graph_pred (U := U) c :=
    empty_set.«def»
  have h₂: (empty_set.op =₍𝐒𝐞𝐭 U₎ empty_set.op) ↔ empty_set_graph_pred (U := U) empty_set.op := by
    forall_elim h₁, empty_set.op
  have h₃: empty_set.op =₍𝐒𝐞𝐭 U₎ empty_set.op := by forall_elim (𝐒𝐞𝐭 U).eq.refl, empty_set.op
  have h₄: empty_set_graph_pred (U := U) empty_set.op := PC₀.deductive_eq_l2r h₂ h₃
  iterate h₄

-- # USING the satisfies theorem, the consumer proof becomes one line:
example {U: Universal} (eu_pred: empty_set_graph_pred (U := U) ∅ₛₑₜ):
    ∀ (x: U.Particular), x ∉ₛₑₜ ∅ₛₑₜ := by forall_intro
  variable(u: U.Particular)
  -- empty_set_graph_pred ∅ₛₑₜ ≡ ∀ x, x ∉ₛₑₜ ∅ₛₑₜ via @[reducible] reduction.
  have h₁: u ∉ₛₑₜ ∅ₛₑₜ := by forall_elim eu_pred, u
  iterate h₁


end Findings

end Test
