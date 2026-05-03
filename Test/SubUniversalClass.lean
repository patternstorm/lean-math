import Universe
import Logic
import Universals.Sets.Definitions.SetsAsUniversals.Definition
import Universals.Dyads.Universal

/-!
# Prototype — `<:` as a typeclass

Goal: verify that promoting `SubUniversal` from a `structure` to a `class`
enables automatic composition of sub-universal witnesses via Lean's
typeclass resolution, collapsing the per-path `CoeDep` explosion into a
single generic coercion.

The production `<:` (a `structure`) is left untouched. We prototype with a
fresh class `SubUniversal'` (notation `<:'`) and `sorry`'d instance bodies
— TC resolution mechanics are independent of the mathematical bodies, so
`sorry` is legitimate here.

## What success looks like

Every one of the `#check` / `example` tests below must elaborate with no
"failed to synthesize instance" errors. Each success means TC resolution
composed a fresh proof of `A <:' B` on demand, for shapes that would have
required a dedicated `CoeDep` instance in the production architecture.
-/

namespace Universe
namespace TestClass

open Logic
open Logic.PC₁
open Sets
open Dyads

-- ============================================================
-- Prototype class
-- ============================================================

class SubUniversal' (U₁: Universal) (U₂: Universal): Type where
  embedding: U₁ ⟴ U₂
  preserves_eq: ∀ (x: U₁.Particular), ∀ (y: U₁.Particular),
    x =₍U₁₎ y ↔ (embedding x =₍U₂₎ embedding y)

notation:25 U₁:26 " <:' " U₂:26 => SubUniversal' U₁ U₂

-- ============================================================
-- Base instances
-- ============================================================

-- Reflexivity.
noncomputable instance subuniversal_refl' (U: Universal): U <:' U := sorry

-- Refined universals are sub-universals of their parent. Registered at the
-- CANONICAL shape `(U ↾ P)`, which subsumes every `↾`-alias in the codebase
-- (`set_as_universal S`, `FunctionUniversal`, `EqRelUniversal`, ...). Each
-- alias must be marked `@[reducible]` (or `abbrev`) so that TC resolution
-- unfolds it to `_ ↾ _` during instance matching.
noncomputable instance refined_universal_is_sub' {U: Universal}
    (P: CongruentUnaryPredicate U): (U ↾ P) <:' U := sorry

-- # On reducibility — the production fix
--
-- For TC resolution to unfold an `↾`-alias during instance matching, the
-- alias must be marked reducible AT ITS DEFINITION SITE. Empirically:
--
--   • `abbrev foo := ...`            → unfolds during TC matching ✓
--   • `@[reducible] def foo := ...`  → unfolds during TC matching ✓
--   • `def foo := ...` + retroactive `attribute [reducible] foo` → does NOT unfold ✗
--
-- So the production rollout MUST edit each alias's definition. The failure mode
-- documented in `SubUniversal/Schema.lean:108-112` was real; the fix is local.
--
-- Standing in for the production change `def set_as_universal := ...` →
-- `@[reducible] def set_as_universal := ...`, we declare a reducible proxy
-- here. (The production `set_as_universal` remains untouched in this prototype.)
@[reducible] def set_as_universal' {U: Universal} (S: Set U): Universal := U ↾ S
instance {U : Universal} (S : Set U) : CoeDep (Set U) S Universal where
  coe := set_as_universal' S

-- ============================================================
-- Composite instance — the whole point of the refactor.
-- Child witnesses travel as INSTANCE arguments, so TC resolution chains.
-- ============================================================

noncomputable instance dyad_sub' {U₁' U₁ U₂' U₂: Universal}
    [e₁: U₁' <:' U₁] [e₂: U₂' <:' U₂]:
    (U₁' ⧓ U₂') <:' (U₁ ⧓ U₂) := sorry

-- ============================================================
-- Single generic coercion — replaces ALL per-path `CoeDep` instances.
-- ============================================================

noncomputable instance generic_coe {U₁ U₂: Universal} [e: U₁ <:' U₂]
    (x: U₁.Particular): CoeDep U₁.Particular x U₂.Particular where
  coe := e.embedding x

-- ============================================================
-- Tests — each must elaborate cleanly.
-- ============================================================

-- The `examples` below route through `noncomputable` instance bodies, so
-- the whole block is wrapped in a `noncomputable section`.
noncomputable section

variable {U₁ U₂ U₃ U: Universal}

-- 1. Reflexivity base (no coercion — sanity check).
example (x: U.Particular): U.Particular := x

-- 2. Set-as-universal → parent.
example (S: Set U) (x: (set_as_universal' S).Particular): U.Particular := x

-- 3. Left-only dyad (was `subsumptivity_left` coercion).
example (S: Set U₁) (d: (set_as_universal' S ⧓ U₂).Particular):
    (U₁ ⧓ U₂).Particular := d

-- 4. Right-only dyad (was `subsumptivity_right` coercion).
example (S: Set U₂) (d: (U₁ ⧓ set_as_universal' S).Particular):
    (U₁ ⧓ U₂).Particular := d

-- 5. Both-sides dyad (was `subsumptivity` coercion).
example (S₁: Set U₁) (S₂: Set U₂)
    (d: (S₁ ⧓ S₂).Particular):
    (U₁ ⧓ U₂).Particular := d

-- 6. Nested dyad — the real scalability test. Two levels of composite
-- universals, mixing a sub-universal with a refl inside a nested dyad.
-- In the current architecture this would require an additional CoeDep
-- instance at the outer level; here it falls out of TC resolution.
example (S₁: Set U₁) (S₂: Set U₂)
    (d: ((S₁ ⧓ S₂) ⧓ U₃).Particular):
    ((U₁ ⧓ U₂) ⧓ U₃).Particular := d

-- 7. Direct instance synthesis checks — verify TC resolution finds the
-- composite witness independently of any coercion.
section
variable (S: Set U) (S₁: Set U₁) (S₂: Set U₂)

#check (inferInstance: U <:' U)
#check (inferInstance: S <:' U)
#check (inferInstance: ( S₁ ⧓  S₂) <:' (U₁ ⧓ U₂))
#check (inferInstance: ( S₁ ⧓ U₂) <:' (U₁ ⧓ U₂))
#check (inferInstance: (U₁ ⧓  S₂) <:' (U₁ ⧓ U₂))
#check (inferInstance: (( S₁ ⧓  S₂) ⧓ U₃) <:' ((U₁ ⧓ U₂) ⧓ U₃))
end

end  -- noncomputable section

end TestClass
end Universe

/-!

Revised production rollout
Smaller and cleaner than the original sketch:

Schema swap — structure SubUniversal → class SubUniversal. Convert explicit (e: U' <: U) args to [e: U' <: U] where useful (or leave explicit; both work).
Mark ↾-aliases reducible at the definition site. One-line edit per alias:
Definition.lean:18 — def set_as_universal → @[reducible] def set_as_universal
Universal.lean:15 — same treatment for FunctionUniversal
Universal.lean:17 — EqRelUniversal
Universal.lean:17 — PEqRelUniversal
Universal.lean:17 — SingletonSetUniversal
Base instances at canonical shapes. Re-mark as instance:
subuniversal_refl: U <: U
refined_universal_is_sub: (U ↾ P) <: U (canonical — covers all aliases)
Composite instances — subsumptivity for dyads (and the analogues for relations/correspondences) re-marked as instance with [...] child args. Drop _left / _right instance variants.
One global generic CoeDep near the SubUniversal schema. Delete every per-path CoeDep instance — including the three I just added in Subsumptivity.lean:122-129 and the existing one at Subsumptivity.lean:62-63.
Net effect
For every refined universal — singleton sets, equivalence relations, partial equivalence relations, function universals, and any future composite — the ↑ coercion to the parent universal will work automatically, with zero further coercion plumbing.

-/
