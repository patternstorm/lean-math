# Notation-Move Refactor — Resume Plan

**Status**: Mid-refactor. Build is broken on **2 files**. The recovery is a file-by-file walk through framework files that import `Universal.Schema` directly.

## What we're doing and why

We're moving the `=₍U₎` notation declaration from [`Logic/PredicateCalculus/Schemas/Universal/Schema.lean`](../../Logic/PredicateCalculus/Schemas/Universal/Schema.lean) (upstream) to [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Instance.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Instance.lean) (downstream), so that the notation expands via `@equals` (the `CongruentBinaryPredicate U U` value) instead of via the raw `universal_eq U` function.

This unifies equality auto-cong with how every other named predicate works: bodies using `=₍U₎` elaborate to `equals.pred ...` form, which the standard `fiber_*_binary_congruent_unary equals` instance pattern-matches against directly — no bridge instances needed.

**Empirical confirmation** that the design works lives in [`Test/EqualityNotationMoveHypothesis.lean`](../../Test/EqualityNotationMoveHypothesis.lean) — 12 test cases, all passing with bridge instances disabled.

## Foundational changes — DONE, do not redo

These are completed and the framework is in this state:

- [`Logic/PredicateCalculus/Schemas/Equality/Schema.lean`](../../Logic/PredicateCalculus/Schemas/Equality/Schema.lean): added `Equality.cong` derived theorem (generic over `X`, from sym+trans) AND `CoeFun` instance on `Equality X` (so `eq x y` works as `eq.pred x y`).
- [`Logic/PredicateCalculus/Schemas/Universal/Schema.lean`](../../Logic/PredicateCalculus/Schemas/Universal/Schema.lean): stripped — only contains `structure Universal`. NO `universal_eq` def, NO `=₍U₎` notation.
- [`Logic/PredicateCalculus/Schemas/Universal.lean`](../../Logic/PredicateCalculus/Schemas/Universal.lean) (barrel): also imports `Equals.Instance` now.
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Instance.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Instance.lean):
  - Defines `equals : CongruentBinaryPredicate U U := { pred := U.eq.pred, cong := U.eq.cong }`.
  - Defines the new `=₍U₎` notation: `notation:50 a:51 " =₍" U:51 "₎ " b:51 => @equals U a b`.
  - Still has commented-out `equal_to`/`equal_from` fibers and `congruent_equal_to`/`congruent_equal_from` bridge instances. These need to be **deleted** at the end (they're dead weight after the notation move).

## The mistake to recover from

I ran a perl substitution `=₍U₎ → U.eq` across all framework files that used `=₍U₎`. This was overzealous:
- For files **strictly upstream** of `Equals.Instance` (can't import it without cycle), the substitution is correct and necessary.
- For files **not in the upstream cycle**, the substitution was unnecessary — they could have just imported `Equals.Instance` and kept the cleaner `=₍U₎` notation.
- For 2 files with compound expressions like `op x =₍U₂₎ op y`, the substitution produced broken `op U₂.eq x op y` because the regex only captured single tokens.

## ⚠ Scope of corruption — code vs comments

The perl substitution `(\S+) =₍(\S+)₎ (\S+) → $2.eq $1 $3` affected both code and comments uniformly. Important distinction:

- **Code**: Lean's type system enforces correctness. Any file that currently compiles has semantically correct code — there is no silent corruption hiding in compiled-but-wrong proofs. If a substitution produced something type-incorrect, the file would not compile.
- **Comments**: not type-checked. A substitution that mangled documentation will survive the build silently. When restoring a file, also fix `U.eq` references inside comments (search the whole file, including `--` and `/-! ... -/` blocks).

Also be careful **not to over-revert legitimate `U.eq` field accesses** that pre-existed the substitution:
- `U.eq.refl`, `U.eq.sym`, `U.eq.trans` — these are field projections on the `Equality` struct, not from my substitution. Leave them alone.
- `U.eq.cong` — same; this is the derived theorem on `Equality`. Leave alone.
- `U.eq.pred` — explicit field projection of the predicate. Leave alone.

Only `U.eq X Y` patterns (taking two argument particulars) come from my substitution of `X =₍U₎ Y`. Those are the ones to revert to notation.

## The recovery algorithm (file by file, no batches)

For each file that imports `Logic.PredicateCalculus.Schemas.Universal.Schema` (the schema directly), do this **one file at a time**:

1. **Read the file** to see its current state.
2. **Add the import**: `import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals` (at the top).
3. **Run** `lake build <module>` for that specific file. **Choose path based on result**:
   - **If it compiles** (no cycle): file is NOT strictly upstream.
     - Restore `=₍U₎` notation throughout (revert any `U.eq X Y` → `X =₍U₎ Y` patterns I introduced).
     - For compound expressions where I broke things (`op U₂.eq x op y`), restore to `op x =₍U₂₎ op y`.
     - Keep the new Equals import.
     - Re-build to confirm clean.
   - **If it fails with import cycle**: file IS strictly upstream.
     - Remove the Equals import just added.
     - Keep the `U.eq` substitution (it was correct for this file).
     - If theorems lose auto-bound `U`, add explicit `{U: Universal}` to signatures.
     - Re-build to confirm clean.
4. **Move to the next file** only after the current one builds clean.

## Priority order — start with the 2 broken files

These currently FAIL compilation:

### 1. [`Logic/PredicateCalculus/Schemas/CongruentOperations/Unary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentOperations/Unary/Schema.lean)
- Corruption on line 9: `cong: ... U₁.eq x y → (op U₂.eq x op y)`
- Original was: `cong: ... x =₍U₁₎ y → (op x =₍U₂₎ op y)`
- After adding Equals import — restore both `=₍U₎` patterns.

### 2. [`Logic/PredicateCalculus/Schemas/Operations/Unary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/Operations/Unary/Schema.lean)
- Already has the Equals import (added during testing).
- Multiple corrupted patterns around lines 45, 69, 75-77, 81-82, 87-89, 92-93.
- All have shape `op U₂.eq <tok1> op <tok2>` or `op U₂.eq <tok1> <tok2>` — restore to original `op <tok1> =₍U₂₎ op <tok2>` or `op <tok1> =₍U₂₎ <tok2>`.

## Then process every other affected file in this list

These are all the files that import `Universal.Schema` directly (i.e., would have been affected by my substitution). For each, run the algorithm above:

### Likely NOT in upstream cycle (will accept Equals import, restore `=₍U₎`):

- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/UnaryOperationGraph/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/UnaryOperationGraph/Schema.lean) — already has the Equals import
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Properties/LeftTotality.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Properties/LeftTotality.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Properties/RightDeterminacy.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Properties/RightDeterminacy.lean) — already fixed with `{U: Universal}` + `U.eq`; can revert to `=₍U₎` if Equals import added
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Schema.lean) (47 occurrences)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Properties/FiberFirstPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Properties/FiberFirstPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Properties/FiberFirstTwoPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Properties/FiberFirstTwoPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Instances/BinaryOperationGraph/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Ternary/Instances/BinaryOperationGraph/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentOperations/Binary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentOperations/Binary/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/Operations/Binary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/Operations/Binary/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/Operations/Unary/Instances/Identity/Operation.lean`](../../Logic/PredicateCalculus/Schemas/Operations/Unary/Instances/Identity/Operation.lean)
- [`Logic/PredicateCalculus/Schemas/Operations/Unary/Instances/Identity/Properties/Invariance.lean`](../../Logic/PredicateCalculus/Schemas/Operations/Unary/Instances/Identity/Properties/Invariance.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Schema.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Predicates/SubsumptionGraph/Predicate.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Predicates/SubsumptionGraph/Predicate.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Predicates/SubsumptionGraph/Properties/LeftTotality.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Predicates/SubsumptionGraph/Properties/LeftTotality.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Predicates/SubsumptionGraph/Properties/RightDeterminacy.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Predicates/SubsumptionGraph/Properties/RightDeterminacy.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Operations/Unary/Subsumption/Operation.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Operations/Unary/Subsumption/Operation.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Operations/Unary/Subsumption/Properties/Equations.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Operations/Unary/Subsumption/Properties/Equations.lean)
- [`Logic/PredicateCalculus/Schemas/RefinedUniversal/Properties/Subsumptivity.lean`](../../Logic/PredicateCalculus/Schemas/RefinedUniversal/Properties/Subsumptivity.lean)
- [`Logic/PredicateCalculus/Schemas/SubUniversal/Schema.lean`](../../Logic/PredicateCalculus/Schemas/SubUniversal/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/SubUniversal/Properties/Reflexivity.lean`](../../Logic/PredicateCalculus/Schemas/SubUniversal/Properties/Reflexivity.lean)
- [`Logic/PredicateCalculus/Schemas/Equality/Properties/LeibnizEqualityImpliesUniversalEquality.lean`](../../Logic/PredicateCalculus/Schemas/Equality/Properties/LeibnizEqualityImpliesUniversalEquality.lean)
- [`Logic/PredicateCalculus/Definitions/Predicates/Binary/Definition.lean`](../../Logic/PredicateCalculus/Definitions/Predicates/Binary/Definition.lean)
- [`Logic/PredicateCalculus/Definitions/Operations/Unary/Definition.lean`](../../Logic/PredicateCalculus/Definitions/Operations/Unary/Definition.lean)
- [`Logic/PredicateCalculus/Definitions/Operations/Binary/Definition.lean`](../../Logic/PredicateCalculus/Definitions/Operations/Binary/Definition.lean)
- [`Logic/PredicateCalculus/Definitions/ExistsUnique/Definition.lean`](../../Logic/PredicateCalculus/Definitions/ExistsUnique/Definition.lean)

### Likely IN upstream cycle (will reject Equals import, must use `U.eq`):

These files I already substituted to `U.eq`. Run the algorithm on each anyway to **confirm** they're upstream and the substitution is correct (and add `{U: Universal}` if auto-bound fails):

- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ConjunctionPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ConjunctionPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/DisjunctionPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/DisjunctionPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ExistentialPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ExistentialPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ExistsUniquePreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ExistsUniquePreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/IffPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/IffPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ImplicationPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/ImplicationPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/NegationPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/NegationPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/PropositionalEquivalencePreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/PropositionalEquivalencePreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/UniversalPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Properties/UniversalPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/Constant.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/Constant.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/True.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/True.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/False.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Unary/Instances/False.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Schema.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Schema.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/BinaryCongruenceFromCongruentFibers.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/BinaryCongruenceFromCongruentFibers.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/FiberFirstPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/FiberFirstPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/FiberSecondPreservesCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/FiberSecondPreservesCongruence.lean)
- [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/PropositionalEquivalencePreservesBinaryCongruence.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Properties/PropositionalEquivalencePreservesBinaryCongruence.lean)

## Final cleanup (only after every file above is processed and the build is green)

1. **Verify full build**:
   ```bash
   lake build Universals.Sets
   ```
   Should be 197-198 jobs clean.

2. **Run the regression test**:
   ```bash
   lake env lean Test/EqualityNotationMoveHypothesis.lean
   ```
   Should exit 0.

3. **Delete dead code in [`Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Instance.lean`](../../Logic/PredicateCalculus/Schemas/CongruentPredicates/Binary/Instances/Equals/Instance.lean)**: remove the commented-out `equal_to` / `equal_from` defs and `congruent_equal_to` / `congruent_equal_from` instances. The file should end up containing only:
   - `equals : CongruentBinaryPredicate U U := { pred := U.eq.pred, cong := U.eq.cong }`
   - The `=₍U₎` notation declaration

4. **Optionally delete** [`Test/EqualityReducibilityHypothesis.lean`](../../Test/EqualityReducibilityHypothesis.lean) (created during testing, no longer needed).

5. **Keep** [`Test/EqualityNotationMoveHypothesis.lean`](../../Test/EqualityNotationMoveHypothesis.lean) as a regression test.

6. **Update skill docs** (`lean-math-predicates`): the pitfall about `=₍U₎` notation not auto-cong-ing is obsolete now — equality bodies auto-cong uniformly.

## How to resume in a fresh session

1. Read this document.
2. Read [`Test/EqualityNotationMoveHypothesis.lean`](../../Test/EqualityNotationMoveHypothesis.lean) to refresh on the empirical foundation.
3. Run `lake build Logic.PredicateCalculus 2>&1 | grep -E "^error: Logic" | sed 's/^error: //' | sed 's/:.*//' | sort -u` to see currently-broken files.
4. Start with the 2 broken files (`CongruentOperations/Unary/Schema.lean` and `Operations/Unary/Schema.lean`) — apply the recovery algorithm to each.
5. Continue through the rest of the affected files list, one at a time.
6. Once all files compile, do the final cleanup.

## Confidence

The design is sound — proven empirically by `Test/EqualityNotationMoveHypothesis.lean`. The execution requires careful file-by-file handling. NEVER batch-substitute again — the regex was too greedy on compound expressions like `op x =₍U₂₎ op y`.
