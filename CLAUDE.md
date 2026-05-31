# Lean-Math: Mathpunk Neo-Logicism

This is a Lean 4 project formalizing mathematics from first-order logic. Some structures (like sets) are **derived** from predicate logic. Others (like natural numbers) are **postulated** as initial objects, ADT-style, within typed FOL.

## Critical Rules

- **Never use Lean automation** (`simp`, `omega`, `decide`, `rfl`, `exact`, `apply`). All proofs use custom natural deduction tactics.
- **Never speculate** about code — read the files before making claims.
- **Don't repeat rejected edits** — stop and wait for guidance.
- **Authorship comments** on all Claude-written proofs: `-- Proof by Claude Opus 4.6 (claude-opus-4-6), YYYY-MM-DD`
- **Keep skills updated**: When making architectural decisions, adding new concepts, or establishing new patterns, update the relevant skills. Per-universal skills (like `lean-math-sets`) should be updated when adding new operations, predicates, or properties to that universal — they don't need to be exact, just an overview pointing to the code.
- **Compile with `lake env lean <file>`** during refactoring, not `lake build` (which outputs errors from unrelated files).

## Skills

Load the relevant skill before starting work:

- **`/lean-math-overview`** — Project architecture, philosophy, schemas, sub-universals, file structure. Start here for new sessions.
- **`/lean-math-proofs`** — Custom natural deduction tactics, proof patterns, congruence proofs.
- **`/lean-math-predicates`** — Named predicate macros (`unary_predicate`/`binary_predicate`), the `Congruent*Predicate` ↔ named-predicate layering, `CoeHead` upcast, auto-cong machinery (`CongruentUnary`/`CongruentBinary` typeclasses), fiber preservation theorems, and the named-arg use-site pattern.
- **`/lean-math-sets`** — The Set Universal: sets as predicates, membership, inclusion, powerset, stratification.
- **`/lean-math-dyads`** — The Dyad Universal: co-existence, predicate curry/uncurry, predicate associativity, `⋈` notation.
- **`/lean-math-conventions`** — Naming, file organization (ADT barrel pattern), notation, user preferences.
