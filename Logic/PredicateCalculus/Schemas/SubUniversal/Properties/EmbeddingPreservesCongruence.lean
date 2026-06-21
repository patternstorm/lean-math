import Logic.PredicateCalculus.Schemas.SubUniversal.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Unary.Schema
import Logic.PredicateCalculus.Schemas.CongruentPredicates.Binary.Instances.Equals
import Logic.PredicateCalculus.Definitions.StatementTemplate.Definition
import Logic.NaturalDeduction.Rules
import Logic.PropositionalCalculus

namespace Logic

namespace PC₁


-- # Embedding preserves congruence
--
-- If `P : CongruentUnaryPredicate U` is congruent on `U` and `e : U' <: U`
-- is a sub-universal embedding, then the lifted body `(x' ↦ P (e.embedding x'))`
-- is congruent on `U'`. Proof chains `e.preserves_eq` (lifting `=₍U'₎` to
-- `=₍U₎` on the embedded particulars) with `P.cong`.
--
-- Proof by Claude Opus 4.7 (claude-opus-4-7), 2026-06-21
def embedding_preserves_congruence {U' U: Universal} (e: U' <: U) (P: CongruentUnaryPredicate U): CongruentUnaryPredicate U' :=
  let pred: U'.Particular → Prop := (x': U'.Particular ↦ P (e.embedding x'))
  let cong: ∀ (a: U'.Particular), ∀ (b: U'.Particular), a =₍U'₎ b → (pred a ↔ pred b) := by forall_intro
    variable(a: U'.Particular)
    variable(b: U'.Particular)
    assume(h₁: a =₍U'₎ b)
    have h₂: a =₍U'₎ b ↔ (e.embedding a =₍U₎ e.embedding b) := by forall_elim e.preserves_eq, a, b
    have h₃: e.embedding a =₍U₎ e.embedding b := PC₀.deductive_eq_l2r h₂ h₁
    have h₄: ∀ (y: U.Particular), e.embedding a =₍U₎ y → (P (e.embedding a) ↔ P y) := by forall_elim P.cong, (e.embedding a)
    have h₅: e.embedding a =₍U₎ e.embedding b → (P (e.embedding a) ↔ P (e.embedding b)) := by forall_elim h₄, (e.embedding b)
    have h₆: P (e.embedding a) ↔ P (e.embedding b) := by modus_ponens h₅, h₃
    iterate h₆
  { pred := pred, cong := cong }

-- Auto-cong instance: lifts `CongruentUnary U P` through a sub-universal
-- embedding `[U' <: U]`. Closes the synthesis gap for graph predicates whose
-- first argument lives in a refined / sub-universal — bodies like
-- `(fun S y => y ∈ₛₑₜ S)` with `S : 𝐒𝐢𝐧𝐠𝐥𝐞𝐭𝐨𝐧𝐒𝐞𝐭 U` previously required a
-- hand-written cong proof; with this instance they auto-derive.
instance congruent_through_subuniversal_embedding
    {U' U: Universal} [e: U' <: U]
    {P: U.Particular → Prop} [p: CongruentUnary U P]:
    CongruentUnary U' (x': U'.Particular ↦ P (e.embedding x')) where
  cong := (embedding_preserves_congruence e { pred := P, cong := p.cong }).cong


end PC₁

end Logic
