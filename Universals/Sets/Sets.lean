import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Definitions.SetComprehension.Definition
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Inclusion.Predicate
import Universals.Sets.Operations.Constants.UniversalSet.Constant
import Universals.Sets.Properties.EmptySetExistence
import Universals.Sets.Operations.Unary.Powerset.Operation
import Universals.Sets.Universals.Singleton.Universal

open Logic
open Logic.PC₁
open Logic.ND
open Universe.Sets




-- # Foundational `Sets`


-- # Set operations.

-- The union of the `Sets` `A` and `B` is a `Set` defined by the predicate `P₍a₎(x) ∨ P₍b₎(x)`.
def union (A B: Set X): Set X := { x: X.Particular | A.pred x ∨ B.pred x }
infixl:65 " ∪ₛₑₜ " => union

-- The complementary of `Set` `A` is the `Set` defined by the `Predicate` `¬P₍a₎`.
def compl (A: Set X): Set X := { x: X.Particular | ¬(A.pred x) }
prefix:max "¬ₛₑₜ" => compl

-- The intersection of the `Sets` `A` and `B` is a `Set` defined by the predicate `P₍a₎(x) ∧ P₍b₎(x)`.
def inter (A B: Set X): Set X := { x: X.Particular | A.pred x ∧ B.pred x }
infixl:70 " ∩ₛₑₜ " => inter

-- # Theorems







--The `Empty Set` is unique.
theorem empty_set_uniqueness: ∃!₍𝐒𝐞𝐭 U₎ (S: Set U), ∀ (x: U.Particular), x ∉ₛₑₜ S := by

  -- P is the predicate for which we want to prove unique existence
  let P: Set U → Prop := (S: Set U ↦ ∀ (x: U.Particular), x ∉ₛₑₜ S)

  -- A is the "only" Set that meets P.
  have h₁: ∃ (S: Set U), P S := empty_set_existence
  have ⟨(A: Set U), (h₂: P A)⟩ := exists_elim h₁

  -- Any Set that meets P is equal to A.
  have h₃: ∀ (S: Set U), P S → (S =ₛₑₜ A) := by forall_intro
    variable (B: Set U)
    assume (h₂₁: P B)

    -- We first show equal extensionality and then convert to set equality.
    have h₂₂: ∀ (x: U.Particular), x ∈ₛₑₜ B ↔ x ∈ₛₑₜ A := by forall_intro
      variable (u: U.Particular)
      have h₂₂₁: u ∈ₛₑₜ B → u ∈ₛₑₜ A := by
        assume (h₂₂₁₁: u ∈ₛₑₜ B)
        have h₂₂₁₂: u ∉ₛₑₜ B := by forall_elim h₂₁, u
        have h₂₂₁₃: (u ∉ₛₑₜ B) ↔ ¬(u ∈ₛₑₜ B) := not_mem_iff_neg_mem
        have h₂₂₁₄: ¬(u ∈ₛₑₜ B) := PC₀.deductive_eq_l2r h₂₂₁₃ h₂₂₁₂
        have h₂₂₁₅: u ∈ₛₑₜ A := PC₀.quodlibet_seqitur h₂₂₁₁ h₂₂₁₄
        iterate h₂₂₁₅
      have h₂₂₂: u ∈ₛₑₜ A → u ∈ₛₑₜ B := by
        assume (h₂₂₂₁: u ∈ₛₑₜ A)
        have h₂₂₂₂: u ∉ₛₑₜ A := by forall_elim h₂, u
        have h₂₂₁₃: (u ∉ₛₑₜ A) ↔ ¬(u ∈ₛₑₜ A) := not_mem_iff_neg_mem
        have h₂₂₂₄: ¬(u ∈ₛₑₜ A) := PC₀.deductive_eq_l2r h₂₂₁₃ h₂₂₂₂
        have h₂₂₂₅: u ∈ₛₑₜ B := PC₀.quodlibet_seqitur h₂₂₂₁ h₂₂₂₄
        iterate h₂₂₂₅
      iff_intro h₂₂₁, h₂₂₂

    -- Convert extensionality to set equality
    have h₂₃: ∀ (S₂: Set U), B =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ B ↔ x ∈ₛₑₜ S₂) := by forall_elim set_extensionality, B
    have h₂₄: B =ₛₑₜ A ↔ (∀ (x: U.Particular), x ∈ₛₑₜ B ↔ x ∈ₛₑₜ A) := by forall_elim h₂₃, A
    have h₂₅: B =ₛₑₜ A := PC₀.deductive_eq_r2l h₂₄ h₂₂

    -- Convert set equality to polymorphic equality
    have h₂₆: ∀ (S₂: Set X), B =ₛₑₜ S₂ ↔ B =ₚ S₂ := by forall_elim eq_poly_eq, B
    have h₂₇: B =ₛₑₜ A ↔ B =ₚ A := by forall_elim h₂₆, A
    have h₂₈: B =ₚ A := PC₀.deductive_eq_l2r h₂₇ h₂₅
    iterate h₂₈

  -- Introduce unique existence for P
  have h₄: P A ∧ (∀ (S: Set X), P S → (S =ₚ A)) := by and_intro h₂, h₃
  have h₅: ∃ (S': Set X), P S' ∧ (∀ (S: Set X), P S → (S =ₚ S')) := by exists_intro h₄, A
  have h₆: (∃! (S: Set X), P S) ↔
           (∃ (S': Set X), P S' ∧ (∀ (S: Set X), (P S) → (S =ₚ S'))) := by forall_elim exists_unique_def, P
  have h₇: ∃! (S: Set X), P S := PC₀.deductive_eq_r2l h₆ h₅
  iterate h₇

/-!

-- ## Theorems, showing that the `Set` operations are well-defined.
theorem complement_operation_is_well_defined (A: Set X) (x : Particular X) :
  x ∈ₛₑₜ (¬ₛₑₜA) ↔ ¬(x ∈ₛₑₜ A) := by
    unfold mem compl
    rfl

theorem intersection_is_well_defined (A B: Set X) (x : Particular X) :
  x ∈ₛₑₜ (A ∩ₛₑₜ B) ↔ (x ∈ₛₑₜ A ∧ x ∈ₛₑₜ B) := by
    unfold mem inter
    rfl

theorem union_is_well_defined (A B : Set X) (x : Particular X) :
  x ∈ₛₑₜ (A ∪ₛₑₜ B) ↔ (x ∈ₛₑₜ A ∨ x ∈ₛₑₜ B) := by
    unfold mem union
    rfl

theorem subset_relation_is_well_defined (A B: Set X) :
  (A ⊆ₛₑₜ B) ↔ (∀ (x: Particular X), x ∈ₛₑₜ A → x ∈ₛₑₜ B) := by
    unfold subset mem
    rfl

-- ## Theorems showing the `Universe` and the `Empty Set` are complements.
theorem the_empty_set_is_the_complement_of_the_universe_set:
  ¬ₛₑₜemptySet = (universalSet: Set X) := by
    funext x
    unfold compl emptySet universalSet
    simp

theorem the_universe_set_is_the_complement_of_the_empty_set:
  ¬ₛₑₜuniversalSet = (emptySet: Set X) := by
    funext x
    unfold compl universalSet emptySet
    simp

-/

end Sets

end Universe
