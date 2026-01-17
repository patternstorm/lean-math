import Logic
import Universe
import Universals.Sets.Universal
import Universals.Sets.Predicates.Binary.Membership.Predicate
import Universals.Sets.Predicates.Binary.Membership.Properties.PredicateEquivIsMembershipEquiv

namespace Universe

namespace Sets

open Logic
open Logic.PC₁


-- ## Set Extensionality `Set` equality is well defined, it's extensional ,i.e. Two sets are equal if and only if they have the same elements.
theorem set_extensionality: ∀ (S₁: (Set U).Particular), ∀ (S₂: (Set U).Particular), S₁ =ₛₑₜ S₂ ↔ (∀ (x: U.Particular), x ∈ₛₑₜ S₁ ↔ x ∈ₛₑₜ S₂) := by forall_intro
  variable (A: (Set U).Particular)
  variable (B: (Set U).Particular)

  -- From set equality, establish predicate equivalence for arbitrary Sets A and B
  have h₁: ∀ S₂: (Set U).Particular, A =ₛₑₜ S₂ ↔ ∀ (x: U.Particular), A.pred x ↔ S₂.pred x := by forall_elim eq_def, A
  have h₂: A =ₛₑₜ B ↔ ∀ (x: U.Particular), A.pred x ↔ B.pred x := by forall_elim h₁, B

  -- Establish equivalence between membership and predicate application for arbitrary Set A
  -- have h₃: ∀ (x: U.Particular), x ∈ₛₑₜ A ↔ A.pred x := by forall_elim mem_def, A

  -- Establish equivalence between membership and predicate application for arbitrary Set B
  -- have h₃: ∀ (x: U.Particular), x ∈ₛₑₜ B ↔ B.pred x := by forall_elim mem_def, B

  -- Proof the conclusion for arbitrary Sets A and B
  have h₄: A =ₛₑₜ B ↔ (∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B) := by

    -- Forward direction: set equality implies membership equivalence
    have h₄₁: A =ₛₑₜ B → (∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B) := by
      assume (h₄₁₁: A =ₛₑₜ B)

      -- Derive the conclusion via forall_intro
      have h₄₁₂: ∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B := by forall_intro
        variable (u: U.Particular)

        -- From the equality of arbitrary Sets A and B, establish membership equivalence
        have h₄₁₂₁: ∀ (x: U.Particular), A.pred x ↔ B.pred x := PC₀.deductive_eq_l2r h₂ h₄₁₁
        have h₄₁₂₂: A.pred u ↔ B.pred u := by forall_elim h₄₁₂₁, u
        have h₄₁₂₃: u ∈ₛₑₜ A ↔ u ∈ₛₑₜ B := PC₀.deductive_eq_l2r pred_eq_iff_mem_eq h₄₁₂₂
        iterate h₄₁₂₃

      iterate h₄₁₂

    -- Backward direction: membership equivalence implies set equality
    have h₄₂: (∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B) → A =ₛₑₜ B := by
      assume (h₄₂₁: ∀ (x: U.Particular), x ∈ₛₑₜ A ↔ x ∈ₛₑₜ B)

      -- Prove ∀ x, A x ↔ B x, then convert to set equality
      have h₄₂₂: ∀ (x: U.Particular), A.pred x ↔ B.pred x := by forall_intro
        variable (u: U.Particular)

        -- Establish membership equivalence for an arbitrary Particular u
        have h₄₂₂₁: u ∈ₛₑₜ A ↔ u ∈ₛₑₜ B := by forall_elim h₄₂₁, u
        have h₄₂₂₂: A.pred u ↔ B.pred u := PC₀.deductive_eq_r2l pred_eq_iff_mem_eq h₄₂₂₁
        iterate h₄₂₂₂

      -- Convert predicate equivalence to set equality
      have h₁₅₂₃: A =ₛₑₜ B := PC₀.deductive_eq_r2l h₂ h₄₂₂
      iterate h₁₅₂₃

    iff_intro h₄₁, h₄₂

end Sets

end Universe
