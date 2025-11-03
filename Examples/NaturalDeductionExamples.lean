import Core.NaturalDeduction

/-!
# Natural Deduction Examples

This file demonstrates the custom natural deduction tactics with classic
first-order logic proofs. Each example shows how the tactics mirror
traditional natural deduction inference rules.
-/

/-!
## Conjunction Examples
-/

-- Example 1: ∧-introduction
theorem and_intro_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  and_intro hp , hq

-- Example 2: ∧-elimination
theorem and_elim_example (P Q : Prop) (h : P ∧ Q) : P := by
  and_elim_left h

theorem and_elim_example2 (P Q : Prop) (h : P ∧ Q) : Q := by
  and_elim_right h

-- Example 3: Conjunction is commutative
theorem and_commutative (P Q : Prop) : P ∧ Q → Q ∧ P := by
  implies_intro h
  and_intro h.right, h.left

/-!
## Disjunction Examples
-/

-- Example 4: ∨-introduction
theorem or_intro_left_example (P Q : Prop) (hp : P) : P ∨ Q := by
  or_intro_left hp

theorem or_intro_right_example (P Q : Prop) (hq : Q) : P ∨ Q := by
  or_intro_right hq

-- Example 5: ∨-elimination (case analysis)
theorem or_elim_example (P Q R : Prop) (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  or_elim h
  · exact hpr ‹_›
  · exact hqr ‹_›

-- Example 6: Disjunction is commutative
theorem or_commutative (P Q : Prop) : P ∨ Q → Q ∨ P := by
  implies_intro h
  or_elim h
  · or_intro_right ‹_›
  · or_intro_left ‹_›

/-!
## Implication Examples
-/

-- Example 7: →-introduction and elimination
theorem implies_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  implies_intro hpq
  implies_intro hqr
  implies_intro hp
  have hq := hpq hp
  implies_elim hqr hq

-- Example 8: Self-implication
theorem self_implies (P : Prop) : P → P := by
  implies_intro hp
  exact hp

/-!
## Negation Examples
-/

-- Example 9: ¬-introduction (proof by contradiction)
theorem not_intro_example (P : Prop) (h : P → False) : ¬P := by
  not_intro hp
  exact h hp

-- Example 10: Contradiction principle
theorem contradiction_example (P : Prop) (hp : P) (hnp : ¬P) : False := by
  absurd hp hnp

/-!
## Universal Quantifier Examples
-/

-- Example 11: ∀-introduction
theorem forall_intro_example (P : Nat → Prop) (h : ∀ n, P n) : ∀ m, P m := by
  forall_intro m
  exact h m

-- Example 12: ∀-elimination
theorem forall_elim_example (P : Nat → Prop) (h : ∀ n, P n) : P 5 := by
  exact h 5

-- Example 13: Universal quantifier distributes over implication
theorem forall_dist (P Q : Nat → Prop) : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  implies_intro h1
  implies_intro h2
  forall_intro x
  exact h1 x (h2 x)

/-!
## Existential Quantifier Examples
-/

-- Example 14: ∃-introduction
theorem exists_intro_example (P : Nat → Prop) (h : P 3) : ∃ n, P n := by
  exists_intro 3

-- Example 15: ∃-elimination
theorem exists_elim_example (P : Nat → Prop) (Q : Prop)
    (h : ∃ n, P n) (hpq : ∀ n, P n → Q) : Q := by
  exists_elim h
  exact hpq _ ‹_›

/-!
## Complex Examples Combining Multiple Rules
-/

-- Example 16: De Morgan's Law (¬(P ∧ Q) → ¬P ∨ ¬Q) - requires classical logic
theorem de_morgan1 (P Q : Prop) : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  implies_intro h
  by_cases hp : P
  · or_intro_right
    not_intro hq
    have hpq : P ∧ Q := And.intro hp hq
    absurd hpq h
  · or_intro_left
    exact hp

-- Example 17: Modus Tollens
theorem modus_tollens (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  implies_intro hpq
  implies_intro hnq
  not_intro hp
  have hq := hpq hp
  absurd hq hnq

-- Example 18: Hypothetical Syllogism
theorem hypothetical_syllogism (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  implies_intro hpq
  implies_intro hqr
  implies_intro hp
  exact hqr (hpq hp)

-- Example 19: Constructive Dilemma
theorem constructive_dilemma (P Q R S : Prop) :
    (P → Q) → (R → S) → (P ∨ R) → (Q ∨ S) := by
  implies_intro hpq
  implies_intro hrs
  implies_intro hpr
  or_elim hpr
  · or_intro_left
    exact hpq ‹_›
  · or_intro_right
    exact hrs ‹_›

-- Example 20: Existential instantiation with universal
theorem exists_forall_example (P : Nat → Nat → Prop) :
    (∃ x, ∀ y, P x y) → (∀ y, ∃ x, P x y) := by
  implies_intro h
  forall_intro y
  exists_elim h
  exists_intro ‹_›
  exact ‹∀ y, P _ y› y
