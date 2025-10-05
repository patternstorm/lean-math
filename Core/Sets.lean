import Core.Universe

/-!
# Predicates As Sets
A *Predicate* partitions the *Particulars* in our *Universe* in two - each partition is called a *Set* -,
according to whether they satisfy the *Predicate* or not.

We can now define operations on *Sets* based on well-known *Predicate* operations.

Let P_A(_) denote the *Predicate* that gives place to the *Set* A.
-/

namespace Universe

-- A *Set* is a *Predicate*
def Set := Predicate

-- *Set* Membership, a *Particular* x is a member of the *Set* A if it satisfies the *Predicate* P_A(_).
def mem (x : Particular X) (A : Set X) : Prop := A x

-- Set operations.
-- The complementary of the *Set* of A is a *Set* defined by the *Predicate* ¬P_A(_).
def compl (A : Set X) : Set X := fun (x : Particular X) => ¬(A x)
-- The intersection of the *Sets* A and B is a *Set* defined by the predicate P_A(x) ∧ P_B(x).
def inter (A B : Set X) : Set X := fun (x : Particular X) => A x ∧ B x
-- The union of the *Sets* A and B is a *Set* defined by the predicate P_A(x) ∨ P_B(x).
def union (A B : Set X) : Set X := fun (x : Particular X) => A x ∨ B x
-- The *Set* A is a subset of the *Set* B if and only if P_A(x) → P_B(x).
def subset (A B : Set X) : Prop := ∀ (x : Particular X), A x → B x

-- Notation
notation:50 x:51 " ∈ " A:51 => mem x A  -- Explicit precedence for arguments
prefix:max "¬ₛ" => compl
infixl:70 " ∩ " => inter
infixl:65 " ∪ " => union
infix:50 " ⊆ " => subset

-- Theorems, showing that the *Set* operations are well-defined.
theorem neg_equiv (A : Set X) (x : Particular X) :
    x ∈ (¬ₛA) ↔ ¬(x ∈ A) := by
  unfold mem compl
  rfl

theorem inter_equiv (A B : Set X) (x : Particular X) :
    x ∈ (A ∩ B) ↔ (x ∈ A ∧ x ∈ B) := by
  unfold mem inter
  rfl

theorem union_equiv (A B : Set X) (x : Particular X) :
    x ∈ (A ∪ B) ↔ (x ∈ A ∨ x ∈ B) := by
  unfold mem union
  rfl

theorem subset_equiv (A B : Set X) :
    (A ⊆ B) ↔ (∀ (x : Particular X), x ∈ A → x ∈ B) := by
  unfold subset mem
  rfl

end Universe
