-- TÀCTIQUES PER A DEDUCCIÓ NATURAL - PRIMER ORDRE

import Lean

open Lean Elab Tactic

-- CONJUNCIÓ
macro "and_intro" h1:term "," h2:term : tactic => `(tactic| exact ⟨$h1, $h2⟩)
macro "and_elim_left" h:term : tactic => `(tactic| exact ($h).left)
macro "and_elim_right" h:term : tactic => `(tactic| exact ($h).right)

-- DISJUNCIÓ
macro "or_intro_left" h:term : tactic => `(tactic| exact Or.inl $h)
macro "or_intro_right" h:term : tactic => `(tactic| exact Or.inr $h)
macro "or_elim" h:ident "as" n1:ident "|" n2:ident : tactic =>
  `(tactic| cases $h:ident with | inl $n1 => ?_ | inr $n2 => ?_)

-- IMPLICACIÓ
macro "implies_intro" : tactic => `(tactic| intro)
macro "implies_elim" h1:term h2:term : tactic => `(tactic| exact $h1 $h2)

-- NEGACIÓ
macro "not_intro" : tactic => `(tactic| intro)
macro "not_elim" h1:term h2:term : tactic => `(tactic| exact ($h1 $h2))
macro "ex_falso" h:term : tactic => `(tactic| exact False.elim $h)

-- QUANTIFICADOR UNIVERSAL
macro "forall_intro" : tactic => `(tactic| intro)
macro "forall_elim" h:term t:term : tactic => `(tactic| exact $h $t)

-- QUANTIFICADOR EXISTENCIAL
macro "exists_intro" t:term "," h:term : tactic => `(tactic| exact ⟨$t, $h⟩)
macro "exists_elim" h:ident "as" x:ident hx:ident : tactic =>
  `(tactic| cases $h:ident with | intro $x $hx => ?_)

-- IGUALTAT
macro "refl" : tactic => `(tactic| rfl)
macro "subst" h:term : tactic => `(tactic| subst $h)

-- EXEMPLES D'ÚS

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  have hq : q := by and_elim_right h
  have hp : p := by and_elim_left h
  and_intro hq, hp

example (p q r : Prop) : (p ∨ q) → (p → r) → (q → r) → r := by
  intro h_or
  intro h_pr
  intro h_qr
  or_elim h_or as hp | hq
  · exact h_pr hp
  · exact h_qr hq

example (p : Prop) : ¬(p ∧ ¬p) := by
  intro h
  have hp : p := by and_elim_left h
  have hnp : ¬p := by and_elim_right h
  exact hnp hp

example (α : Type) (P : α → Prop) (a : α) : (∀ x, P x) → P a := by
  intro h
  exact h a

example (α : Type) (P : α → Prop) (a : α) : P a → ∃ x, P x := by
  intro h
  exists_intro a, h

example (α : Type) (P Q : α → Prop) :
    (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  intro h_ex
  intro h_all
  exists_elim h_ex as x h_px
  have h_qx : Q x := h_all x h_px
  exists_intro x, h_qx

example (p : Prop) : p → ¬¬p := by
  intro hp -- have hp : p := by intro hp
  intro hnp
  exact hnp hp

-- Exemple amb igualtat
example (α : Type) (a b c : α) : a = b → b = c → a = c := by
  intro h1
  intro h2
  subst h1
  subst h2
  refl

-- Llei del mig exclòs (usant clàssica)
example (p : Prop) : p ∨ ¬p := by
  exact Classical.em p

-- Reducció a l'absurd (prova per contradicció)
example (p : Prop) : ¬¬p → p := by
  intro h
  by_cases hp : p
  · exact hp
  · ex_falso (h hp)
