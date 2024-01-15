From stdpp Require Export
  list.

From zebra Require Import
  prelude.
From zebra Require Import
  options.

Section basic.
  Context {A : Type}.

  Implicit Types x y z : A.
  Implicit Types l : list A.

  Lemma rev_elim l :
    l = [] ∨ ∃ l' x, l = l' ++ [x].
  Proof.
    revert l. refine (rev_ind _ _ _); [| intros x l _]; naive_solver.
  Qed.
End basic.
