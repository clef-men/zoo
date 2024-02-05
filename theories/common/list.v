From stdpp Require Export
  list.

From zebre Require Import
  prelude.
From zebre Require Import
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

  Lemma reverse_nil_iff l :
    reverse l = [] ↔
    l = [].
  Proof.
    destruct (rev_elim l) as [-> | (l' & x & ->)]; first done.
    rewrite reverse_snoc app_nil. naive_solver.
  Qed.
End basic.
