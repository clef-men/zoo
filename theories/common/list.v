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
End basic.

Section foldr.
  Lemma foldr_comm_acc_strong {A B} (R : relation B) `{!PreOrder R} (f : A → B → B) (g : B → B) b l :
    (∀ x, Proper (R ==> R) (f x)) →
    (∀ x y, x ∈ l → R (f x (g y)) (g (f x y))) →
    R (foldr f (g b) l) (g (foldr f b l)).
  Proof.
    intros ? Hcomm. induction l as [|x l IH]; simpl; [done |].
    rewrite <- Hcomm by auto using elem_of_list_here.
    rewrite -> IH by auto using elem_of_list_further. done.
  Qed.
End foldr.

