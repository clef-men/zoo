From stdpp Require Export
  list.

From zoo Require Import
  prelude.
From zoo Require Import
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

  Lemma foldr_insert_strong `(f : A → B → B) comp l i x y acc :
    l !! i = Some x →
    ( ∀ x acc,
      f x (f y acc) = f y (f x acc)
    ) →
    ( ∀ acc,
      f (comp y x) acc = f y (f x acc)
    ) →
    foldr f acc (<[i := comp y x]> l) = f y (foldr f acc l).
  Proof.
    intros Hlookup Hf Hcomp.
    rewrite insert_take_drop. { eapply lookup_lt_Some. done. }
    rewrite -{3}(take_drop_middle l i x) // !foldr_app /=.
    rewrite -(foldr_comm_acc_strong _ _ (f y)) // Hcomp //.
  Qed.
  Lemma foldr_insert_strong' op `{!Assoc (=) op} `{!Comm (=) op} comp l i x y acc :
    l !! i = Some x →
    ( ∀ acc,
      op (comp y x) acc = op y (op x acc)
    ) →
    foldr op acc (<[i := comp y x]> l) = op y (foldr op acc l).
  Proof.
    intros Hlookup Hcomp.
    apply foldr_insert_strong; try done.
    intros. rewrite assoc (comm _ _ y) //.
  Qed.
  Lemma foldr_insert op `{!Assoc (=) op} `{!Comm (=) op} l i x y acc :
    l !! i = Some x →
    foldr op acc (<[i := op y x]> l) = op y (foldr op acc l).
  Proof.
    intros Hlookup.
    apply: foldr_insert_strong'; done.
  Qed.

  Lemma lookup_last_length l i :
    is_Some (l !! i) →
    l !! S i = None →
    length l = S i.
  Proof.
    intros ?%lookup_lt_is_Some ?%lookup_ge_None. lia.
  Qed.
End basic.

Section Permutation.
  Context {A : Type}.

  Implicit Types x : A.
  Implicit Types l : list A.

  Lemma Permutation_swap' l i1 x1 i2 x2 :
    l !! i1 = Some x1 →
    l !! i2 = Some x2 →
    <[i1 := x2]> (<[i2 := x1]> l) ≡ₚ l.
  Proof.
    rewrite Permutation_inj => Hlookup1 Hlookup2.
    opose proof* (lookup_lt_Some l i1) as Hi1; first done.
    opose proof* (lookup_lt_Some l i2) as Hi2; first done.
    split.
    - rewrite !insert_length //.
    - exists (λ j, if decide (j = i1) then i2 else if decide (j = i2) then i1 else j). split.
      + intros j1 j2. repeat case_decide; naive_solver.
      + intros j. repeat case_decide; subst.
        * rewrite list_lookup_insert // insert_length //.
        * rewrite list_lookup_insert_ne // list_lookup_insert //.
        * rewrite list_lookup_insert_ne // list_lookup_insert_ne //.
  Qed.
End Permutation.
