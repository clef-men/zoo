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
