From stdpp Require Export
  gmultiset.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo Require Import
  options.

Section basic.
  Context `{Countable A}.

  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Lemma gmultiset_empty_elem_of X :
    X = ∅ ↔
      ∀ x,
      x ∉ X.
  Proof.
    multiset_solver.
  Qed.
End basic.

Section size.
  Context `{Countable A}.

  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Lemma gmultiset_size_singleton_inv X x y :
    size X = 1 →
    x ∈ X →
    y ∈ X →
    x = y.
  Proof.
    rewrite /size /gmultiset_size /= -!gmultiset_elem_of_elements.
    generalize (elements X). intros [| ? l] ?*; simplify.
    rewrite (nil_length_inv l) // !elem_of_list_singleton. congruence.
  Qed.
  Lemma gmultiset_size_1_elem_of X :
    size X = 1 →
      ∃ x,
      X = {[+x+]}.
  Proof.
    intros Hsize.
    destruct (gmultiset_size_pos_elem_of X) as (x & Hx); first lia. exists x.
    assert ({[+x+]} ⊆ X) by multiset_solver.
    rewrite (gmultiset_disj_union_difference {[+x+]} X) //.
    assert (X ∖ {[+x+]} = ∅) as ->; last rewrite right_id //.
    rewrite -gmultiset_size_empty_iff gmultiset_size_difference // gmultiset_size_singleton. lia.
  Qed.

  Lemma gmultiset_elem_of_size_non_empty x X :
    x ∈ X →
    size X ≠ 0.
  Proof.
    rewrite gmultiset_size_non_empty_iff.
    multiset_solver.
  Qed.
End size.

Section list_to_set_disj.
  Context `{Countable A}.

  Implicit Types x y : A.
  Implicit Types l : list A.

  Lemma list_to_set_disj_snoc l x :
    list_to_set_disj (l ++ [x]) =@{gmultiset _} {[+x+]} ⊎ list_to_set_disj l.
  Proof.
    rewrite list_to_set_disj_app list_to_set_disj_cons right_id (comm (⊎)) //.
  Qed.
End list_to_set_disj.

Section disj_union_list.
  Context `{Countable A}.

  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.
  Implicit Types Xs Ys : list $ gmultiset A.

  Lemma gmultiset_disj_union_list_empty Xs :
    ⋃+ Xs = ∅ ↔
      ∀ X,
      X ∈ Xs →
      X = ∅.
  Proof.
    setoid_rewrite gmultiset_empty_elem_of.
    setoid_rewrite elem_of_gmultiset_disj_union_list.
    naive_solver.
  Qed.

  Lemma gmultiset_disj_union_list_delete Xs i X :
    Xs !! i = Some X →
    ⋃+ Xs = X ⊎ ⋃+ (delete i Xs).
  Proof.
    intros Hlookup.
    rewrite {1}(delete_Permutation Xs i X) //.
  Qed.

  Lemma gmultiset_disj_union_list_insert Xs i X :
    is_Some (Xs !! i) →
    ⋃+ <[i := X]> Xs = X ⊎ ⋃+ (delete i Xs).
  Proof.
    intros (Y & Hlookup).
    opose proof* (lookup_lt_Some Xs i Y); first done.
    rewrite (gmultiset_disj_union_list_delete (<[i := X]> Xs) i X).
    { rewrite list_lookup_insert //. }
    rewrite list_delete_insert_delete //.
  Qed.
  Lemma gmultiset_disj_union_list_insert_id Xs i X :
    Xs !! i = Some X →
    ⋃+ <[i := X]> Xs = ⋃+ Xs.
  Proof.
    intros Hlookup.
    rewrite gmultiset_disj_union_list_insert //.
    rewrite {2}(delete_Permutation Xs i X) //.
  Qed.
  Lemma gmultiset_disj_union_list_insert_disj_union_l Xs i X1 X2 :
    Xs !! i = Some X2 →
    ⋃+ <[i := X1 ⊎ X2]> Xs = X1 ⊎ ⋃+ Xs.
  Proof.
    intros Hlookup.
    rewrite gmultiset_disj_union_list_insert //.
    rewrite -assoc. f_equal.
    rewrite -gmultiset_disj_union_list_insert //.
    rewrite gmultiset_disj_union_list_insert_id //.
  Qed.
  Lemma gmultiset_disj_union_list_insert_disj_union_r Xs i X1 X2 :
    Xs !! i = Some X1 →
    ⋃+ <[i := X1 ⊎ X2]> Xs = X2 ⊎ ⋃+ Xs.
  Proof.
    intros Hlookup.
    rewrite (comm (⊎)) gmultiset_disj_union_list_insert_disj_union_l //.
  Qed.
End disj_union_list.
