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

  Lemma gmultiset_disj_union_empty X1 X2 :
    X1 ⊎ X2 = ∅ ↔
      X1 = ∅ ∧
      X2 = ∅.
  Proof.
    multiset_solver.
  Qed.
  Lemma gmultiset_disj_union_empty_inv X1 X2 :
    X1 ⊎ X2 = ∅ →
      X1 = ∅ ∧
      X2 = ∅.
  Proof.
    rewrite gmultiset_disj_union_empty //.
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

Section map.
  Context `{Countable A}.
  Context `{Countable B}.
  Context (f : A → B).

  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.
  Implicit Types 𝑋 𝑌 : gmultiset B.

  Lemma gmultiset_size_map X :
    size (gmultiset_map f X) = size X.
  Proof.
    induction X as [| x X IH] using gmultiset_ind.
    - done.
    - rewrite gmultiset_map_disj_union gmultiset_map_singleton.
      rewrite !gmultiset_size_disj_union !gmultiset_size_singleton.
      auto.
  Qed.

  Lemma gmultiset_map_singleton_inv X 𝑥 :
    gmultiset_map f X = {[+𝑥+]} →
      ∃ x,
      X = {[+x+]} ∧
      𝑥 = f x.
  Proof.
    intros Heq.
    destruct X as [| x X _] using gmultiset_ind.
    - done.
    - rewrite gmultiset_map_disj_union gmultiset_map_singleton in Heq.
      assert (size X = 0) as ->%gmultiset_size_empty_inv.
      { apply (f_equal size) in Heq.
        rewrite gmultiset_size_disj_union gmultiset_size_map !gmultiset_size_singleton in Heq.
        lia.
      }
      rewrite gmultiset_map_empty right_id in Heq.
      set_solver.
  Qed.

  Lemma gmultiset_map_disj_union_inv X 𝑋1 𝑋2 :
    gmultiset_map f X = 𝑋1 ⊎ 𝑋2 →
      ∃ X1 X2,
      X = X1 ⊎ X2 ∧
      𝑋1 = gmultiset_map f X1 ∧
      𝑋2 = gmultiset_map f X2.
  Proof.
    move: 𝑋1 𝑋2. induction X as [| x X IH] using gmultiset_ind => 𝑋1 𝑋2 Heq.
    - exists ∅, ∅.
      rewrite gmultiset_map_empty in Heq.
      apply symmetry, gmultiset_disj_union_empty in Heq as (-> & ->).
      done.
    - rewrite gmultiset_map_disj_union gmultiset_map_singleton in Heq.
      assert (f x ∈ 𝑋1 ⊎ 𝑋2) as Helem by multiset_solver.
      rewrite (gmultiset_disj_union_difference' (f x) (𝑋1 ⊎ 𝑋2)) // in Heq.
      apply (inj _) in Heq.
      apply gmultiset_elem_of_disj_union in Helem as [Helem | Helem].
      + replace ((𝑋1 ⊎ 𝑋2) ∖ {[+f x+]}) with ((𝑋1 ∖ {[+f x+]}) ⊎ 𝑋2) in Heq by multiset_solver.
        apply IH in Heq as (X1 & X2 & -> & Heq1 & Heq2).
        exists ({[+x+]} ⊎ X1), X2. split_and!.
        * set_solver by lia.
        * rewrite gmultiset_map_disj_union gmultiset_map_singleton.
          multiset_solver.
        * done.
      + replace ((𝑋1 ⊎ 𝑋2) ∖ {[+f x+]}) with (𝑋1 ⊎ (𝑋2 ∖ {[+f x+]})) in Heq by multiset_solver.
        apply IH in Heq as (X1 & X2 & -> & Heq1 & Heq2).
        exists X1, ({[+x+]} ⊎ X2). split_and!.
        * set_solver by lia.
        * done.
        * rewrite gmultiset_map_disj_union gmultiset_map_singleton.
          multiset_solver.
  Qed.
  Lemma gmultiset_map_disj_union_singleton_l_inv X 𝑥 𝑋 :
    gmultiset_map f X = {[+𝑥+]} ⊎ 𝑋 →
      ∃ x X',
      X = {[+x+]} ⊎ X' ∧
      𝑥 = f x ∧
      𝑋 = gmultiset_map f X'.
  Proof.
    intros (X1 & X2 & -> & (x & -> & ->)%symmetry%gmultiset_map_singleton_inv & Heq)%gmultiset_map_disj_union_inv.
    eauto.
  Qed.
  Lemma gmultiset_map_disj_union_singleton_r_inv X 𝑥 𝑋 :
    gmultiset_map f X = 𝑋 ⊎ {[+𝑥+]} →
      ∃ X' x,
      X = X' ⊎ {[+x+]} ∧
      𝑋 = gmultiset_map f X' ∧
      𝑥 = f x.
  Proof.
    setoid_rewrite (comm (⊎)) at 1 3.
    intros (x & X' & -> & -> & ->)%gmultiset_map_disj_union_singleton_l_inv.
    eauto.
  Qed.
End map.

Section list_to_set_disj.
  Context `{Countable A}.

  Implicit Types x y : A.
  Implicit Types l : list A.

  Lemma list_to_set_disj_empty l :
    list_to_set_disj l =@{gmultiset _} ∅ ↔
    l = [].
  Proof.
    split.
    - destruct l as [| x l]; first done.
      multiset_solver.
    - intros ->.
      apply list_to_set_disj_nil.
  Qed.

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
  Lemma gmultiset_disj_union_list_replicate_empty n :
    ⋃+ replicate n ∅ =@{gmultiset A} ∅.
  Proof.
    apply gmultiset_disj_union_list_empty. intros X (-> & _)%elem_of_replicate => //.
  Qed.

  Lemma gmultiset_disj_union_list_delete Xs i X :
    Xs !! i = Some X →
    ⋃+ (delete i Xs) = ⋃+ Xs ∖ X.
  Proof.
    intros Hlookup.
    rewrite {2}(delete_Permutation Xs i X) //.
    multiset_solver.
  Qed.
  Lemma gmultiset_disj_union_list_delete' Xs i X :
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
    rewrite (gmultiset_disj_union_list_delete' (<[i := X]> Xs) i X).
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
