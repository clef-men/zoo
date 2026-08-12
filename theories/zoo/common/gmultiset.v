Require Export stdpp.gmultiset.

Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.options.

Section basic.
  Context `{Countable A}.

  Implicit Type x y : A.
  Implicit Type X Y : gmultiset A.

  Lemma gmultisetｰemptyｰelem_of X :
    X = ∅ ↔
      ∀ x,
      x ∉ X.
  Proof.
    multiset_solver.
  Qed.

  Lemma gmultisetｰdisj_unionｰempty X1 X2 :
    X1 ⊎ X2 = ∅ ↔
      X1 = ∅ ∧
      X2 = ∅.
  Proof.
    multiset_solver.
  Qed.
  Lemma gmultisetｰdisj_unionｰemptyｰinv X1 X2 :
    X1 ⊎ X2 = ∅ →
      X1 = ∅ ∧
      X2 = ∅.
  Proof.
    rewrite gmultisetｰdisj_unionｰempty //.
  Qed.

  Lemma elem_ofｰgmultisetｰdisj_unionｰl x X1 X2 :
    x ∈ X1 →
    x ∈ X1 ⊎ X2.
  Proof.
    multiset_solver.
  Qed.
  Lemma elem_ofｰgmultisetｰdisj_unionｰr x X1 X2 :
    x ∈ X2 →
    x ∈ X1 ⊎ X2.
  Proof.
    multiset_solver.
  Qed.
End basic.

Section size.
  Context `{Countable A}.

  Implicit Type x y : A.
  Implicit Type X Y : gmultiset A.

  Lemma gmultisetｰsizeｰsingletonｰinv X x y :
    size X = 1 →
    x ∈ X →
    y ∈ X →
    x = y.
  Proof.
    rewrite /size /gmultiset_size /= -!gmultiset_elem_of_elements.
    generalize (elements X). intros [| ? l] ?*; simp.
    rewrite (nil_length_inv l) // !list_elem_of_singleton. congruence.
  Qed.
  Lemma gmultisetｰsizeｰ1ｰelem_of X :
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

  Lemma gmultisetｰelem_ofｰsizeｰnon_empty x X :
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

  Implicit Type x y : A.
  Implicit Type X Y : gmultiset A.
  Implicit Type 𝑋 𝑌 : gmultiset B.

  Lemma gmultisetｰsizeｰmap X :
    size (gmultiset_map f X) = size X.
  Proof.
    induction X as [| x X IH] using gmultiset_ind.
    - done.
    - rewrite gmultiset_map_disj_union gmultiset_map_singleton.
      rewrite !gmultiset_size_disj_union !gmultiset_size_singleton.
      auto.
  Qed.

  Lemma gmultiset_mapｰemptyｰinv X :
    gmultiset_map f X = ∅ →
    X = ∅.
  Proof.
    destruct X as [| x X _] using gmultiset_ind.
    - done.
    - intros Hsize%(f_equal size).
      rewrite gmultiset_map_disj_union gmultiset_map_singleton in Hsize.
      rewrite gmultiset_size_disj_union gmultiset_size_singleton gmultiset_size_empty // in Hsize.
  Qed.

  Lemma gmultiset_mapｰsingletonｰinv X 𝑥 :
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
        rewrite gmultiset_size_disj_union gmultisetｰsizeｰmap !gmultiset_size_singleton in Heq.
        lia.
      }
      rewrite gmultiset_map_empty right_id in Heq.
      set_solver.
  Qed.

  Lemma gmultiset_mapｰdisj_unionｰinv X 𝑋1 𝑋2 :
    gmultiset_map f X = 𝑋1 ⊎ 𝑋2 →
      ∃ X1 X2,
      X = X1 ⊎ X2 ∧
      𝑋1 = gmultiset_map f X1 ∧
      𝑋2 = gmultiset_map f X2.
  Proof.
    move: 𝑋1 𝑋2. induction X as [| x X IH] using gmultiset_ind => 𝑋1 𝑋2 Heq.
    - exists ∅, ∅.
      rewrite gmultiset_map_empty in Heq.
      apply symmetry, gmultisetｰdisj_unionｰempty in Heq as (-> & ->).
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
  Lemma gmultiset_mapｰdisj_unionｰsingletonｰlｰinv X 𝑥 𝑋 :
    gmultiset_map f X = {[+𝑥+]} ⊎ 𝑋 →
      ∃ x X',
      X = {[+x+]} ⊎ X' ∧
      𝑥 = f x ∧
      𝑋 = gmultiset_map f X'.
  Proof.
    intros (X1 & X2 & -> & (x & -> & ->)%symmetry%gmultiset_mapｰsingletonｰinv & Heq)%gmultiset_mapｰdisj_unionｰinv.
    eauto.
  Qed.
  Lemma gmultiset_mapｰdisj_unionｰsingletonｰrｰinv X 𝑥 𝑋 :
    gmultiset_map f X = 𝑋 ⊎ {[+𝑥+]} →
      ∃ X' x,
      X = X' ⊎ {[+x+]} ∧
      𝑋 = gmultiset_map f X' ∧
      𝑥 = f x.
  Proof.
    setoid_rewrite (comm (⊎)) at 1 3.
    intros (x & X' & -> & -> & ->)%gmultiset_mapｰdisj_unionｰsingletonｰlｰinv.
    eauto.
  Qed.
End map.

Section list_to_set_disj.
  Context `{Countable A}.

  Implicit Type x y : A.
  Implicit Type l : list A.

  Lemma list_to_set_disjｰempty l :
    list_to_set_disj l =@{gmultiset _} ∅ ↔
    l = [].
  Proof.
    split.
    - destruct l as [| x l]; first done.
      multiset_solver.
    - intros ->.
      apply list_to_set_disj_nil.
  Qed.

  Lemma list_to_set_disjｰsnoc l x :
    list_to_set_disj (l ++ [x]) =@{gmultiset _} {[+x+]} ⊎ list_to_set_disj l.
  Proof.
    rewrite list_to_set_disj_app list_to_set_disj_cons right_id (comm (⊎)) //.
  Qed.
End list_to_set_disj.

Section disj_union_list.
  Context `{Countable A}.

  Implicit Type x y : A.
  Implicit Type X Y : gmultiset A.
  Implicit Type Xs Ys : list $ gmultiset A.

  Lemma gmultisetｰdisj_union_listｰempty Xs :
    ⋃+ Xs = ∅ ↔
      ∀ X,
      X ∈ Xs →
      X = ∅.
  Proof.
    setoid_rewrite gmultisetｰemptyｰelem_of.
    setoid_rewrite elem_of_gmultiset_disj_union_list.
    naive_solver.
  Qed.
  Lemma gmultisetｰdisj_union_listｰreplicateｰempty n :
    ⋃+ replicate n ∅ =@{gmultiset A} ∅.
  Proof.
    apply gmultisetｰdisj_union_listｰempty. intros X (-> & _)%elem_of_replicate => //.
  Qed.

  Lemma gmultisetｰdisj_union_listｰdelete Xs i X :
    Xs !! i = Some X →
    ⋃+ (delete i Xs) = ⋃+ Xs ∖ X.
  Proof.
    intros Hlookup.
    rewrite {2}(delete_Permutation Xs i X) //.
    multiset_solver.
  Qed.
  Lemma gmultisetｰdisj_union_listｰdelete' Xs i X :
    Xs !! i = Some X →
    ⋃+ Xs = X ⊎ ⋃+ (delete i Xs).
  Proof.
    intros Hlookup.
    rewrite {1}(delete_Permutation Xs i X) //.
  Qed.

  Lemma gmultisetｰdisj_union_listｰinsert Xs i X :
    is_Some (Xs !! i) →
    ⋃+ <[i := X]> Xs = X ⊎ ⋃+ (delete i Xs).
  Proof.
    intros (Y & Hlookup).
    opose proof* (lookup_lt_Some Xs i Y); first done.
    rewrite (gmultisetｰdisj_union_listｰdelete' (<[i := X]> Xs) i X).
    { rewrite list_lookup_insert_eq //. }
    rewrite listｰdeleteｰinsertｰeq //.
  Qed.
  Lemma gmultisetｰdisj_union_listｰinsertｰid Xs i X :
    Xs !! i = Some X →
    ⋃+ <[i := X]> Xs = ⋃+ Xs.
  Proof.
    intros Hlookup.
    rewrite gmultisetｰdisj_union_listｰinsert //.
    rewrite {2}(delete_Permutation Xs i X) //.
  Qed.
  Lemma gmultisetｰdisj_union_listｰinsertｰdisj_unionｰl Xs i X1 X2 :
    Xs !! i = Some X2 →
    ⋃+ <[i := X1 ⊎ X2]> Xs = X1 ⊎ ⋃+ Xs.
  Proof.
    intros Hlookup.
    rewrite gmultisetｰdisj_union_listｰinsert //.
    rewrite -assoc. f_equal.
    rewrite -gmultisetｰdisj_union_listｰinsert //.
    rewrite gmultisetｰdisj_union_listｰinsertｰid //.
  Qed.
  Lemma gmultisetｰdisj_union_listｰinsertｰdisj_unionｰr Xs i X1 X2 :
    Xs !! i = Some X1 →
    ⋃+ <[i := X1 ⊎ X2]> Xs = X2 ⊎ ⋃+ Xs.
  Proof.
    intros Hlookup.
    rewrite (comm (⊎)) gmultisetｰdisj_union_listｰinsertｰdisj_unionｰl //.
  Qed.
End disj_union_list.
