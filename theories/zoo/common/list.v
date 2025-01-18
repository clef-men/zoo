From stdpp Require Export
  list.

From zoo Require Import
  prelude.
From zoo.common Require Import
  math.
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

  Lemma length_lookup_last l i :
    is_Some (l !! i) →
    l !! S i = None →
    length l = S i.
  Proof.
    intros ?%lookup_lt_is_Some ?%lookup_ge_None. lia.
  Qed.

  Lemma tail_app l1 l2 :
    l1 ≠ [] →
    tail (l1 ++ l2) = tail l1 ++ l2.
  Proof.
    destruct l1; done.
  Qed.

  Lemma head_app_cons l1 x l2 :
    head (l1 ++ x :: l2) = head (l1 ++ [x]).
  Proof.
    move: l1 x. induction l2 as [| x' l2 IH] => l1 x; first done.
    rewrite (assoc _ l1 [x]) IH -assoc head_snoc_snoc //.
  Qed.
  Lemma head_drop_Some l i x :
    l !! i = Some x →
    head (drop i l) = Some x.
  Proof.
    intros Hlookup.
    assert (length (take i l) = i) as Hlength_take.
    { apply lookup_lt_Some in Hlookup. rewrite length_take. lia. }
    apply take_drop_middle in Hlookup as <-.
    rewrite drop_app Hlength_take Nat.sub_diag skipn_all2 //; first lia.
  Qed.
  Lemma head_drop l i :
    head (drop i l) = l !! i.
  Proof.
    destruct (l !! i) as [x |] eqn:Hlookup.
    - apply head_drop_Some. done.
    - rewrite skipn_all2 // -lookup_ge_None //.
  Qed.

  Lemma last_cons' x l :
    last (x :: l) = Some $ default x (last l).
  Proof.
    rewrite last_cons. destruct (last l); done.
  Qed.
  Lemma last_take l i x :
    l !! i = Some x →
    last (take (S i) l) = Some x.
  Proof.
    intros Hlookup.
    assert (length (take i l) = i) as Hlength_take.
    { apply lookup_lt_Some in Hlookup. rewrite length_take. lia. }
    apply take_drop_middle in Hlookup as <-.
    rewrite take_app Hlength_take Nat.sub_succ_l // Nat.sub_diag last_snoc //.
  Qed.
  Lemma last_take' l i :
    is_Some (l !! i) →
    last (take i l) = nat_elim None (l !!.) i.
  Proof.
    intros Hlookup.
    destruct i as [| i]; first done.
    odestruct (lookup_lt_is_Some_2 l i) as (x & Hlookup').
    { apply lookup_lt_is_Some in Hlookup. lia. }
    rewrite /= Hlookup'. apply last_take. done.
  Qed.

  Lemma drop_lookup_None l i :
    l !! i = None →
    drop i l = [].
  Proof.
    intros Hlookup.
    apply drop_ge, lookup_ge_None_1. done.
  Qed.
End basic.

Section zip.
  Context {A1 A2 : Type}.

  Lemma prod_map_zip {B1 B2} (f1 : A1 → B1) (f2 : A2 → B2) l1 l2 :
    prod_map f1 f2 <$> (zip l1 l2) = zip (f1 <$> l1) (f2 <$> l2).
  Proof.
    move: l2. induction l1 as [| x1 l1 IH]; intros [| x2 l2]; try done.
    cbn. rewrite IH //.
  Qed.
End zip.

Section foldri.
  Context {A B : Type}.

  Fixpoint foldri' (f : nat → A → B → B) acc l i :=
    match l with
    | [] =>
        acc
    | x :: l =>
        f i x (foldri' f acc l (S i))
    end.
  #[global] Arguments foldri' _ _ !_ _ / : assert.
  Definition foldri f acc l :=
    foldri' f acc l 0.

  Lemma foldri'_app f acc l1 l2 i :
    foldri' f acc (l1 ++ l2) i =
    foldri' f (foldri' f acc l2 (i + (length l1))) l1 i.
  Proof.
    move: i. induction l1 as [| x l1 IH] => i.
    - rewrite right_id //.
    - rewrite /= -Nat.add_succ_comm IH //.
  Qed.
  Lemma foldri_app f acc l1 l2 :
    foldri f acc (l1 ++ l2) =
    foldri f (foldri' f acc l2 (length l1)) l1.
  Proof.
    apply foldri'_app.
  Qed.
End foldri.

Section foldr2.
  Context {A1 A2 B : Type}.

  Fixpoint foldr2 (f : A1 → A2 → B → B) acc l1 l2 :=
    match l1 with
    | [] =>
        acc
    | x1 :: l1 =>
        match l2 with
        | [] =>
            acc
        | x2 :: l2 =>
            f x1 x2 (foldr2 f acc l1 l2)
        end
    end.
  #[global] Arguments foldr2 _ _ !_ !_ / : assert.

  Lemma foldr2_app f acc l11 l12 l21 l22 :
    length l11 = length l21 →
      foldr2 f acc (l11 ++ l12) (l21 ++ l22) =
      foldr2 f (foldr2 f acc l12 l22) l11 l21.
  Proof.
    move: l21. induction l11 as [| x1 l11 IH] => l21 Hlength.
    - destruct l21; done.
    - destruct l21; first done.
      simpl. f_equal. naive_solver.
  Qed.
End foldr2.

Section Forall'.
  Context {A} (P : A → Prop).

  Fixpoint Forall' l :=
    match l with
    | [] =>
        True
    | x :: l =>
        P x ∧ Forall' l
    end.
  #[global] Arguments Forall' !_ / : assert.

  Lemma Forall'_Forall l :
    Forall' l ↔ Forall P l.
  Proof.
    induction l; first done.
    rewrite Forall_cons. naive_solver.
  Qed.
End Forall'.

Section Foralli.
  Context {A} (P : nat → A → Prop).

  Fixpoint Foralli' l i :=
    match l with
    | [] =>
        True
    | x :: l =>
        P i x ∧ Foralli' l (S i)
    end.
  #[global] Arguments Foralli' !_ _ / : assert.
  Definition Foralli l :=
    Foralli' l 0.

  Lemma Foralli'_lookup l i j x :
    Foralli' l i →
    l !! j = Some x →
    P (i + j) x.
  Proof.
    move: i j. induction l as [| y l IH] => i j H Hlookup; first done.
    destruct j.
    - rewrite right_id. naive_solver.
    - rewrite -Nat.add_succ_comm.
      apply (IH (S i) j); [naive_solver | done].
  Qed.
  Lemma Foralli_lookup {l} i x :
    Foralli l →
    l !! i = Some x →
    P i x.
  Proof.
    apply Foralli'_lookup.
  Qed.
End Foralli.

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
    - rewrite !length_insert //.
    - exists (λ j, if decide (j = i1) then i2 else if decide (j = i2) then i1 else j). split.
      + intros j1 j2. repeat case_decide; naive_solver.
      + intros j. repeat case_decide; subst.
        * rewrite list_lookup_insert // length_insert //.
        * rewrite list_lookup_insert_ne // list_lookup_insert //.
        * rewrite list_lookup_insert_ne // list_lookup_insert_ne //.
  Qed.
End Permutation.

Section slice.
  Context {A : Type}.

  Implicit Types x : A.
  Implicit Types l : list A.

  Definition slice i n l :=
    take n (drop i l).

  Lemma slice_cons i n x l :
    l !! i = Some x →
    x :: slice (S i) n l = slice i (S n) l.
  Proof.
    intros Hlookup.
    rewrite -firstn_cons -drop_S //.
  Qed.
  Lemma slice_cons' i n x l :
    l !! i = Some x →
    n ≠ 0 →
    x :: slice (S i) (n - 1) l = slice i n l.
  Proof.
    intros Hlookup (n' & ->)%Nat.neq_0_r.
    rewrite Nat.sub_succ right_id.
    apply slice_cons. done.
  Qed.
  Lemma slice_snoc i n l x :
    l !! (i + n) = Some x →
    slice i n l ++ [x] = slice i (S n) l.
  Proof.
    intros Hlookup.
    rewrite -take_S_r // lookup_drop //.
  Qed.

  Lemma slice_length i n l :
    i + n ≤ length l →
    length (slice i n l) = n.
  Proof.
    rewrite length_take length_drop. lia.
  Qed.

  Lemma slice_lookup_Some_inv i n l k x :
    slice i n l !! k = Some x →
    k < n.
  Proof.
    intros (_ & ?)%lookup_take_Some. done.
  Qed.
End slice.
