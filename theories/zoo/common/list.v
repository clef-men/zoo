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

  Lemma app_not_nil l1 l2 :
    l1 ≠ [] ∨ l2 ≠ [] →
    l1 ++ l2 ≠ [].
  Proof.
    intros []; destruct l1; done.
  Qed.
  Lemma app_not_nil_l l1 l2 :
    l1 ≠ [] →
    l1 ++ l2 ≠ [].
  Proof.
    intros. apply app_not_nil. auto.
  Qed.
  Lemma app_not_nil_r l1 l2 :
    l2 ≠ [] →
    l1 ++ l2 ≠ [].
  Proof.
    intros. apply app_not_nil. auto.
  Qed.

  Lemma reverse_nil_iff l :
    reverse l = [] ↔
    l = [].
  Proof.
    destruct l as [| x l _] using rev_ind; first done.
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
  Lemma last_removelast l x :
    last l = Some x →
    l = removelast l ++ [x].
  Proof.
    destruct l as [| y l _] using rev_ind; first done.
    rewrite last_snoc removelast_last. naive_solver.
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

Section zip3_with.
  Context {A1 A2 A3 B : Type}.

  Implicit Types f : A1 → A2 → A3 → B.

  Fixpoint zip3_with f l1 l2 l3 :=
    match l1, l2, l3 with
    | x1 :: l1, x2 :: l2, x3 :: l3 =>
        f x1 x2 x3 :: zip3_with f l1 l2 l3
    | _, _, _ =>
        []
    end.
  #[global] Arguments zip3_with _ !_ !_ !_ / : assert.

  Lemma length_zip3_with f l1 l2 l3 :
    length l1 = length l2 →
    length l1 = length l3 →
    length (zip3_with f l1 l2 l3) = length l1.
  Proof.
    move: l2 l3. induction l1 => l2 l3; first done.
    destruct l2, l3; try done.
    naive_solver.
  Qed.

  Lemma lookup_zip3_with_Some f l1 l2 l3 i x :
    zip3_with f l1 l2 l3 !! i = Some x ↔
      ∃ x1 x2 x3,
      l1 !! i = Some x1 ∧
      l2 !! i = Some x2 ∧
      l3 !! i = Some x3 ∧
      x = f x1 x2 x3.
  Proof.
    move: l1 l2 l3. induction i => l1 l2 l3.
    all: destruct l1, l2, l3; try done.
    all: naive_solver.
  Qed.
End zip3_with.

Section foldri.
  Implicit Types i : nat.

  #[local] Fixpoint foldri' `(f : nat → A → B → B) acc l i :=
    match l with
    | [] =>
        acc
    | x :: l =>
        f i x (foldri' f acc l (S i))
    end.
  #[global] Arguments foldri' _ _ _ _ !_ _ / : assert.
  Definition foldri `(f : nat → A → B → B) acc l :=
    foldri' f acc l 0.

  #[local] Lemma foldri'_app `(f : nat → A → B → B) acc l1 l2 i :
    foldri' f acc (l1 ++ l2) i =
    foldri' f (foldri' f acc l2 (i + (length l1))) l1 i.
  Proof.
    move: i. induction l1 as [| x l1 IH] => i.
    - rewrite right_id //.
    - rewrite /= -Nat.add_succ_comm IH //.
  Qed.
  Lemma foldri_app `(f : nat → A → B → B) acc l1 l2 :
    foldri f acc (l1 ++ l2) =
    foldri f (foldri' f acc l2 (length l1)) l1.
  Proof.
    apply @foldri'_app.
  Qed.

  #[local] Lemma foldri'_fmap `(f : nat → A → B → B) `(g : C → A) acc l i :
    foldri' f acc (g <$> l) i = foldri' (λ i x, f i (g x)) acc l i.
  Proof.
    move: i. induction l as [| x l IH] => i /=; first done.
    rewrite IH //.
  Qed.
  Lemma foldri_fmap `(f : nat → A → B → B) `(g : C → A) acc l :
    foldri f acc (g <$> l) = foldri (λ i x, f i (g x)) acc l.
  Proof.
    apply foldri'_fmap.
  Qed.

  #[local] Lemma foldri'_comm `(f : nat → A → B → B) `(g : B → C) h acc l i :
    ( ∀ i x acc,
      h i x (g acc) = g (f i x acc)
    ) →
    foldri' h (g acc) l i = g (foldri' f acc l i).
  Proof.
    intros Hh.
    move: i. induction l as [| x l IH] => i /=; first done.
    rewrite IH //.
  Qed.
  Lemma foldri_comm `(f : nat → A → B → B) `(g : B → C) h acc l :
    ( ∀ i x acc,
      h i x (g acc) = g (f i x acc)
    ) →
    foldri h (g acc) l = g (foldri f acc l).
  Proof.
    apply foldri'_comm.
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

Section Forall.
  Context `(P : A → Prop).

  Lemma Forall_elem_of l x :
    Forall P l →
    x ∈ l →
    P x.
  Proof.
    rewrite Forall_forall. auto.
  Qed.
End Forall.

Section Forall'.
  Context `(P : A → Prop).

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
  Context `(P : nat → A → Prop).

  #[local] Fixpoint Foralli' l i :=
    match l with
    | [] =>
        True
    | x :: l =>
        P i x ∧ Foralli' l (S i)
    end.
  #[global] Arguments Foralli' !_ _ / : assert.
  Definition Foralli l :=
    Foralli' l 0.

  #[local] Lemma Foralli'_lookup_1 l i j x :
    Foralli' l i →
    l !! j = Some x →
    P (i + j) x.
  Proof.
    move: l i. induction j => l i.
    all: destruct l; first done.
    - rewrite right_id. naive_solver.
    - rewrite -Nat.add_succ_comm. naive_solver.
  Qed.
  Lemma Foralli_lookup_1 {l} i x :
    Foralli l →
    l !! i = Some x →
    P i x.
  Proof.
    apply Foralli'_lookup_1.
  Qed.

  Lemma Foralli'_lookup_2 l i :
    (∀ j x, l !! j = Some x → P (i + j) x) →
    Foralli' l i.
  Proof.
    move: i. induction l as [| x l IH] => i H; first done.
    split.
    - specialize (H 0). rewrite right_id in H. auto.
    - apply IH => j y.
      rewrite Nat.add_succ_comm. naive_solver.
  Qed.
  Lemma Foralli_lookup_2 l :
    (∀ i x, l !! i = Some x → P i x) →
    Foralli l.
  Proof.
    apply (Foralli'_lookup_2 l 0).
  Qed.

  Lemma Foralli_lookup l :
    Foralli l ↔
    ∀ i x, l !! i = Some x → P i x.
  Proof.
    split.
    - eauto using Foralli_lookup_1.
    - apply Foralli_lookup_2.
  Qed.
End Foralli.

Section Forall2.
  Context `(P : A1 → A1 → Prop).

  Lemma Forall2_insert_l {l1 l2} i x1 x2 :
    l2 !! i = Some x2 →
    Forall2 P l1 l2 →
    P x1 x2 →
    Forall2 P (<[i := x1]> l1) l2.
  Proof.
    intros Hl2_lookup H HP.
    rewrite -(list_insert_id l2 i x2) //.
    apply Forall2_insert; done.
  Qed.
  Lemma Forall2_insert_r {l1 l2} i x1 x2 :
    l1 !! i = Some x1 →
    Forall2 P l1 l2 →
    P x1 x2 →
    Forall2 P l1 (<[i := x2]> l2).
  Proof.
    intros Hl1_lookup H HP.
    rewrite -(list_insert_id l1 i x1) //.
    apply Forall2_insert; done.
  Qed.
End Forall2.

Section Forall2'.
  Context `(P : A1 → A2 → Prop).

  Fixpoint Forall2' l1 l2 :=
    match l1, l2 with
    | [], [] =>
        True
    | x1 :: l1, x2 :: l2 =>
        P x1 x2 ∧ Forall2' l1 l2
    | _, _ =>
        False
    end.
  #[global] Arguments Forall2' !_ !_ / : assert.

  Lemma Forall2'_Forall2 l1 l2 :
    Forall2' l1 l2 ↔ Forall2 P l1 l2.
  Proof.
    move: l2. induction l1 => l2.
    all: destruct l2; try done.
    all: split; try naive_solver.
    - intros ?%Forall2_nil_cons_inv. done.
    - intros ?%Forall2_cons_nil_inv. done.
    - rewrite Forall2_cons. naive_solver.
  Qed.

  #[global] Instance Forall2'_dec `{!RelDecision P} :
    RelDecision Forall2'.
  Proof.
    refine (
      fix go l1 l2 : Decision (Forall2' l1 l2) :=
        match l1, l2 with
        | [], [] =>
            left _
        | x1 :: l1, x2 :: l2 =>
            cast_if_and
              (decide (P x1 x2))
              (go l1 l2)
        | _, _ =>
            right _
        end
    ).
    all: clear go.
    all: abstract first [constructor; done | inv 1; done].
  Defined.

  Lemma Forall2'_length l1 l2 :
    Forall2' l1 l2 →
    length l1 = length l2.
  Proof.
    rewrite Forall2'_Forall2. apply Forall2_length.
  Qed.
End Forall2'.

Section Forall2'.
  Context `(P : A → A → Prop).

  Lemma Forall2'_refl :
    (∀ x, P x x) →
    Reflexive (Forall2' P).
  Proof.
    intros ? l. induction l; done.
  Defined.
  #[global] Instance Forall2'_reflexive `{!Reflexive P} :
    Reflexive (Forall2' P).
  Proof.
    apply Forall2'_refl. done.
  Qed.

  Lemma Forall2'_sym :
    (∀ x1 x2, P x1 x2 → P x2 x1) →
    Symmetric (Forall2' P).
  Proof.
    intros ? l1. induction l1 => l2.
    all: destruct l2; naive_solver.
  Defined.
  #[global] Instance Forall2'_symmetric `{!Symmetric P} :
    Symmetric (Forall2' P).
  Proof.
    apply Forall2'_sym. done.
  Qed.

  Lemma Forall2'_trans :
    (∀ x1 x2 x3, P x1 x2 → P x2 x3 → P x1 x3) →
    Transitive (Forall2' P).
  Proof.
    intros ? l1. induction l1 => l2 l3.
    all: destruct l2, l3; naive_solver.
  Defined.
  #[global] Instance Forall2'_transitive `{!Transitive P} :
    Transitive (Forall2' P).
  Proof.
    apply Forall2'_trans. done.
  Defined.
End Forall2'.

Section Forall2i.
  Context `(P : nat → A1 → A2 → Prop).

  #[local] Fixpoint Forall2i' l1 l2 i :=
    match l1, l2 with
    | [], [] =>
        True
    | x1 :: l1, x2 :: l2 =>
        P i x1 x2 ∧ Forall2i' l1 l2 (S i)
    | _, _ =>
        False
    end.
  #[global] Arguments Forall2i' !_ !_ _ / : assert.
  Definition Forall2i l1 l2 :=
    Forall2i' l1 l2 0.

  #[local] Lemma Forall2i'_length l1 l2 i :
    Forall2i' l1 l2 i →
    length l1 = length l2.
  Proof.
    move: l2 i. induction l1.
    all: destruct l2; first done.
    all: naive_solver.
  Qed.
  Lemma Forall2i_length l1 l2 :
    Forall2i l1 l2 →
    length l1 = length l2.
  Proof.
    apply Forall2i'_length.
  Qed.

  #[local] Lemma Forall2i'_lookup_lr l1 l2 i j x1 x2 :
    Forall2i' l1 l2 i →
    l1 !! j = Some x1 →
    l2 !! j = Some x2 →
    P (i + j) x1 x2.
  Proof.
    move: l1 l2 i. induction j => l1 l2 i.
    all: destruct l1; first done.
    all: destruct l2; first done.
    - rewrite right_id. naive_solver.
    - rewrite -Nat.add_succ_comm. naive_solver.
  Qed.
  Lemma Forall2i_lookup_lr {l1 l2} i x1 x2 :
    Forall2i l1 l2 →
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    P i x1 x2.
  Proof.
    apply Forall2i'_lookup_lr.
  Qed.

  Lemma Forall2i_lookup_r l1 l2 i x1 :
    Forall2i l1 l2 →
    l1 !! i = Some x1 →
      ∃ x2,
      l2 !! i = Some x2 ∧
      P i x1 x2.
  Proof.
    intros H Hlookup1.
    opose proof* Forall2i_length as Hlen; first done.
    destruct (lookup_lt_is_Some_2 l2 i) as (x2 & Hlookup2).
    { rewrite -Hlen. eapply lookup_lt_Some. done. }
    eauto using Forall2i_lookup_lr.
  Qed.
  Lemma Forall2i_lookup_l l1 l2 i x2 :
    Forall2i l1 l2 →
    l2 !! i = Some x2 →
      ∃ x1,
      l1 !! i = Some x1 ∧
      P i x1 x2.
  Proof.
    intros H Hlookup2.
    opose proof* Forall2i_length as Hlen; first done.
    destruct (lookup_lt_is_Some_2 l1 i) as (x1 & Hlookup1).
    { rewrite Hlen. eapply lookup_lt_Some. done. }
    eauto using Forall2i_lookup_lr.
  Qed.

  #[local] Lemma Forall2i'_same_length_lookup_2 l1 l2 i :
    length l1 = length l2 →
    ( ∀ j x1 x2,
      l1 !! j = Some x1 →
      l2 !! j = Some x2 →
      P (i + j) x1 x2
    ) →
    Forall2i' l1 l2 i.
  Proof.
    move: l2 i. induction l1 as [| x1 l1 IH] => l2 i.
    all: destruct l2 as [| x2 l2]; try done.
    intros [= Hlen] H. split.
    - specialize (H 0). rewrite right_id in H. naive_solver.
    - apply IH; first done. intros j.
      specialize (H (S j)). rewrite -Nat.add_succ_comm // in H.
  Qed.
  Lemma Forall2i_same_length_lookup_2 l1 l2 :
    length l1 = length l2 →
    ( ∀ i x1 x2,
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      P i x1 x2
    ) →
    Forall2i l1 l2.
  Proof.
    intros.
    apply Forall2i'_same_length_lookup_2; done.
  Qed.
  Lemma Forall2i_same_length_lookup l1 l2 :
    Forall2i l1 l2 ↔
      length l1 = length l2 ∧
        ∀ i x1 x2,
        l1 !! i = Some x1 →
        l2 !! i = Some x2 →
        P i x1 x2.
  Proof.
    split.
    - intros H.
      opose proof* Forall2i_length as Hlen; first done.
      eauto using Forall2i_lookup_lr.
    - intros (? & ?).
      auto using Forall2i_same_length_lookup_2.
  Qed.
End Forall2i.

Section fmap.
  Context {A B : Type}.

  Implicit Types x : A.
  Implicit Types 𝑥 : B.
  Implicit Types l : list A.
  Implicit Types 𝑙 : list B.
  Implicit Types f : A → B.

  Lemma fmap_app_cons_inv f l 𝑙1 𝑥 𝑙2 :
    f <$> l = 𝑙1 ++ 𝑥 :: 𝑙2 →
      ∃ l1 x l2,
      l = l1 ++ x :: l2 ∧
      𝑙1 = f <$> l1 ∧
      𝑥 = f x ∧
      𝑙2 = f <$> l2.
  Proof.
    intros (l1 & ? & -> & (x & l2 & -> & -> & ->)%symmetry%fmap_cons_inv & ->)%fmap_app_inv.
    naive_solver.
  Qed.

  Lemma list_fmap_alt_Forall2_l f 𝑙 l :
    Forall2 (λ b a, b = f a) 𝑙 l →
    𝑙 = f <$> l.
  Proof.
    rewrite list_eq_Forall2 Forall2_fmap_r //.
  Qed.
  Lemma list_fmap_alt_Forall2_r f l 𝑙 :
    Forall2 (λ a b, f a = b) l 𝑙 →
    𝑙 = f <$> l.
  Proof.
    rewrite list_eq_Forall2 -Forall2_fmap_l //.
  Qed.
End fmap.

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

  Lemma slice_0 n l :
    slice 0 n l = take n l.
  Proof.
    done.
  Qed.
End slice.

Create HintDb simpl_length.
Hint Rewrite
  @length_reverse
  @length_app
  @length_insert
  @length_take
  @length_drop
  @length_fmap
  @length_replicate
  @length_seq
  @length_zip_with
  @length_zip3_with
: simpl_length.

Tactic Notation "simpl_length" :=
  autorewrite with simpl_length; try done.
Tactic Notation "simpl_length" "/=" :=
  repeat (progress csimpl in * || simpl_length).
Tactic Notation "simpl_length" "in" ne_hyp_list(Hs) :=
  autorewrite with simpl_length in Hs; try done.
Tactic Notation "simpl_length" "/=" "in" ne_hyp_list(Hs) :=
  repeat (progress csimpl in * || simpl_length in Hs).
Tactic Notation "simpl_length" "in" "*" :=
  autorewrite with simpl_length in *; try done.
Tactic Notation "simpl_length" "/=" "in" "*" :=
  repeat (progress csimpl in * || simpl_length in * ).
