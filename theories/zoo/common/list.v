Require stdpp.list.
Require stdpp.sorting.

Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.options.

Export stdpp.list.
Export stdpp.sorting.

Create HintDb simp_length.

#[global] Hint Rewrite
  @length_reverse
  @length_app
  @length_insert
  @length_take
  @length_drop
  @length_fmap
  @length_replicate
  @length_seq
  @length_seqZ
  @length_zip_with
: simp_length.

Tactic Notation "simp_length" :=
  autorewrite with simp_length; try done.
Tactic Notation "simp_length" "/=" :=
  repeat (progress csimpl in * || simp_length).
Tactic Notation "simp_length" "in" ne_hyp_list(Hs) :=
  autorewrite with simp_length in Hs; try done.
Tactic Notation "simp_length" "/=" "in" ne_hyp_list(Hs) :=
  repeat (progress csimpl in * || simp_length in Hs).
Tactic Notation "simp_length" "in" "*" :=
  autorewrite with simp_length in *; try done.
Tactic Notation "simp_length" "/=" "in" "*" :=
  repeat (progress csimpl in * || simp_length in * ).

Section basic.
  Context {A : Type}.

  Implicit Type x y z : A.
  Implicit Type l : list A.

  Lemma listｰeq l1 l2 :
    l1 = l2 ↔
      length l1 = length l2 ∧
        ∀ i x1 x2,
        l1 !! i = Some x1 →
        l2 !! i = Some x2 →
        x1 = x2.
  Proof.
    rewrite list_eq_Forall2 Forall2_same_length_lookup //.
  Qed.

  Lemma appｰnotｰnil l1 l2 :
    l1 ≠ [] ∨ l2 ≠ [] →
    l1 ++ l2 ≠ [].
  Proof.
    intros []; destruct l1; done.
  Qed.
  Lemma appｰnotｰnilｰl l1 l2 :
    l1 ≠ [] →
    l1 ++ l2 ≠ [].
  Proof.
    intros. apply appｰnotｰnil. auto.
  Qed.
  Lemma appｰnotｰnilｰr l1 l2 :
    l2 ≠ [] →
    l1 ++ l2 ≠ [].
  Proof.
    intros. apply appｰnotｰnil. auto.
  Qed.

  Lemma lookupｰappｰrｰSome l1 l2 i y :
    length l1 ≤ i →
    l2 !! (i - length l1) = Some y →
    (l1 ++ l2) !! i = Some y.
  Proof.
    intros.
    rewrite lookup_app_r //.
  Qed.
  Lemma lookupｰconsｰrｰSome x l i y :
    0 < i →
    l !! (i - 1) = Some y →
    (x :: l) !! i = Some y.
  Proof.
    apply (lookupｰappｰrｰSome [_]).
  Qed.

  Lemma elem_ofｰappｰl l1 l2 x :
    x ∈ l1 →
    x ∈ l1 ++ l2.
  Proof.
    rewrite elem_of_app. auto.
  Qed.
  Lemma elem_ofｰappｰr l1 l2 x :
    x ∈ l2 →
    x ∈ l1 ++ l2.
  Proof.
    rewrite elem_of_app. auto.
  Qed.

  Lemma reverseｰnilｰiff l :
    reverse l = [] ↔
    l = [].
  Proof.
    destruct l as [| x l _] using rev_ind; first done.
    rewrite reverse_snoc app_nil. naive_solver.
  Qed.

  Lemma foldrｰinsertｰstrong `(f : A → B → B) comp l i x y acc :
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
  Lemma foldrｰinsertｰstrong' op `{!Assoc (=) op} `{!Comm (=) op} comp l i x y acc :
    l !! i = Some x →
    ( ∀ acc,
      op (comp y x) acc = op y (op x acc)
    ) →
    foldr op acc (<[i := comp y x]> l) = op y (foldr op acc l).
  Proof.
    intros Hlookup Hcomp.
    apply foldrｰinsertｰstrong; try done.
    intros. rewrite assoc (comm _ _ y) //.
  Qed.
  Lemma foldrｰinsert op `{!Assoc (=) op} `{!Comm (=) op} l i x y acc :
    l !! i = Some x →
    foldr op acc (<[i := op y x]> l) = op y (foldr op acc l).
  Proof.
    intros Hlookup.
    apply: foldrｰinsertｰstrong'; done.
  Qed.

  Lemma lengthｰlookupｰlast l i :
    is_Some (l !! i) →
    l !! ˖i = None →
    length l = ˖i.
  Proof.
    intros ?%lookup_lt_is_Some ?%lookup_ge_None. lia.
  Qed.

  Lemma tailｰapp l1 l2 :
    l1 ≠ [] →
    tail (l1 ++ l2) = tail l1 ++ l2.
  Proof.
    destruct l1; done.
  Qed.
  Lemma lengthｰtail l :
    length (tail l) ≤ length l.
  Proof.
    destruct l => /=; lia.
  Qed.

  Lemma headｰapp l1 l2 :
    0 < length l1 →
    head (l1 ++ l2) = head l1.
  Proof.
    destruct l1; naive_solver lia.
  Qed.
  Lemma headｰappｰcons l1 x l2 :
    head (l1 ++ x :: l2) = head (l1 ++ [x]).
  Proof.
    rewrite (assoc _ _ [_]) headｰapp //.
    { rewrite length_app /=. lia. }
  Qed.
  Lemma headｰdropｰSome l i x :
    l !! i = Some x →
    head (drop i l) = Some x.
  Proof.
    intros Hlookup.
    assert (length (take i l) = i) as Hlength_take.
    { apply lookup_lt_Some in Hlookup. rewrite length_take. lia. }
    apply take_drop_middle in Hlookup as <-.
    rewrite drop_app Hlength_take Nat.sub_diag skipn_all2 //; first lia.
  Qed.
  Lemma headｰdrop l i :
    head (drop i l) = l !! i.
  Proof.
    destruct (l !! i) as [x |] eqn:Hlookup.
    - apply headｰdropｰSome. done.
    - rewrite skipn_all2 // -lookup_ge_None //.
  Qed.

  Lemma hdｰcorrect default l x :
    0 < length l →
    hd default l = x →
    head l = Some x.
  Proof.
    destruct l; naive_solver lia.
  Qed.
  Lemma hdｰapp default l1 l2 :
    0 < length l1 →
    hd default (l1 ++ l2) = hd default l1.
  Proof.
    destruct l1; naive_solver lia.
  Qed.
  Lemma hdｰappｰcons default l1 x l2 :
    hd default (l1 ++ x :: l2) = hd default (l1 ++ [x]).
  Proof.
    rewrite (assoc _ _ [_]) hdｰapp //.
    { rewrite length_app /=. lia. }
  Qed.
  Lemma hdｰdropｰSome default l i x :
    l !! i = Some x →
    hd default (drop i l) = x.
  Proof.
    intros Hlookup.
    assert (length (take i l) = i) as Hlength_take.
    { apply lookup_lt_Some in Hlookup. rewrite length_take. lia. }
    apply take_drop_middle in Hlookup as <-.
    rewrite drop_app Hlength_take Nat.sub_diag skipn_all2 //; first lia.
  Qed.

  Lemma lastｰcons' x l :
    last (x :: l) = Some $ default x (last l).
  Proof.
    rewrite last_cons. destruct (last l); done.
  Qed.
  Lemma lastｰtake l i x :
    l !! i = Some x →
    last (take ˖i l) = Some x.
  Proof.
    intros Hlookup.
    assert (length (take i l) = i) as Hlength_take.
    { apply lookup_lt_Some in Hlookup. rewrite length_take. lia. }
    apply take_drop_middle in Hlookup as <-.
    rewrite take_app Hlength_take Nat.sub_succ_l // Nat.sub_diag last_snoc //.
  Qed.
  Lemma lastｰtake' l i :
    is_Some (l !! i) →
    last (take i l) = nat۰elim None (l !!.) i.
  Proof.
    intros Hlookup.
    destruct i as [| i]; first done.
    odestruct (lookup_lt_is_Some_2 l i) as (x & Hlookup').
    { apply lookup_lt_is_Some in Hlookup. lia. }
    rewrite /= Hlookup'. apply lastｰtake. done.
  Qed.
  Lemma lastｰremovelast l x :
    last l = Some x →
    l = removelast l ++ [x].
  Proof.
    destruct l as [| y l _] using rev_ind; first done.
    rewrite last_snoc removelast_last. naive_solver.
  Qed.

  Lemma dropｰlookupｰNone l i :
    l !! i = None →
    drop i l = [].
  Proof.
    intros Hlookup.
    apply drop_ge, lookup_ge_None_1. done.
  Qed.
  Lemma dropｰconsｰinv i l x l' :
    drop i l = x :: l' →
      l !! i = Some x ∧
      l' = drop ˖i l.
  Proof.
    intros Heq.
    apply (f_equal head) in Heq as Hlookup.
    rewrite headｰdrop /= in Hlookup.
    split; first done.
    apply drop_S in Hlookup.
    congruence.
  Qed.

  Lemma insertｰconsｰl i x y l :
    i = 0 →
    <[i := x]> (y :: l) = x :: l.
  Proof.
    intros ->.
    rewrite (insert_app_l [_]) //=. lia.
  Qed.
  Lemma insertｰconsｰr i x y l :
    0 < i →
    <[i := x]> (y :: l) = y :: <[i - 1 := x]> l.
  Proof.
    intros.
    rewrite (insert_app_r_alt [_]) //.
  Qed.

  Lemma insertｰappｰrｰ0 i x l1 l2 :
    i = length l1 →
    <[i := x]> (l1 ++ l2) = l1 ++ <[0 := x]> l2.
  Proof.
    intros ->.
    rewrite insert_app_r_alt // Nat.sub_diag //.
  Qed.

  Lemma listｰdeleteｰinsertｰeq l i x :
    i < length l →
    delete i (<[i := x]> l) = delete i l.
  Proof.
    intros Hi.
    rewrite insert_take_drop //.
    replace i with (length $ take i l) at 1 by (simp_length; lia).
    rewrite delete_middle delete_take_drop //.
  Qed.
End basic.

Section suffix.
  Context {A : Type}.

  Implicit Type x : A.
  Implicit Type l : list A.

  Lemma suffixｰtail l1 l2 :
    l1 `suffix_of` l2 →
    tail l1 `suffix_of` l2.
  Proof.
    destruct l1; first done.
    intros ?%suffix_cons_l. done.
  Qed.

  Lemma suffixｰfmap `(f : A → B) `{!Inj (=) (=) f} l1 l2 :
    suffix (f <$> l1) (f <$> l2) →
    suffix l1 l2.
  Proof.
    intros (l & (l21 & l22 & -> & <-%(inj _) & ->)%fmap_app_inv).
    exists l21. done.
  Qed.
End suffix.

Section seqZ.
  Lemma seqZｰprefix {i n1} n2 :
    (0 ≤ n2 ≤ n1)%Z →
    seqZ i n2 `prefix_of` seqZ i n1.
  Proof.
    intros.
    replace n1 with (n2 + (n1 - n2))%Z by lia.
    rewrite seqZ_app. 1,2: lia.
    eexists => //.
  Qed.

  Lemma seqZｰsuffix {i1 n1} i2 n2 :
    (i1 ≤ i2 ≤ i1 + n1)%Z →
    (i2 - i1 = n1 - n2)%Z →
    seqZ i2 n2 `suffix_of` seqZ i1 n1.
  Proof.
    intros.
    replace n1 with ((i2 - i1) + n2)%Z by lia.
    rewrite seqZ_app. 1,2: lia.
    replace (i1 + (i2 - i1))%Z with i2 by lia.
    eexists => //.
  Qed.
End seqZ.

Section zip.
  Context {A1 A2 : Type}.

  Lemma prod_mapｰzip {B1 B2} (f1 : A1 → B1) (f2 : A2 → B2) l1 l2 :
    prod_map f1 f2 <$> (zip l1 l2) = zip (f1 <$> l1) (f2 <$> l2).
  Proof.
    move: l2. induction l1 as [| x1 l1 IH]; intros [| x2 l2]; try done.
    cbn. rewrite IH //.
  Qed.
End zip.

Section zip3_with.
  Context {A1 A2 A3 B : Type}.

  Implicit Type f : A1 → A2 → A3 → B.

  Fixpoint zip3_with f l1 l2 l3 :=
    match l1, l2, l3 with
    | x1 :: l1, x2 :: l2, x3 :: l3 =>
        f x1 x2 x3 :: zip3_with f l1 l2 l3
    | _, _, _ =>
        []
    end.
  #[global] Arguments zip3_with _ !_ !_ !_ / : assert.

  Lemma lengthｰzip3_with f l1 l2 l3 :
    length l1 = length l2 →
    length l1 = length l3 →
    length (zip3_with f l1 l2 l3) = length l1.
  Proof.
    move: l2 l3. induction l1 => l2 l3; first done.
    destruct l2, l3; try done.
    naive_solver.
  Qed.

  Lemma lookupｰzip3_withｰSome f l1 l2 l3 i x :
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

#[global] Hint Rewrite
  @lengthｰzip3_with
: simp_length.

Section zip3.
  Context {A1 A2 A3 : Type}.

  Definition zip3 :=
    zip3_with (B := A1 * A2 * A3) $ λ x1 x2 x3,
      (x1, x2, x3).

  Lemma zip3ｰcons x1 l1 x2 l2 x3 l3 :
    zip3 (x1 :: l1) (x2 :: l2) (x3 :: l3) = (x1, x2, x3) :: zip3 l1 l2 l3.
  Proof.
    done.
  Qed.

  Lemma lengthｰzip3 l1 l2 l3 :
    length l1 = length l2 →
    length l1 = length l3 →
    length (zip3 l1 l2 l3) = length l1.
  Proof.
    apply lengthｰzip3_with.
  Qed.

  Lemma zipｰzip l1 l2 l3 :
    zip (zip l1 l2) l3 = zip3 l1 l2 l3.
  Proof.
    move: l2 l3. induction l1 as [| x1 l1 IH] => l2 l3 //.
    destruct l2 as [| x2 l2] => //.
    destruct l3 as [| x3 l3] => //.
    rewrite /= IH //.
  Qed.
End zip3.

#[global] Hint Rewrite
  @lengthｰzip3
: simp_length.

Section foldri.
  Implicit Type i : nat.

  Fixpoint foldri' `(f : nat → A → B → B) acc l i :=
    match l with
    | [] =>
        acc
    | x :: l =>
        f i x (foldri' f acc l ˖i)
    end.
  #[global] Arguments foldri' _ _ _ _ !_ _ / : assert.
  Definition foldri `(f : nat → A → B → B) acc l :=
    foldri' f acc l 0.

  #[local] Lemma foldri'ｰapp `(f : nat → A → B → B) acc l1 l2 i :
    foldri' f acc (l1 ++ l2) i =
    foldri' f (foldri' f acc l2 (i + (length l1))) l1 i.
  Proof.
    move: i. induction l1 as [| x l1 IH] => i.
    - rewrite right_id //.
    - rewrite /= -Nat.add_succ_comm IH //.
  Qed.
  Lemma foldriｰapp `(f : nat → A → B → B) acc l1 l2 :
    foldri f acc (l1 ++ l2) =
    foldri f (foldri' f acc l2 (length l1)) l1.
  Proof.
    apply @foldri'ｰapp.
  Qed.

  #[local] Lemma foldri'ｰfmap `(f : nat → A → B → B) `(g : C → A) acc l i :
    foldri' f acc (g <$> l) i = foldri' (λ i x, f i (g x)) acc l i.
  Proof.
    move: i. induction l as [| x l IH] => i /=; first done.
    rewrite IH //.
  Qed.
  Lemma foldriｰfmap `(f : nat → A → B → B) `(g : C → A) acc l :
    foldri f acc (g <$> l) = foldri (λ i x, f i (g x)) acc l.
  Proof.
    apply foldri'ｰfmap.
  Qed.

  #[local] Lemma foldri'ｰcomm `(f : nat → A → B → B) `(g : B → C) h acc l i :
    ( ∀ i x acc,
      h i x (g acc) = g (f i x acc)
    ) →
    foldri' h (g acc) l i = g (foldri' f acc l i).
  Proof.
    intros Hh.
    move: i. induction l as [| x l IH] => i /=; first done.
    rewrite IH //.
  Qed.
  Lemma foldriｰcomm `(f : nat → A → B → B) `(g : B → C) h acc l :
    ( ∀ i x acc,
      h i x (g acc) = g (f i x acc)
    ) →
    foldri h (g acc) l = g (foldri f acc l).
  Proof.
    apply foldri'ｰcomm.
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

  Lemma foldr2ｰapp f acc l11 l12 l21 l22 :
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

  Lemma Forallｰelem_of l x :
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

  Lemma Forall'ｰForall l :
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
        P i x ∧ Foralli' l ˖i
    end.
  #[global] Arguments Foralli' !_ _ / : assert.
  Definition Foralli l :=
    Foralli' l 0.

  #[local] Lemma Foralli'ｰlookup₁ l i j x :
    Foralli' l i →
    l !! j = Some x →
    P (i + j) x.
  Proof.
    move: l i. induction j => l i.
    all: destruct l; first done.
    - rewrite right_id. naive_solver.
    - rewrite -Nat.add_succ_comm. naive_solver.
  Qed.
  Lemma Foralliｰlookup₁ {l} i x :
    Foralli l →
    l !! i = Some x →
    P i x.
  Proof.
    apply Foralli'ｰlookup₁.
  Qed.

  Lemma Foralli'ｰlookup₂ l i :
    (∀ j x, l !! j = Some x → P (i + j) x) →
    Foralli' l i.
  Proof.
    move: i. induction l as [| x l IH] => i H; first done.
    split.
    - specialize (H 0). rewrite right_id in H. auto.
    - apply IH => j y.
      rewrite Nat.add_succ_comm. naive_solver.
  Qed.
  Lemma Foralliｰlookup₂ l :
    (∀ i x, l !! i = Some x → P i x) →
    Foralli l.
  Proof.
    apply (Foralli'ｰlookup₂ l 0).
  Qed.

  Lemma Foralliｰlookup l :
    Foralli l ↔
    ∀ i x, l !! i = Some x → P i x.
  Proof.
    split.
    - eauto using Foralliｰlookup₁.
    - apply Foralliｰlookup₂.
  Qed.
End Foralli.

Section Forall2.
  Context `(P : A1 → A1 → Prop).

  Lemma Forall2ｰinsertｰl {l1 l2} i x1 x2 :
    l2 !! i = Some x2 →
    Forall2 P l1 l2 →
    P x1 x2 →
    Forall2 P (<[i := x1]> l1) l2.
  Proof.
    intros Hl2_lookup H HP.
    rewrite -(list_insert_id l2 i x2) //.
    apply Forall2_insert; done.
  Qed.
  Lemma Forall2ｰinsertｰr {l1 l2} i x1 x2 :
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

  Lemma Forall2'ｰForall2 l1 l2 :
    Forall2' l1 l2 ↔ Forall2 P l1 l2.
  Proof.
    move: l2. induction l1 => l2.
    all: destruct l2; try done.
    all: split; try naive_solver.
    - intros ?%Forall2_nil_cons_inv. done.
    - intros ?%Forall2_cons_nil_inv. done.
    - rewrite Forall2_cons. naive_solver.
  Qed.

  #[global] Instance Forall2'ｰdec `{!RelDecision P} :
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

  Lemma Forall2'ｰlength l1 l2 :
    Forall2' l1 l2 →
    length l1 = length l2.
  Proof.
    rewrite Forall2'ｰForall2. apply Forall2_length.
  Qed.
End Forall2'.

Section Forall2'.
  Context `(P : A → A → Prop).

  Lemma Forall2'ｰrefl :
    (∀ x, P x x) →
    Reflexive (Forall2' P).
  Proof.
    intros ? l. induction l; done.
  Defined.
  #[global] Instance Forall2'ｰreflexive `{!Reflexive P} :
    Reflexive (Forall2' P).
  Proof.
    apply Forall2'ｰrefl. done.
  Qed.

  Lemma Forall2'ｰsym :
    (∀ x1 x2, P x1 x2 → P x2 x1) →
    Symmetric (Forall2' P).
  Proof.
    intros ? l1. induction l1 => l2.
    all: destruct l2; naive_solver.
  Defined.
  #[global] Instance Forall2'ｰsymmetric `{!Symmetric P} :
    Symmetric (Forall2' P).
  Proof.
    apply Forall2'ｰsym. done.
  Qed.

  Lemma Forall2'ｰtrans :
    (∀ x1 x2 x3, P x1 x2 → P x2 x3 → P x1 x3) →
    Transitive (Forall2' P).
  Proof.
    intros ? l1. induction l1 => l2 l3.
    all: destruct l2, l3; naive_solver.
  Defined.
  #[global] Instance Forall2'ｰtransitive `{!Transitive P} :
    Transitive (Forall2' P).
  Proof.
    apply Forall2'ｰtrans. done.
  Defined.
End Forall2'.

Section Forall2i.
  Context `(P : nat → A1 → A2 → Prop).

  #[local] Fixpoint Forall2i' l1 l2 i :=
    match l1, l2 with
    | [], [] =>
        True
    | x1 :: l1, x2 :: l2 =>
        P i x1 x2 ∧ Forall2i' l1 l2 ˖i
    | _, _ =>
        False
    end.
  #[global] Arguments Forall2i' !_ !_ _ / : assert.
  Definition Forall2i l1 l2 :=
    Forall2i' l1 l2 0.

  #[local] Lemma Forall2i'ｰlength l1 l2 i :
    Forall2i' l1 l2 i →
    length l1 = length l2.
  Proof.
    move: l2 i. induction l1.
    all: destruct l2; first done.
    all: naive_solver.
  Qed.
  Lemma Forall2iｰlength l1 l2 :
    Forall2i l1 l2 →
    length l1 = length l2.
  Proof.
    apply Forall2i'ｰlength.
  Qed.

  #[local] Lemma Forall2i'ｰlookupｰlr l1 l2 i j x1 x2 :
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
  Lemma Forall2iｰlookupｰlr {l1 l2} i x1 x2 :
    Forall2i l1 l2 →
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    P i x1 x2.
  Proof.
    apply Forall2i'ｰlookupｰlr.
  Qed.

  Lemma Forall2iｰlookupｰr l1 l2 i x1 :
    Forall2i l1 l2 →
    l1 !! i = Some x1 →
      ∃ x2,
      l2 !! i = Some x2 ∧
      P i x1 x2.
  Proof.
    intros H Hlookup1.
    opose proof* Forall2iｰlength as Hlen; first done.
    destruct (lookup_lt_is_Some_2 l2 i) as (x2 & Hlookup2).
    { rewrite -Hlen. eapply lookup_lt_Some. done. }
    eauto using Forall2iｰlookupｰlr.
  Qed.
  Lemma Forall2iｰlookupｰl l1 l2 i x2 :
    Forall2i l1 l2 →
    l2 !! i = Some x2 →
      ∃ x1,
      l1 !! i = Some x1 ∧
      P i x1 x2.
  Proof.
    intros H Hlookup2.
    opose proof* Forall2iｰlength as Hlen; first done.
    destruct (lookup_lt_is_Some_2 l1 i) as (x1 & Hlookup1).
    { rewrite Hlen. eapply lookup_lt_Some. done. }
    eauto using Forall2iｰlookupｰlr.
  Qed.

  #[local] Lemma Forall2i'ｰsame_lengthｰlookup₂ l1 l2 i :
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
      specialize (H ˖j). rewrite -Nat.add_succ_comm // in H.
  Qed.
  Lemma Forall2iｰsame_lengthｰlookup₂ l1 l2 :
    length l1 = length l2 →
    ( ∀ i x1 x2,
      l1 !! i = Some x1 →
      l2 !! i = Some x2 →
      P i x1 x2
    ) →
    Forall2i l1 l2.
  Proof.
    intros.
    apply Forall2i'ｰsame_lengthｰlookup₂; done.
  Qed.
  Lemma Forall2iｰsame_lengthｰlookup l1 l2 :
    Forall2i l1 l2 ↔
      length l1 = length l2 ∧
        ∀ i x1 x2,
        l1 !! i = Some x1 →
        l2 !! i = Some x2 →
        P i x1 x2.
  Proof.
    split.
    - intros H.
      opose proof* Forall2iｰlength as Hlen; first done.
      eauto using Forall2iｰlookupｰlr.
    - intros (? & ?).
      auto using Forall2iｰsame_lengthｰlookup₂.
  Qed.
End Forall2i.

Section fmap.
  Context {A B : Type}.

  Implicit Type x : A.
  Implicit Type 𝑥 : B.
  Implicit Type l : list A.
  Implicit Type 𝑙 : list B.
  Implicit Type f : A → B.

  Lemma fmapｰappｰconsｰinv f l 𝑙1 𝑥 𝑙2 :
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
  Lemma fmapｰsnocｰinv f l 𝑙 𝑥 :
    f <$> l = 𝑙 ++ [𝑥] →
      ∃ l' x,
      l = l' ++ [x] ∧
      𝑙 = f <$> l' ∧
      𝑥 = f x.
  Proof.
    intros (l' & x & ? & -> & -> & -> & ->%symmetry%fmap_nil_inv)%fmapｰappｰconsｰinv.
    eauto.
  Qed.

  Lemma listｰfmapｰaltｰForall2ｰl f 𝑙 l :
    Forall2 (λ b a, b = f a) 𝑙 l →
    𝑙 = f <$> l.
  Proof.
    rewrite list_eq_Forall2 Forall2_fmap_r //.
  Qed.
  Lemma listｰfmapｰaltｰForall2ｰr f l 𝑙 :
    Forall2 (λ a b, f a = b) l 𝑙 →
    𝑙 = f <$> l.
  Proof.
    rewrite list_eq_Forall2 -Forall2_fmap_l //.
  Qed.
End fmap.

Section Permutation.
  Context {A : Type}.

  Implicit Type x : A.
  Implicit Type l : list A.

  #[global] Instance Permutationｰdisjoint :
    Proper (Permutation ==> Permutation ==> iff) (disjoint (A := list A)).
  Proof.
    intros x1 x2 Hx l1 l2 Hl.
    rewrite /disjoint /set_disjoint_instance.
    setoid_rewrite Hx.
    setoid_rewrite Hl.
    done.
  Qed.

  Lemma Permutationｰswap' l i1 x1 i2 x2 :
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
        * rewrite list_lookup_insert_eq // length_insert //.
        * rewrite list_lookup_insert_ne // list_lookup_insert_eq //.
        * rewrite list_lookup_insert_ne // list_lookup_insert_ne //.
  Qed.
End Permutation.

Section slice.
  Context {A : Type}.

  Implicit Type x : A.
  Implicit Type l : list A.

  Definition slice i n l :=
    take n (drop i l).

  Lemma sliceｰcons i n x l :
    l !! i = Some x →
    x :: slice ˖i n l = slice i ˖n l.
  Proof.
    intros Hlookup.
    rewrite -firstn_cons -drop_S //.
  Qed.
  Lemma sliceｰcons' i n x l :
    l !! i = Some x →
    n ≠ 0 →
    x :: slice ˖i (n - 1) l = slice i n l.
  Proof.
    intros Hlookup (n' & ->)%Nat.neq_0_r.
    rewrite Nat.sub_succ right_id.
    apply sliceｰcons. done.
  Qed.
  Lemma sliceｰsnoc i n l x :
    l !! (i + n) = Some x →
    slice i n l ++ [x] = slice i ˖n l.
  Proof.
    intros Hlookup.
    rewrite -take_S_r // lookup_drop //.
  Qed.

  Lemma lengthｰslice i n l :
    length (slice i n l) = n `min` (length l - i).
  Proof.
    rewrite length_take length_drop //.
  Qed.
  Lemma lengthｰslice' i n l :
    i + n ≤ length l →
    length (slice i n l) = n.
  Proof.
    rewrite lengthｰslice. lia.
  Qed.

  Lemma sliceｰlookupｰSomeｰinv i n l k x :
    slice i n l !! k = Some x →
    k < n.
  Proof.
    intros (_ & ?)%lookup_take_Some. done.
  Qed.

  Lemma sliceｰ0 n l :
    slice 0 n l = take n l.
  Proof.
    done.
  Qed.
End slice.

#[global] Hint Rewrite
  @lengthｰslice
: simp_length.

Section with_slice.
  Context {A : Type}.

  Implicit Type x : A.
  Implicit Type l s : list A.

  Definition with_slice i n l s :=
    take i l ++ s ++ drop (i + n) l.

  Lemma lengthｰwith_slice i n l s :
    length (with_slice i n l s) = i `min` length l + length s + (length l - i - n).
  Proof.
    rewrite !length_app length_take length_drop. lia.
  Qed.
  Lemma lengthｰwith_slice' i n l s :
    i + n ≤ length l →
    length s = n →
    length (with_slice i n l s) = length l.
  Proof.
    intros.
    rewrite lengthｰwith_slice. lia.
  Qed.

  Lemma with_sliceｰ0 n l s :
    with_slice 0 n l s = s ++ drop n l.
  Proof.
    rewrite /with_slice //.
  Qed.
  Lemma with_sliceｰall n l s :
    length l ≤ n →
    with_slice 0 n l s = s.
  Proof.
    intros.
    rewrite with_sliceｰ0 skipn_all2 // right_id //.
  Qed.

  Lemma with_sliceｰappｰl i n l1 l2 s :
    i + n ≤ length l1 →
    with_slice i n (l1 ++ l2) s = with_slice i n l1 s ++ l2.
  Proof.
    intros.
    rewrite /with_slice take_app_le; first lia.
    rewrite drop_app_le // !assoc //.
  Qed.
  Lemma with_sliceｰappｰr i n l1 l2 s :
    length l1 ≤ i →
    with_slice i n (l1 ++ l2) s = l1 ++ with_slice (i - length l1) n l2 s.
  Proof.
    intros.
    rewrite /with_slice take_app_ge // drop_app_ge; first lia.
    rewrite Nat.add_sub_swap // !assoc //.
  Qed.
  Lemma with_sliceｰappｰlength n l1 l2 s :
    with_slice (length l1) n (l1 ++ l2) s = l1 ++ s ++ drop n l2.
  Proof.
    rewrite with_sliceｰappｰr // Nat.sub_diag with_sliceｰ0 //.
  Qed.
  Lemma with_sliceｰappｰlength' i n l1 l2 s :
    i = length l1 →
    with_slice i n (l1 ++ l2) s = l1 ++ s ++ drop n l2.
  Proof.
    intros ->.
    apply with_sliceｰappｰlength.
  Qed.

  Lemma with_sliceｰsliceｰnil i l s :
    with_slice i 0 l [] = l.
  Proof.
    rewrite /with_slice Nat.add_0_r left_id take_drop //.
  Qed.

  Lemma with_sliceｰsliceｰsnoc i n l s x :
    i + n < length l →
    length s = n →
    with_slice i ˖n l (s ++ [x]) = <[i + n := x]> (with_slice i n l s).
  Proof.
    intros.
    destruct (lookup_lt_is_Some_2 l (i + n)) as (y & Hlookup); first done.
    rewrite /with_slice.
    rewrite insert_app_r_alt length_take; first lia.
    rewrite Nat.min_l; first lia.
    rewrite insert_app_r_alt; first lia.
    replace (i + n - i - length s) with 0 by lia.
    rewrite (drop_S l y (i + n)) //.
    rewrite -assoc Nat.add_succ_r //.
  Qed.

  Lemma with_sliceｰlookupｰleft {i n l s} k x :
    l !! k = Some x →
    k < i →
    with_slice i n l s !! k = Some x.
  Proof.
    intros Hlookup Hk.
    apply lookup_lt_Some in Hlookup as ?.
    rewrite lookup_app_l.
    { rewrite length_take. lia. }
    rewrite lookup_take_Some //.
  Qed.
  Lemma with_sliceｰlookupｰmiddle {i n l s} k x :
    s !! (k - i) = Some x →
    i ≤ length l →
    i ≤ k →
    with_slice i n l s !! k = Some x.
  Proof.
    intros Hlookup Hi Hk.
    apply lookup_lt_Some in Hlookup as ?.
    rewrite lookup_app_r length_take; first lia.
    rewrite Nat.min_l; first lia.
    rewrite lookup_app_l //.
  Qed.
  Lemma with_sliceｰlookupｰmiddle' {i n l s} k1 k2 x :
    s !! k2 = Some x →
    k2 = k1 - i →
    i ≤ length l →
    i ≤ k1 →
    with_slice i n l s !! k1 = Some x.
  Proof.
    intros Hlookup ->.
    apply with_sliceｰlookupｰmiddle. done.
  Qed.
  Lemma with_sliceｰlookupｰright {i n l s} k x :
    l !! k = Some x →
    length s = n →
    i + n ≤ k →
    with_slice i n l s !! k = Some x.
  Proof.
    intros Hlookup Hs Hk.
    apply lookup_lt_Some in Hlookup as ?.
    rewrite lookup_app_r length_take; first lia.
    rewrite lookup_app_r; first lia.
    rewrite lookup_drop -Hlookup. f_equal. lia.
  Qed.
End with_slice.

#[global] Hint Rewrite
  @lengthｰwith_slice
: simp_length.

Section rotation.
  Context {A : Type}.

  Implicit Type x : A.
  Implicit Type l : list A.

  Definition rotation n l :=
    drop n l ++ take n l.

  Lemma rotationｰ0 l :
    rotation 0 l = l.
  Proof.
    rewrite /rotation right_id //.
  Qed.
  Lemma rotationｰS n x l :
    n ≤ length l →
    rotation ˖n (x :: l) = rotation n (l ++ [x]).
  Proof.
    intros Hn.
    rewrite /rotation.
    rewrite skipn_cons firstn_cons.
    rewrite drop_app_le // take_app_le // -assoc //.
  Qed.
  Lemma rotationｰadd n1 n2 l :
    n1 + n2 = length l →
    rotation n1 (rotation n2 l) = rotation (n1 + n2) l.
  Proof.
    intros ?.
    rewrite /rotation.
    rewrite drop_app drop_drop length_drop.
    rewrite take_app length_drop.
    replace (n1 - (length l - n2)) with 0 by lia.
    rewrite drop_0 app_nil_r -assoc take_take_drop Nat.add_comm //.
  Qed.
  Lemma rotationｰlength n l :
    n = length l →
    rotation n l = l.
  Proof.
    intros ->.
    rewrite /rotation drop_all firstn_all //.
  Qed.

  Lemma rotationｰPermutation n l :
    rotation n l ≡ₚ l.
  Proof.
    rewrite /rotation comm take_drop //.
  Qed.

  Lemma lengthｰrotation n l :
    length (rotation n l) = length l.
  Proof.
    apply Permutation_length, rotationｰPermutation.
  Qed.

  Lemma rotationｰreplicate n k x :
    rotation n (replicate k x) = replicate k x.
  Proof.
    pose proof (rotationｰPermutation n (replicate k x)) as <-%symmetry%replicate_Permutation. done.
  Qed.
End rotation.

#[global] Hint Rewrite
  @lengthｰrotation
: simp_length.

Section omap.
  Context {A : Type}.
  Context {B : Type}.

  Implicit Type x y : A.
  Implicit Type 𝑥 𝑦 : B.
  Implicit Type o : option B.
  Implicit Type l : list A.
  Implicit Type 𝑙 : list B.
  Implicit Type f : A → option B.

  Lemma lengthｰomap f l :
    length (omap f l) ≤ length l.
  Proof.
    induction l as [| x l IH] => //=.
    destruct (f x) => /=.
    - rewrite -Nat.succ_le_mono //.
    - apply Nat.le_le_succ_r. done.
  Qed.

  Lemma listｰomapｰinsertｰNone {f l} i x1 x2 o :
    l !! i = Some x1 →
    f x1 = None →
    f x2 = o →
    omap f (<[i := x2]> l) ≡ₚ
      match o with
      | None =>
          id
      | Some 𝑥 =>
          cons 𝑥
      end $
      omap f l.
  Proof.
    intros Hlookup Hx1 Hx2.
    apply lookup_lt_Some in Hlookup as Hi.
    rewrite insert_take_drop //.
    rewrite -{3}(take_drop_middle l i x1) //.
    rewrite omap_app /= Hx2.
    rewrite omap_app /= Hx1.
    destruct o; solve_Permutation.
  Qed.
  Lemma listｰomapｰinsertｰNoneｰSome {f l} i x1 x2 𝑥 :
    l !! i = Some x1 →
    f x1 = None →
    f x2 = Some 𝑥 →
    omap f (<[i := x2]> l) ≡ₚ 𝑥 :: omap f l.
  Proof.
    apply: listｰomapｰinsertｰNone.
  Qed.
  Lemma listｰomapｰinsertｰNoneｰNone {f l} i x1 x2 :
    l !! i = Some x1 →
    f x1 = None →
    f x2 = None →
    omap f (<[i := x2]> l) ≡ₚ omap f l.
  Proof.
    apply: listｰomapｰinsertｰNone.
  Qed.

  Lemma listｰomapｰinsertｰSomeｰNone {f l} i x1 𝑥 x2 :
    l !! i = Some x1 →
    f x1 = Some 𝑥 →
    f x2 = None →
    omap f (<[i := x2]> l) = delete (length $ omap f $ take i l) (omap f l).
  Proof.
    intros Hlookup Hx1 Hx2.
    apply lookup_lt_Some in Hlookup as Hi.
    rewrite insert_take_drop //.
    rewrite -{4}(take_drop_middle l i x1) //.
    rewrite omap_app /= Hx2.
    rewrite omap_app /= Hx1.
    rewrite delete_middle //.
  Qed.
End omap.

#[global] Hint Rewrite
  @lengthｰomap
: simp_length.

Section oflatten.
  Context {A : Type}.

  Implicit Type x y : A.
  Implicit Type o : option A.
  Implicit Type l : list (option A).

  Definition oflatten l :=
    omap id l.

  Lemma lengthｰoflatten l :
    length (oflatten l) ≤ length l.
  Proof.
    apply lengthｰomap.
  Qed.

  Lemma oflattenｰcons o l :
    oflatten (o :: l) = from_option (λ x, [x]) [] o ++ oflatten l.
  Proof.
    destruct o; done.
  Qed.
  Lemma oflattenｰconsｰNone l :
    oflatten (None :: l) = oflatten l.
  Proof.
    rewrite oflattenｰcons //.
  Qed.
  Lemma oflattenｰconsｰSome x l :
    oflatten (Some x :: l) = x :: oflatten l.
  Proof.
    rewrite oflattenｰcons //.
  Qed.

  Lemma oflattenｰapp l1 l2 :
    oflatten (l1 ++ l2) = oflatten l1 ++ oflatten l2.
  Proof.
    apply omap_app.
  Qed.

  Lemma oflattenｰsnoc l o :
    oflatten (l ++ [o]) = oflatten l ++ from_option (λ x, [x]) [] o.
  Proof.
    rewrite oflattenｰapp //.
  Qed.
  Lemma oflattenｰsnocｰNone l :
    oflatten (l ++ [None]) = oflatten l.
  Proof.
    rewrite oflattenｰsnoc /= right_id //.
  Qed.
  Lemma oflattenｰsnocｰSome l x :
    oflatten (l ++ [Some x]) = oflatten l ++ [x].
  Proof.
    rewrite oflattenｰsnoc //.
  Qed.

  Lemma elem_ofｰoflatten l x :
    x ∈ oflatten l ↔
    Some x ∈ l.
  Proof.
    rewrite list_elem_of_omap. naive_solver.
  Qed.

  Lemma oflattenｰlookupｰSome l i x :
    l !! i = Some $ Some x →
    oflatten l !! (length $ oflatten $ take i l) = Some x.
  Proof.
    intros Hlookup.
    rewrite -{2}(take_drop_middle l i (Some x)) //.
    rewrite oflattenｰapp list_lookup_middle //.
  Qed.

  Lemma oflattenｰinsertｰNone {l} i o :
    l !! i = Some None →
    oflatten (<[i := o]> l) ≡ₚ
      match o with
      | None =>
          id
      | Some x =>
          cons x
      end $
      oflatten l.
  Proof.
    intros Hlookup.
    apply: listｰomapｰinsertｰNone; done.
  Qed.
  Lemma oflattenｰinsertｰNoneｰSome {l} i x :
    l !! i = Some None →
    oflatten (<[i := Some x]> l) ≡ₚ x :: oflatten l.
  Proof.
    intros Hlookup.
    apply: oflattenｰinsertｰNone. done.
  Qed.
  Lemma oflattenｰinsertｰNoneｰNone {l} i x :
    l !! i = Some None →
    oflatten (<[i := None]> l) ≡ₚ oflatten l.
  Proof.
    intros Hlookup.
    apply: oflattenｰinsertｰNone. done.
  Qed.

  Lemma oflattenｰinsertｰSomeｰNone {l} i x :
    l !! i = Some $ Some x →
    oflatten (<[i := None]> l) = delete (length $ oflatten $ take i l) (oflatten l).
  Proof.
    intros Hlookup.
    apply: listｰomapｰinsertｰSomeｰNone; done.
  Qed.
End oflatten.

#[global] Hint Rewrite
  @lengthｰoflatten
: simp_length.

Section Sorted.
  Context `(R : A → A → Prop).

  Implicit Type x : A.
  Implicit Type l : list A.

  Lemma StronglySortedｰnil :
    StronglySorted R [].
  Proof.
    apply SSorted_nil.
  Qed.
  Lemma StronglySortedｰsingleton x :
    StronglySorted R [x].
  Proof.
    apply StronglySorted_cons.
    split. 1: done.
    apply StronglySortedｰnil.
  Qed.
  Lemma StronglySortedｰtrivial l :
    length l ≤ 1 →
    StronglySorted R l.
  Proof.
    destruct l as [| x0 [| x1 l]] => /= Hl.
    - apply StronglySortedｰnil.
    - apply StronglySortedｰsingleton.
    - lia.
  Qed.

  Lemma StronglySortedｰappｰcons `{!Transitive R} l1 x l2 :
    StronglySorted R l1 →
    Forall (flip R x) l1 →
    Forall (R x) l2 →
    StronglySorted R l2 →
    StronglySorted R (l1 ++ x :: l2).
  Proof.
    intros Hl1 H1 H2 Hl2.
    rewrite StronglySorted_app StronglySorted_cons.
    split_and!. 2-4: done.
    intros x1 x2 Hx1 Hx2.
    eapply Forallｰelem_of in H1. 2: done.
    apply elem_of_cons in Hx2 as [-> | Hx2] => //.
    trans x. 1: done.
    eapply Forallｰelem_of; done.
  Qed.
End Sorted.
