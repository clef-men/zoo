Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.hashtbl__code.
Require Import zoo_std.hashtbl__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type l : location.
Implicit Type v t key hash equal pred bucket buckets : val.
Implicit Type bucket_vals : list val.

(* ------------------------------------------------------------------------ *)
(* Entries. *)

(* An entry is a binding of the table: a key, a value and the abstract
   key represented by the key. *)
Record entry Key := Entry
  { entry۰key : val
  ; entry۰value : val
  ; entry۰𝑘𝑒𝑦 : Key
  }.
#[local] Arguments Entry {_} _ _ _.
#[local] Arguments entry۰key {_} _.
#[local] Arguments entry۰value {_} _.
#[local] Arguments entry۰𝑘𝑒𝑦 {_} _.

#[local] Abbreviation entries۰𝑘𝑒𝑦𝑠 entries :=
  (entry۰𝑘𝑒𝑦 <$> entries).

Section entries.
  Context {Key : Type} `{!EqDecision Key}.

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type entry : entry Key.
  Implicit Type entries : list (entry Key).

  (* The value of the first binding of [𝑘𝑒𝑦], as found by
     [hashtbl٠bucket٠assoc]. *)
  #[local] Fixpoint entries۰lookup 𝑘𝑒𝑦 entries : option val :=
    match entries with
    | [] =>
        None
    | Entry _ v 𝑘𝑒𝑦' :: entries =>
        if decide (𝑘𝑒𝑦 = 𝑘𝑒𝑦') then Some v else entries۰lookup 𝑘𝑒𝑦 entries
    end.

  (* Removes the first binding of [𝑘𝑒𝑦], as [hashtbl٠bucket٠remove]. *)
  #[local] Fixpoint entries۰remove 𝑘𝑒𝑦 entries :=
    match entries with
    | [] =>
        []
    | entry :: entries =>
        if decide (𝑘𝑒𝑦 = entry.(entry۰𝑘𝑒𝑦)) then
          entries
        else
          entry :: entries۰remove 𝑘𝑒𝑦 entries
    end.

  (* Replaces the value of the first binding of [𝑘𝑒𝑦], as
     [hashtbl٠bucket٠replace]. *)
  #[local] Fixpoint entries۰replace 𝑘𝑒𝑦 v entries :=
    match entries with
    | [] =>
        []
    | entry :: entries =>
        if decide (𝑘𝑒𝑦 = entry.(entry۰𝑘𝑒𝑦)) then
          Entry entry.(entry۰key) v entry.(entry۰𝑘𝑒𝑦) :: entries
        else
          entry :: entries۰replace 𝑘𝑒𝑦 v entries
    end.

  (* Keeps the entries whose abstract key satisfies [P], as
     [hashtbl٠bucket٠filter]. *)
  #[local] Definition entries۰filter (P : Key → Prop) `{!∀ 𝑘𝑒𝑦, Decision (P 𝑘𝑒𝑦)} entries :=
    filter (λ entry, P entry.(entry۰𝑘𝑒𝑦)) entries.

  #[local] Lemma entries۰lookupｰNone 𝑘𝑒𝑦 entries :
    entries۰lookup 𝑘𝑒𝑦 entries = None ↔
    𝑘𝑒𝑦 ∉ entries۰𝑘𝑒𝑦𝑠 entries.
  Proof.
    induction entries as [| [key v 𝑘𝑒𝑦'] entries IH]; first set_solver.
    rewrite /= elem_of_cons. case_decide; naive.
  Qed.
  #[local] Lemma entries۰lookupｰfilter 𝑘𝑒𝑦 (P : Key → Prop) `{!∀ 𝑘𝑒𝑦, Decision (P 𝑘𝑒𝑦)} entries :
    entries۰lookup 𝑘𝑒𝑦 (entries۰filter P entries) =
      if decide (P 𝑘𝑒𝑦) then entries۰lookup 𝑘𝑒𝑦 entries else None.
  Proof.
    rewrite /entries۰filter.
    induction entries as [| [key v 𝑘𝑒𝑦'] entries IH]; first by case_decide.
    rewrite filter_cons. cbn [entry۰𝑘𝑒𝑦].
    destruct (decide (P 𝑘𝑒𝑦')) as [HP' | HP'].
    - cbn [entries۰lookup]. rewrite IH.
      destruct (decide (𝑘𝑒𝑦 = 𝑘𝑒𝑦')) as [-> | H𝑘𝑒𝑦]; last done.
      rewrite decide_True //.
    - cbn [entries۰lookup]. rewrite IH.
      destruct (decide (P 𝑘𝑒𝑦)) as [HP | HP]; last done.
      rewrite decide_False //. intros ->. done.
  Qed.
  #[local] Lemma entries۰lookupｰremove 𝑘𝑒𝑦 𝑘𝑒𝑦' entries :
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries) →
    entries۰lookup 𝑘𝑒𝑦' (entries۰remove 𝑘𝑒𝑦 entries) =
      if decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦) then None else entries۰lookup 𝑘𝑒𝑦' entries.
  Proof.
    induction entries as [| [key v 𝑘𝑒𝑦''] entries IH]; first by case_decide.
    rewrite fmap_cons NoDup_cons /=. intros (Hnotin & Hnodup).
    destruct (decide (𝑘𝑒𝑦 = 𝑘𝑒𝑦'')) as [<- | H𝑘𝑒𝑦].
    - destruct (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦)) as [-> | H𝑘𝑒𝑦']; last done.
      apply entries۰lookupｰNone. done.
    - rewrite /= IH //.
      destruct (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦'')), (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦)); congruence.
  Qed.
  #[local] Lemma entries۰lookupｰreplace 𝑘𝑒𝑦 𝑘𝑒𝑦' v entries :
    entries۰lookup 𝑘𝑒𝑦' (entries۰replace 𝑘𝑒𝑦 v entries) =
      if decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦) then (λ _, v) <$> entries۰lookup 𝑘𝑒𝑦 entries else entries۰lookup 𝑘𝑒𝑦' entries.
  Proof.
    induction entries as [| [key v' 𝑘𝑒𝑦''] entries IH]; first by case_decide.
    rewrite /=.
    destruct (decide (𝑘𝑒𝑦 = 𝑘𝑒𝑦'')) as [<- | H𝑘𝑒𝑦].
    - rewrite /=.
      destruct (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦)); done.
    - rewrite /= IH.
      destruct (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦'')), (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦)); congruence.
  Qed.

  #[local] Lemma entries۰𝑘𝑒𝑦𝑠ｰremove 𝑘𝑒𝑦 𝑘𝑒𝑦' entries :
    𝑘𝑒𝑦' ∈ entries۰𝑘𝑒𝑦𝑠 (entries۰remove 𝑘𝑒𝑦 entries) →
    𝑘𝑒𝑦' ∈ entries۰𝑘𝑒𝑦𝑠 entries.
  Proof.
    induction entries as [| entry entries IH]; first done.
    rewrite /=. case_decide; set_solver.
  Qed.
  #[local] Lemma entries۰𝑘𝑒𝑦𝑠ｰremoveｰNoDup 𝑘𝑒𝑦 entries :
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries) →
    NoDup (entries۰𝑘𝑒𝑦𝑠 (entries۰remove 𝑘𝑒𝑦 entries)).
  Proof.
    induction entries as [| entry entries IH]; first done.
    rewrite fmap_cons NoDup_cons /=. intros (Hnotin & Hnodup).
    case_decide; first done.
    rewrite fmap_cons NoDup_cons. split; last auto.
    intros ?%entries۰𝑘𝑒𝑦𝑠ｰremove. done.
  Qed.
  #[local] Lemma entries۰𝑘𝑒𝑦𝑠ｰreplace 𝑘𝑒𝑦 v entries :
    entries۰𝑘𝑒𝑦𝑠 (entries۰replace 𝑘𝑒𝑦 v entries) = entries۰𝑘𝑒𝑦𝑠 entries.
  Proof.
    induction entries as [| entry entries IH]; first done.
    cbn [entries۰replace].
    destruct (decide _); rewrite !fmap_cons ?IH //.
  Qed.
  #[local] Lemma entries۰𝑘𝑒𝑦𝑠ｰfilter (P : Key → Prop) `{!∀ 𝑘𝑒𝑦, Decision (P 𝑘𝑒𝑦)} 𝑘𝑒𝑦 entries :
    𝑘𝑒𝑦 ∈ entries۰𝑘𝑒𝑦𝑠 (entries۰filter P entries) →
      P 𝑘𝑒𝑦 ∧
      𝑘𝑒𝑦 ∈ entries۰𝑘𝑒𝑦𝑠 entries.
  Proof.
    rewrite /entries۰filter.
    induction entries as [| entry entries IH]; first set_solver.
    rewrite filter_cons fmap_cons elem_of_cons.
    destruct (decide _) as [HP | HP].
    - rewrite fmap_cons elem_of_cons. intros [-> | (? & ?)%IH]; naive.
    - intros (? & ?)%IH. naive.
  Qed.
  #[local] Lemma entries۰𝑘𝑒𝑦𝑠ｰfilterｰNoDup (P : Key → Prop) `{!∀ 𝑘𝑒𝑦, Decision (P 𝑘𝑒𝑦)} entries :
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries) →
    NoDup (entries۰𝑘𝑒𝑦𝑠 (entries۰filter P entries)).
  Proof.
    induction entries as [| entry entries IH]; first done.
    rewrite fmap_cons NoDup_cons. intros (Hnotin & Hnodup).
    rewrite {1}/entries۰filter filter_cons.
    case_decide; last auto.
    rewrite fmap_cons NoDup_cons. split; last auto.
    intros (_ & ?)%entries۰𝑘𝑒𝑦𝑠ｰfilter. done.
  Qed.

  #[local] Lemma entries۰replaceｰNone 𝑘𝑒𝑦 v entries :
    entries۰lookup 𝑘𝑒𝑦 entries = None →
    entries۰replace 𝑘𝑒𝑦 v entries = entries.
  Proof.
    induction entries as [| [key v' 𝑘𝑒𝑦'] entries IH]; first done.
    rewrite /=. case_decide; first done.
    intros ?. rewrite IH //.
  Qed.
End entries.

(* ------------------------------------------------------------------------ *)
(* Indices. *)

(* The index of the bucket of [𝑘𝑒𝑦] when there are [cap] buckets. *)
#[local] Definition index {Key} (𝘩𝑎𝑠𝘩 : Key → Z) (cap : nat) 𝑘𝑒𝑦 : nat :=
  ₊(𝘩𝑎𝑠𝘩 𝑘𝑒𝑦 `mod` ⁺cap).

#[local] Lemma indexｰlt {Key} (𝘩𝑎𝑠𝘩 : Key → Z) cap 𝑘𝑒𝑦 :
  0 < cap →
  index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 < cap.
Proof.
  intros Hcap.
  pose proof (Z.mod_pos_bound (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap ltac:(lia)).
  rewrite /index. lia.
Qed.
#[local] Lemma indexｰZ {Key} (𝘩𝑎𝑠𝘩 : Key → Z) cap 𝑘𝑒𝑦 :
  0 < cap →
  ⁺(index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦) = (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦 `mod` ⁺cap)%Z.
Proof.
  intros Hcap.
  pose proof (Z.mod_pos_bound (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap ltac:(lia)).
  rewrite /index. lia.
Qed.
#[local] Lemma indexｰdouble {Key} (𝘩𝑎𝑠𝘩 : Key → Z) cap 𝑘𝑒𝑦 :
  is_pow2 cap →
    (Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = 0)%Z ∧
    index 𝘩𝑎𝑠𝘩 (2 * cap) 𝑘𝑒𝑦 = index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦
  ∨ (Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = ⁺cap)%Z ∧
    index 𝘩𝑎𝑠𝘩 (2 * cap) 𝑘𝑒𝑦 = index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 + cap.
Proof.
  intros Hcap.
  pose proof (is_pow2ｰpos _ Hcap).
  pose proof (Z.mod_pos_bound (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap ltac:(lia)).
  rewrite /index Zｰlandｰpow2 // Zｰmodｰpow2ｰdouble //.
  destruct (Z.testbit _ _); [right | left]; simpl; lia.
Qed.

(* ------------------------------------------------------------------------ *)
(* Pure invariant. *)

Section inv۰pure.
  Context {Key : Type} `{Countable Key}.

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type 𝘩𝑎𝑠𝘩 : Key → Z.
  Implicit Type m : gmap Key val.
  Implicit Type entry : entry Key.
  Implicit Type entries : list (entry Key).
  Implicit Type contents : list (list (entry Key)).

  (* [contents] lists the entries of each bucket:
     - there are [cap] buckets, a power of 2;
     - every entry lives in the bucket given by its hash;
     - the abstract keys of a bucket are pairwise distinct;
     - [m] is the map represented by the buckets. *)
  Record inv۰pure 𝘩𝑎𝑠𝘩 cap contents m :=
    { inv۰pure۰cap :
        is_pow2 cap
    ; inv۰pure۰length :
        length contents = cap
    ; inv۰pure۰index i entries 𝑘𝑒𝑦 :
        contents !! i = Some entries →
        𝑘𝑒𝑦 ∈ entries۰𝑘𝑒𝑦𝑠 entries →
        index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = i
    ; inv۰pure۰nodup i entries :
        contents !! i = Some entries →
        NoDup (entries۰𝑘𝑒𝑦𝑠 entries)
    ; inv۰pure۰model 𝑘𝑒𝑦 :
        m !! 𝑘𝑒𝑦 = entries۰lookup 𝑘𝑒𝑦 (contents !!! index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦)
    }.
  #[local] Arguments inv۰pure۰cap {_ _ _ _} _.
  #[local] Arguments inv۰pure۰length {_ _ _ _} _.
  #[local] Arguments inv۰pure۰index {_ _ _ _} _ _ _ _.
  #[local] Arguments inv۰pure۰nodup {_ _ _ _} _ _ _.
  #[local] Arguments inv۰pure۰model {_ _ _ _} _ _.

  #[local] Lemma inv۰pureｰempty 𝘩𝑎𝑠𝘩 cap :
    is_pow2 cap →
    inv۰pure 𝘩𝑎𝑠𝘩 cap (replicate cap []) ∅.
  Proof.
    intros Hcap.
    pose proof (is_pow2ｰpos _ Hcap).
    split.
    - done.
    - rewrite length_replicate //.
    - intros i entries 𝑘𝑒𝑦 (-> & _)%lookup_replicate. set_solver.
    - intros i entries (-> & _)%lookup_replicate. constructor.
    - intros 𝑘𝑒𝑦.
      rewrite lookup_empty lookup_total_replicate_2 //.
      apply indexｰlt. lia.
  Qed.

  #[local] Lemma inv۰pureｰlookup {𝘩𝑎𝑠𝘩 cap contents m} 𝑘𝑒𝑦 :
    inv۰pure 𝘩𝑎𝑠𝘩 cap contents m →
      ∃ entries,
      contents !! index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = Some entries ∧
      m !! 𝑘𝑒𝑦 = entries۰lookup 𝑘𝑒𝑦 entries.
  Proof.
    intros Hinv.
    pose proof (is_pow2ｰpos _ (inv۰pure۰cap Hinv)).
    destruct (lookup_lt_is_Some_2 contents (index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦)) as (entries & Hlookup).
    { rewrite (inv۰pure۰length Hinv). apply indexｰlt. lia. }
    exists entries. split; first done.
    rewrite (inv۰pure۰model Hinv) (list_lookup_total_correct _ _ _ Hlookup) //.
  Qed.

  #[local] Lemma inv۰pureｰupdate {𝘩𝑎𝑠𝘩 cap contents m} i entries entries' m' :
    inv۰pure 𝘩𝑎𝑠𝘩 cap contents m →
    contents !! i = Some entries →
    ( ∀ 𝑘𝑒𝑦,
      𝑘𝑒𝑦 ∈ entries۰𝑘𝑒𝑦𝑠 entries' →
      index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = i
    ) →
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries') →
    ( ∀ 𝑘𝑒𝑦,
      index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = i →
      m' !! 𝑘𝑒𝑦 = entries۰lookup 𝑘𝑒𝑦 entries'
    ) →
    ( ∀ 𝑘𝑒𝑦,
      index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ≠ i →
      m' !! 𝑘𝑒𝑦 = m !! 𝑘𝑒𝑦
    ) →
    inv۰pure 𝘩𝑎𝑠𝘩 cap (<[i := entries']> contents) m'.
  Proof.
    intros Hinv Hlookup Hindex Hnodup Hmodel1 Hmodel2.
    pose proof (lookup_lt_Some _ _ _ Hlookup).
    split.
    - apply Hinv.
    - rewrite length_insert. apply Hinv.
    - intros j entries'' 𝑘𝑒𝑦.
      rewrite list_lookup_insert_Some. intros [(<- & <- & _) | (_ & Hlookup')].
      + apply Hindex.
      + apply (inv۰pure۰index Hinv _ _ _ Hlookup').
    - intros j entries''.
      rewrite list_lookup_insert_Some. intros [(<- & <- & _) | (_ & Hlookup')].
      + done.
      + apply (inv۰pure۰nodup Hinv _ _ Hlookup').
    - intros 𝑘𝑒𝑦.
      destruct (decide (index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = i)) as [Hindex' | Hindex'].
      + rewrite Hindex' list_lookup_total_insert_eq //. auto.
      + rewrite list_lookup_total_insert_ne; first done.
        rewrite Hmodel2 //. apply Hinv.
  Qed.

  #[local] Lemma inv۰pureｰadd {𝘩𝑎𝑠𝘩 cap contents m} 𝑘𝑒𝑦 entries key v :
    inv۰pure 𝘩𝑎𝑠𝘩 cap contents m →
    contents !! index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = Some entries →
    entries۰lookup 𝑘𝑒𝑦 entries = None →
    inv۰pure 𝘩𝑎𝑠𝘩 cap
      (<[index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 := Entry key v 𝑘𝑒𝑦 :: entries]> contents)
      (<[𝑘𝑒𝑦 := v]> m).
  Proof.
    intros Hinv Hlookup Hentries.
    apply (inv۰pureｰupdate _ entries _ _ Hinv Hlookup).
    - intros 𝑘𝑒𝑦'.
      rewrite fmap_cons elem_of_cons. intros [-> | H𝑘𝑒𝑦']; first done.
      apply (inv۰pure۰index Hinv _ _ _ Hlookup H𝑘𝑒𝑦').
    - rewrite fmap_cons NoDup_cons. split.
      + apply entries۰lookupｰNone. done.
      + apply (inv۰pure۰nodup Hinv _ _ Hlookup).
    - intros 𝑘𝑒𝑦' Hindex.
      rewrite /=. case_decide as H𝑘𝑒𝑦.
      + subst. rewrite lookup_insert_eq //.
      + rewrite lookup_insert_ne; first done.
        rewrite (inv۰pure۰model Hinv) Hindex (list_lookup_total_correct _ _ _ Hlookup) //.
    - intros 𝑘𝑒𝑦' Hindex.
      rewrite lookup_insert_ne //. congruence.
  Qed.

  #[local] Lemma inv۰pureｰremove {𝘩𝑎𝑠𝘩 cap contents m} 𝑘𝑒𝑦 entries :
    inv۰pure 𝘩𝑎𝑠𝘩 cap contents m →
    contents !! index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = Some entries →
    inv۰pure 𝘩𝑎𝑠𝘩 cap
      (<[index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 := entries۰remove 𝑘𝑒𝑦 entries]> contents)
      (delete 𝑘𝑒𝑦 m).
  Proof.
    intros Hinv Hlookup.
    pose proof (inv۰pure۰nodup Hinv _ _ Hlookup) as Hnodup.
    apply (inv۰pureｰupdate _ entries _ _ Hinv Hlookup).
    - intros 𝑘𝑒𝑦' ?%entries۰𝑘𝑒𝑦𝑠ｰremove.
      apply (inv۰pure۰index Hinv _ _ _ Hlookup). done.
    - apply entries۰𝑘𝑒𝑦𝑠ｰremoveｰNoDup. done.
    - intros 𝑘𝑒𝑦' Hindex.
      rewrite entries۰lookupｰremove //. case_decide as H𝑘𝑒𝑦.
      + subst. rewrite lookup_delete_eq //.
      + rewrite lookup_delete_ne; first done.
        rewrite (inv۰pure۰model Hinv) Hindex (list_lookup_total_correct _ _ _ Hlookup) //.
    - intros 𝑘𝑒𝑦' Hindex.
      rewrite lookup_delete_ne //. congruence.
  Qed.

  #[local] Lemma inv۰pureｰreplace {𝘩𝑎𝑠𝘩 cap contents m} 𝑘𝑒𝑦 entries v :
    inv۰pure 𝘩𝑎𝑠𝘩 cap contents m →
    contents !! index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 = Some entries →
    is_Some (entries۰lookup 𝑘𝑒𝑦 entries) →
    inv۰pure 𝘩𝑎𝑠𝘩 cap
      (<[index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 := entries۰replace 𝑘𝑒𝑦 v entries]> contents)
      (<[𝑘𝑒𝑦 := v]> m).
  Proof.
    intros Hinv Hlookup (v' & Hentries).
    apply (inv۰pureｰupdate _ entries _ _ Hinv Hlookup).
    - intros 𝑘𝑒𝑦'.
      rewrite entries۰𝑘𝑒𝑦𝑠ｰreplace.
      apply (inv۰pure۰index Hinv _ _ _ Hlookup).
    - rewrite entries۰𝑘𝑒𝑦𝑠ｰreplace.
      apply (inv۰pure۰nodup Hinv _ _ Hlookup).
    - intros 𝑘𝑒𝑦' Hindex.
      rewrite entries۰lookupｰreplace. case_decide as H𝑘𝑒𝑦.
      + subst. rewrite lookup_insert_eq Hentries //.
      + rewrite lookup_insert_ne; first done.
        rewrite (inv۰pure۰model Hinv) Hindex (list_lookup_total_correct _ _ _ Hlookup) //.
    - intros 𝑘𝑒𝑦' Hindex.
      rewrite lookup_insert_ne //. congruence.
  Qed.

  (* The buckets after resizing: bucket [i] is split into buckets [i] and
     [i + cap] according to the bit of the hash selected by [cap]. *)
  #[local] Definition contents۰split 𝘩𝑎𝑠𝘩 (cap : nat) contents :=
    (entries۰filter (λ 𝑘𝑒𝑦, Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = 0)%Z <$> contents) ++
    (entries۰filter (λ 𝑘𝑒𝑦, Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = ⁺cap)%Z <$> contents).

  #[local] Lemma inv۰pureｰsplit {𝘩𝑎𝑠𝘩 cap contents m} :
    inv۰pure 𝘩𝑎𝑠𝘩 cap contents m →
    inv۰pure 𝘩𝑎𝑠𝘩 (2 * cap) (contents۰split 𝘩𝑎𝑠𝘩 cap contents) m.
  Proof.
    intros Hinv.
    pose proof (inv۰pure۰cap Hinv) as Hcap.
    pose proof (is_pow2ｰpos _ Hcap).
    pose proof (inv۰pure۰length Hinv) as Hlength.
    split.
    - apply is_pow2ｰdouble. done.
    - rewrite /contents۰split length_app !length_fmap. lia.
    - intros j entries' 𝑘𝑒𝑦.
      rewrite /contents۰split lookup_app_Some length_fmap.
      intros [Hlookup | (Hj & Hlookup)].
      + apply list_lookup_fmap_Some in Hlookup as (entries & -> & Hlookup).
        intros (Hbit & H𝑘𝑒𝑦)%entries۰𝑘𝑒𝑦𝑠ｰfilter.
        pose proof (inv۰pure۰index Hinv _ _ _ Hlookup H𝑘𝑒𝑦).
        destruct (indexｰdouble 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 Hcap) as [(_ & ->) | (? & _)]; lia.
      + apply list_lookup_fmap_Some in Hlookup as (entries & -> & Hlookup).
        intros (Hbit & H𝑘𝑒𝑦)%entries۰𝑘𝑒𝑦𝑠ｰfilter.
        pose proof (inv۰pure۰index Hinv _ _ _ Hlookup H𝑘𝑒𝑦).
        destruct (indexｰdouble 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 Hcap) as [(? & _) | (_ & ->)]; lia.
    - intros j entries'.
      rewrite /contents۰split lookup_app_Some length_fmap.
      intros [Hlookup | (_ & Hlookup)].
      + apply list_lookup_fmap_Some in Hlookup as (entries & -> & Hlookup).
        apply entries۰𝑘𝑒𝑦𝑠ｰfilterｰNoDup.
        apply (inv۰pure۰nodup Hinv _ _ Hlookup).
      + apply list_lookup_fmap_Some in Hlookup as (entries & -> & Hlookup).
        apply entries۰𝑘𝑒𝑦𝑠ｰfilterｰNoDup.
        apply (inv۰pure۰nodup Hinv _ _ Hlookup).
    - intros 𝑘𝑒𝑦.
      pose proof (indexｰlt 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ltac:(lia)).
      rewrite (inv۰pure۰model Hinv) /contents۰split.
      destruct (indexｰdouble 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 Hcap) as [(Hbit & ->) | (Hbit & ->)].
      + rewrite lookup_total_app_l; first (rewrite length_fmap; lia).
        rewrite list_lookup_total_fmap; first lia.
        rewrite entries۰lookupｰfilter decide_True //.
      + rewrite lookup_total_app_r; first (rewrite length_fmap; lia).
        rewrite length_fmap Hlength Nat.add_sub.
        rewrite list_lookup_total_fmap; first lia.
        rewrite entries۰lookupｰfilter decide_True //.
  Qed.

  (* The buckets during resizing, after the first [i] buckets were split. *)
  #[local] Definition contents۰resize 𝘩𝑎𝑠𝘩 (cap : nat) contents (i : nat) :=
    ( λ j,
      if decide (j < i ∨ cap ≤ j < cap + i) then
        contents۰split 𝘩𝑎𝑠𝘩 cap contents !!! j
      else
        []
    ) <$> seq 0 (2 * cap).

  #[local] Lemma contents۰resizeｰlength 𝘩𝑎𝑠𝘩 cap contents i :
    length (contents۰resize 𝘩𝑎𝑠𝘩 cap contents i) = 2 * cap.
  Proof.
    rewrite length_fmap length_seq //.
  Qed.
  #[local] Lemma contents۰resizeｰ0 𝘩𝑎𝑠𝘩 cap contents :
    contents۰resize 𝘩𝑎𝑠𝘩 cap contents 0 = replicate (2 * cap) [].
  Proof.
    apply (list_eq_same_length _ _ (2 * cap)).
    - rewrite length_replicate //.
    - apply contents۰resizeｰlength.
    - intros j entries1 entries2 Hj.
      rewrite list_lookup_fmap lookup_seq_lt // lookup_replicate_2 //=.
      intros [= <-] [= <-].
      rewrite decide_False //. lia.
  Qed.
  #[local] Lemma contents۰resizeｰstep 𝘩𝑎𝑠𝘩 cap contents i entries :
    length contents = cap →
    contents !! i = Some entries →
    <[i + cap := entries۰filter (λ 𝑘𝑒𝑦, Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = ⁺cap)%Z entries]> (
      <[i := entries۰filter (λ 𝑘𝑒𝑦, Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = 0)%Z entries]> (
        contents۰resize 𝘩𝑎𝑠𝘩 cap contents i
      )
    ) =
    contents۰resize 𝘩𝑎𝑠𝘩 cap contents ˖i.
  Proof.
    intros Hlength Hlookup.
    pose proof (lookup_lt_Some _ _ _ Hlookup).
    apply list_eq => j.
    destruct (decide (j = i + cap)) as [-> | Hj1]; last destruct (decide (j = i)) as [-> | Hj2].
    - rewrite list_lookup_insert_eq.
      { rewrite length_insert contents۰resizeｰlength. lia. }
      rewrite list_lookup_fmap lookup_seq_lt /=; first lia.
      rewrite decide_True; first lia.
      rewrite /contents۰split lookup_total_app_r; first (rewrite length_fmap; lia).
      rewrite length_fmap Hlength Nat.add_sub list_lookup_total_fmap; first lia.
      rewrite (list_lookup_total_correct _ _ _ Hlookup) //.
    - rewrite list_lookup_insert_ne; first lia.
      rewrite list_lookup_insert_eq.
      { rewrite contents۰resizeｰlength. lia. }
      rewrite list_lookup_fmap lookup_seq_lt /=; first lia.
      rewrite decide_True; first lia.
      rewrite /contents۰split lookup_total_app_l; first (rewrite length_fmap; lia).
      rewrite list_lookup_total_fmap; first lia.
      rewrite (list_lookup_total_correct _ _ _ Hlookup) //.
    - rewrite !list_lookup_insert_ne; [lia.. |].
      rewrite !list_lookup_fmap.
      destruct (decide (j < 2 * cap)).
      + rewrite lookup_seq_lt //=.
        repeat case_decide; try done; lia.
      + rewrite lookup_seq_ge //. lia.
  Qed.
  #[local] Lemma contents۰resizeｰcap 𝘩𝑎𝑠𝘩 cap contents :
    length contents = cap →
    contents۰resize 𝘩𝑎𝑠𝘩 cap contents cap = contents۰split 𝘩𝑎𝑠𝘩 cap contents.
  Proof.
    intros Hlength.
    assert (length (contents۰split 𝘩𝑎𝑠𝘩 cap contents) = 2 * cap) as Hlength'.
    { rewrite /contents۰split length_app !length_fmap. lia. }
    apply (list_eq_same_length _ _ (2 * cap)); [done | apply contents۰resizeｰlength |].
    intros j entries1 entries2 Hj.
    rewrite list_lookup_fmap lookup_seq_lt //= list_lookup_lookup_total_lt; first lia.
    intros [= <-] [= <-].
    rewrite decide_True //. lia.
  Qed.
End inv۰pure.

#[local] Arguments inv۰pure۰cap {_ _ _ _ _ _ _} _.
#[local] Arguments inv۰pure۰length {_ _ _ _ _ _ _} _.
#[local] Arguments inv۰pure۰index {_ _ _ _ _ _ _} _ _ _ _.
#[local] Arguments inv۰pure۰nodup {_ _ _ _ _ _ _} _ _ _.
#[local] Arguments inv۰pure۰model {_ _ _ _ _ _ _} _ _.

(* ------------------------------------------------------------------------ *)
(* Validity of [hash] and [equal]. *)

Section hashtbl۰valid.
  Context `{zoo۰G : !ZooG Σ}.

  (* Abstract keys: [key۰model key 𝑘𝑒𝑦] means that the key value [key]
     represents the abstract key [𝑘𝑒𝑦]. *)
  Context {Key : Type} `{!EqDecision Key}.
  Context (key۰model : val → Key → iProp Σ).

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type 𝘩𝑎𝑠𝘩 : Key → Z.

  (* A key value represents at most one abstract key. *)
  Definition hashtbl۰valid۰functional : iProp Σ :=
    □ ∀ key 𝑘𝑒𝑦1 𝑘𝑒𝑦2,
      key۰model key 𝑘𝑒𝑦1 -∗
      key۰model key 𝑘𝑒𝑦2 -∗
      ⌜𝑘𝑒𝑦1 = 𝑘𝑒𝑦2⌝.

  (* [hash] implements the pure function [𝘩𝑎𝑠𝘩] on abstract keys. *)
  Definition hashtbl۰valid۰hash hash 𝘩𝑎𝑠𝘩 : iProp Σ :=
    □ ∀ key 𝑘𝑒𝑦,
      key۰model key 𝑘𝑒𝑦 -∗
      WP hash key {{ res,
        ⌜res = #(𝘩𝑎𝑠𝘩 𝑘𝑒𝑦)⌝
      }}.

  (* [equal] decides equality of abstract keys. *)
  Definition hashtbl۰valid۰equal equal : iProp Σ :=
    □ ∀ key1 𝑘𝑒𝑦1 key2 𝑘𝑒𝑦2,
      key۰model key1 𝑘𝑒𝑦1 -∗
      key۰model key2 𝑘𝑒𝑦2 -∗
      WP equal key1 key2 {{ res,
        ⌜res = #(bool_decide (𝑘𝑒𝑦1 = 𝑘𝑒𝑦2))⌝
      }}.

  Definition hashtbl۰valid hash 𝘩𝑎𝑠𝘩 equal : iProp Σ :=
    hashtbl۰valid۰functional ∗
    hashtbl۰valid۰hash hash 𝘩𝑎𝑠𝘩 ∗
    hashtbl۰valid۰equal equal.
End hashtbl۰valid.

(* ------------------------------------------------------------------------ *)
(* Constants. *)

#[local] Definition min_capacity :=
  val۰to_nat' hashtbl٠min_capacity.
#[local] Lemma min_capacityｰis_pow2 :
  is_pow2 min_capacity.
Proof.
  exists 4. done.
Qed.
#[local] Lemma hashtbl٠min_capacityｰunfold :
  hashtbl٠min_capacity = #min_capacity.
Proof.
  done.
Qed.
Opaque hashtbl٠min_capacity.
Opaque min_capacity.

#[local] Lemma hashtbl٠max_capacityｰspec :
  ∃ n : Z,
  hashtbl٠max_capacity = #n.
Proof.
  destruct sys٠max_array_lengthｰspec as (n & Hn).
  exists n. rewrite /hashtbl٠max_capacity Hn //.
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification. *)

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.
  Context {Key : Type} `{Countable Key}.
  Context (key۰model : val → Key → iProp Σ).
  Context `{key۰modelｰpersistent : !∀ key 𝑘𝑒𝑦, Persistent (key۰model key 𝑘𝑒𝑦)}.

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type 𝘩𝑎𝑠𝘩 : Key → Z.
  Implicit Type m : gmap Key val.
  Implicit Type entry : entry Key.
  Implicit Type entries : list (entry Key).
  Implicit Type contents : list (list (entry Key)).

  (* [bucket] is a list of mutable [Cons] cells holding [entries]. *)
  #[local] Fixpoint bucket۰model bucket entries : iProp Σ :=
    match entries with
    | [] =>
        ⌜bucket = §hashtbl٠bucket٠Nil%V⌝
    | entry :: entries =>
        ∃ l next,
        ⌜bucket = #l⌝ ∗
        l ↦ₕ Header §hashtbl٠bucket٠Cons 3 ∗
        l.[hashtbl٠bucket٠key] ↦ entry.(entry۰key) ∗
        l.[hashtbl٠bucket٠data] ↦ entry.(entry۰value) ∗
        l.[hashtbl٠bucket٠next] ↦ next ∗
        key۰model entry.(entry۰key) entry.(entry۰𝑘𝑒𝑦) ∗
        bucket۰model next entries
    end.
  #[local] Arguments bucket۰model _ !_ / : assert.
  #[local] Instance : CustomIpat "bucket۰model" :=
    " ( %l{}
      & %next{}
      & ->
      & #Hl{}_header
      & Hl{}_key
      & Hl{}_data
      & Hl{}_next
      & #Hl{}_key_model
      & Hbucket{}_next
      )
    ".

  #[local] Lemma bucket۰modelｰreplicate n :
    ⊢ [∗ list] bucket; entries ∈ replicate n §hashtbl٠bucket٠Nil%V; replicate n [],
      bucket۰model bucket entries.
  Proof.
    induction n as [| n IH]; first done.
    rewrite /=. iSplit; first done.
    iApply IH.
  Qed.

  Please Definition hashtbl۰model t m : iProp Σ :=
    ∃ l hash 𝘩𝑎𝑠𝘩 equal buckets cap bucket_vals contents,
    ⌜t = #l⌝ ∗
    l.[hash] ↦□ hash ∗
    l.[equal] ↦□ equal ∗
    l.[buckets] ↦ buckets ∗
    l.[mask] ↦ #(⁺cap - 1) ∗
    l.[size] ↦ #(size m) ∗
    hashtbl۰valid key۰model hash 𝘩𝑎𝑠𝘩 equal ∗
    array۰model buckets (DfracOwn 1) bucket_vals ∗
    ( [∗ list] bucket; entries ∈ bucket_vals; contents,
      bucket۰model bucket entries
    ) ∗
    ⌜inv۰pure 𝘩𝑎𝑠𝘩 cap contents m⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{}
      & %hash{}
      & %𝘩𝑎𝑠𝘩{}
      & %equal{}
      & %buckets{}
      & %cap{}
      & %bucket_vals{}
      & %contents{}
      & {%Heq{eq};->}
      & #Hl{}_hash
      & #Hl{}_equal
      & Hl{}_buckets
      & Hl{}_mask
      & Hl{}_size
      & #(Hvalid{}_functional & Hvalid{}_hash & Hvalid{}_equal)
      & Hbuckets{}
      & Hbuckets{}_models
      & %Hinv{}
      )
    ".

  Lemma hashtbl۰modelｰexclusive t m1 m2 :
    hashtbl۰model t m1 -∗
    hashtbl۰model t m2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2 eq=2)". simplify_eq.
    iCombine "Hl1_buckets Hl2_buckets" gives %(? & _). done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Bucket.assoc]. *)

  #[local] Lemma hashtbl٠bucket٠assocｰspec equal key 𝑘𝑒𝑦 bucket entries :
    {{{
      hashtbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠assoc equal key bucket
    {{{
      RET entries۰lookup 𝑘𝑒𝑦 entries;
      bucket۰model bucket entries
    }}}.
  Proof.
    iIntros "%Φ (#Hequal & #Hkey & Hbucket) HΦ".

    iInduction entries as [| [key' v 𝑘𝑒𝑦'] entries] "IH" forall (bucket Φ).

    - iDestruct "Hbucket" as %->.
      wp۰rec.
      iSteps.

    - iDestruct "Hbucket" as "(:bucket۰model)".
      wp۰rec.
      wp۰match.
      wp۰load.
      wp۰apply+ (wpｰwand with "(Hequal Hkey Hl_key_model)") as (res) "->".
      case_bool_decide as H𝑘𝑒𝑦.

      + wp۰load.
        wp۰pures.
        rewrite /= decide_True //.
        iApply "HΦ". iFrameSteps.

      + wp۰load.
        wp۰apply ("IH" with "Hbucket_next") as "Hbucket_next".
        rewrite /= decide_False //.
        iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Bucket.mem]. *)

  #[local] Lemma hashtbl٠bucket٠memｰspec equal key 𝑘𝑒𝑦 bucket entries :
    {{{
      hashtbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠mem equal key bucket
    {{{
      RET #(bool_decide (is_Some (entries۰lookup 𝑘𝑒𝑦 entries)));
      bucket۰model bucket entries
    }}}.
  Proof.
    iIntros "%Φ (#Hequal & #Hkey & Hbucket) HΦ".

    wp۰rec.
    wp۰apply+ (hashtbl٠bucket٠assocｰspec with "[$Hequal $Hkey $Hbucket]") as "Hbucket".
    destruct (entries۰lookup 𝑘𝑒𝑦 entries).

    - wp۰pures.
      iApply ("HΦ" with "Hbucket").

    - wp۰pures.
      iApply ("HΦ" with "Hbucket").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Bucket.add]. *)

  #[local] Lemma hashtbl٠bucket٠addｰspec key 𝑘𝑒𝑦 v bucket entries :
    {{{
      key۰model key 𝑘𝑒𝑦 ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠add key v bucket
    {{{
      bucket'
    , RET bucket';
      bucket۰model bucket' (Entry key v 𝑘𝑒𝑦 :: entries)
    }}}.
  Proof.
    iIntros "%Φ (#Hkey & Hbucket) HΦ".

    wp۰rec.
    wp۰block l as "Hl_key Hl_data Hl_next" header:"#Hl_header".
    iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Bucket.remove]. *)

  #[local] Lemma hashtbl٠bucket٠remove₁ｰspec equal key 𝑘𝑒𝑦 (prev : location) bucket entries :
    {{{
      hashtbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      prev ↦ₕ Header §hashtbl٠bucket٠Cons 3 ∗
      prev.[hashtbl٠bucket٠next] ↦ bucket ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠remove₁ equal key #prev bucket
    {{{
      bucket'
    , RET entries۰lookup 𝑘𝑒𝑦 entries;
      prev.[hashtbl٠bucket٠next] ↦ bucket' ∗
      bucket۰model bucket' (entries۰remove 𝑘𝑒𝑦 entries)
    }}}.
  Proof.
    iIntros "%Φ (#Hequal & #Hkey & Hprev_header & Hprev_next & Hbucket) HΦ".

    iInduction entries as [| [key' v 𝑘𝑒𝑦'] entries] "IH" forall (prev bucket Φ).

    - iDestruct "Hbucket" as %->.
      wp۰rec.
      iSteps.

    - iDestruct "Hbucket" as "(:bucket۰model)".
      wp۰rec.
      wp۰match.
      wp۰load.
      wp۰apply+ (wpｰwand with "(Hequal Hkey Hl_key_model)") as (res) "->".
      case_bool_decide as H𝑘𝑒𝑦.

      + wp۰match.
        wp۰load.
        wp۰store.
        wp۰load.
        wp۰pures.
        rewrite /= !decide_True //.
        iApply "HΦ". iFrameSteps.

      + wp۰load.
        wp۰apply ("IH" with "Hl_header Hl_next Hbucket_next") as "%bucket' (Hl_next & Hbucket')".
        rewrite /= !decide_False //.
        iApply "HΦ". iFrameSteps.
  Qed.

  #[local] Lemma hashtbl٠bucket٠removeｰspec equal buckets bucket_vals (i : nat) key 𝑘𝑒𝑦 bucket entries :
    bucket_vals !! i = Some bucket →
    {{{
      hashtbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      array۰model buckets (DfracOwn 1) bucket_vals ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠remove equal buckets #i key bucket
    {{{
      bucket'
    , RET entries۰lookup 𝑘𝑒𝑦 entries;
      array۰model buckets (DfracOwn 1) (<[i := bucket']> bucket_vals) ∗
      bucket۰model bucket' (entries۰remove 𝑘𝑒𝑦 entries)
    }}}.
  Proof.
    iIntros "%Hlookup %Φ (#Hequal & #Hkey & Hbuckets & Hbucket) HΦ".

    pose proof (lookup_lt_Some _ _ _ Hlookup).

    destruct entries as [| [key' v 𝑘𝑒𝑦'] entries].

    - iDestruct "Hbucket" as %->.
      wp۰rec.
      wp۰pures.
      iApply "HΦ".
      rewrite list_insert_id //. iSteps.

    - iDestruct "Hbucket" as "(:bucket۰model)".
      wp۰rec.
      wp۰match.
      wp۰load.
      wp۰apply+ (wpｰwand with "(Hequal Hkey Hl_key_model)") as (res) "->".
      case_bool_decide as H𝑘𝑒𝑦.

      + wp۰load.
        wp۰apply (array٠unsafe_setｰspec with "Hbuckets") as "Hbuckets"; first lia.
        wp۰load.
        wp۰pures.
        rewrite /= !decide_True // Nat2Z.id.
        iApply "HΦ". iFrameSteps.

      + wp۰load.
        wp۰apply (hashtbl٠bucket٠remove₁ｰspec with "[$Hequal $Hkey $Hl_header $Hl_next $Hbucket_next]") as "%bucket' (Hl_next & Hbucket')".
        rewrite /= !decide_False //.
        iApply ("HΦ" $! #l).
        rewrite list_insert_id //. iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Bucket.replace]. *)

  #[local] Lemma hashtbl٠bucket٠replaceｰspec equal key 𝑘𝑒𝑦 v bucket entries :
    {{{
      hashtbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠replace equal key v bucket
    {{{
      RET entries۰lookup 𝑘𝑒𝑦 entries;
      bucket۰model bucket (entries۰replace 𝑘𝑒𝑦 v entries)
    }}}.
  Proof.
    iIntros "%Φ (#Hequal & #Hkey & Hbucket) HΦ".

    iInduction entries as [| [key' v' 𝑘𝑒𝑦'] entries] "IH" forall (bucket Φ).

    - iDestruct "Hbucket" as %->.
      wp۰rec.
      iSteps.

    - iDestruct "Hbucket" as "(:bucket۰model)".
      wp۰rec.
      wp۰match.
      wp۰load.
      wp۰apply+ (wpｰwand with "(Hequal Hkey Hl_key_model)") as (res) "->".
      case_bool_decide as H𝑘𝑒𝑦.

      + wp۰load.
        wp۰store.
        wp۰pures.
        rewrite /= !decide_True //.
        iApply "HΦ". iFrameSteps.

      + wp۰load.
        wp۰apply ("IH" with "Hbucket_next") as "Hbucket_next".
        rewrite /= !decide_False //.
        iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [Bucket.filter]. *)

  #[local] Lemma hashtbl٠bucket٠filterｰspec (P : Key → Prop) `{!∀ 𝑘𝑒𝑦, Decision (P 𝑘𝑒𝑦)} pred bucket entries :
    {{{
      □ (
        ∀ key 𝑘𝑒𝑦,
        key۰model key 𝑘𝑒𝑦 -∗
        WP pred key {{ res,
          ⌜res = #(bool_decide (P 𝑘𝑒𝑦))⌝
        }}
      ) ∗
      bucket۰model bucket entries
    }}}
      hashtbl٠bucket٠filter pred bucket
    {{{
      bucket'
    , RET bucket';
      bucket۰model bucket entries ∗
      bucket۰model bucket' (entries۰filter P entries)
    }}}.
  Proof.
    iIntros "%Φ (#Hpred & Hbucket) HΦ".

    iInduction entries as [| [key v 𝑘𝑒𝑦] entries] "IH" forall (bucket Φ).

    - iDestruct "Hbucket" as %->.
      wp۰rec.
      iSteps.

    - iDestruct "Hbucket" as "(:bucket۰model)".
      wp۰rec.
      wp۰match.
      wp۰load.
      wp۰apply+ (wpｰwand with "(Hpred Hl_key_model)") as (res) "->".
      rewrite /entries۰filter filter_cons. cbn [entry۰𝑘𝑒𝑦].
      case_bool_decide as HP.

      + rewrite decide_True //.
        wp۰load.
        wp۰apply ("IH" with "Hbucket_next") as "%bucket' (Hbucket_next & Hbucket')".
        wp۰load.
        wp۰load.
        wp۰block l' as "Hl'_key Hl'_data Hl'_next" header:"#Hl'_header".
        iApply "HΦ".
        iSplitL "Hl_key Hl_data Hl_next Hbucket_next".
        { iFrameSteps. }
        iFrameSteps.

      + rewrite decide_False //.
        wp۰load.
        wp۰apply ("IH" with "Hbucket_next") as "%bucket' (Hbucket_next & Hbucket')".
        iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [create]. *)

  Lemma hashtbl٠createｰspec hash 𝘩𝑎𝑠𝘩 equal :
    {{{
      hashtbl۰valid key۰model hash 𝘩𝑎𝑠𝘩 equal
    }}}
      hashtbl٠create hash equal
    {{{
      t
    , RET t;
      hashtbl۰model t ∅
    }}}.
  Proof.
    iIntros "%Φ #(Hvalid_functional & Hvalid_hash & Hvalid_equal) HΦ".

    wp۰rec.
    rewrite hashtbl٠min_capacityｰunfold.
    wp۰apply+ (array٠makeｰspec with "[//]") as "%buckets (_ & Hbuckets)".
    wp۰block l as "#Hl_hash #Hl_equal Hl_buckets Hl_mask Hl_size".
    rewrite Nat2Z.id.
    iDestruct (bucket۰modelｰreplicate min_capacity) as "Hbuckets_models".
    pose proof (inv۰pureｰempty 𝘩𝑎𝑠𝘩 min_capacity min_capacityｰis_pow2).

    iApply "HΦ".
    rewrite /hashtbl۰model map_size_empty.
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [size]. *)

  Lemma hashtbl٠sizeｰspec t m :
    {{{
      hashtbl۰model t m
    }}}
      hashtbl٠size t
    {{{
      RET #(size m);
      hashtbl۰model t m
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec.
    wp۰load.
    iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [index]. *)

  #[local] Lemma hashtbl٠indexｰspec l hash 𝘩𝑎𝑠𝘩 cap key 𝑘𝑒𝑦 :
    is_pow2 cap →
    {{{
      l.[hash] ↦□ hash ∗
      l.[mask] ↦ #(⁺cap - 1) ∗
      hashtbl۰valid۰hash key۰model hash 𝘩𝑎𝑠𝘩 ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠index #l key
    {{{
      RET #(index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦);
      l.[mask] ↦ #(⁺cap - 1)
    }}}.
  Proof.
    iIntros "%Hcap %Φ (#Hl_hash & Hl_mask & #Hvalid_hash & #Hkey) HΦ".

    pose proof (is_pow2ｰpos _ Hcap).

    wp۰rec.
    wp۰load.
    wp۰load.
    wp۰apply+ (wpｰwand with "(Hvalid_hash Hkey)") as (res) "->".
    wp۰pures.
    rewrite Zｰlandｰpow2ｰpred // -indexｰZ; first lia.
    iApply ("HΦ" with "Hl_mask").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find]. *)

  Lemma hashtbl٠findｰspec t m key 𝑘𝑒𝑦 :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠find t key
    {{{
      RET m !! 𝑘𝑒𝑦;
      hashtbl۰model t m
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Hkey) HΦ".

    pose proof (inv۰pure۰cap Hinv) as Hcap.
    destruct (inv۰pureｰlookup 𝑘𝑒𝑦 Hinv) as (entries & Hcontents_lookup & Hlookup).
    iDestruct (big_sepL2ｰlookupｰaccｰr with "Hbuckets_models") as "(%bucket & %Hbucket_vals_lookup & Hbucket & Hbuckets_models)"; first done.

    wp۰rec.
    wp۰apply+ (hashtbl٠indexｰspec with "[$Hl_hash $Hl_mask $Hvalid_hash $Hkey]") as "Hl_mask"; first done.
    wp۰load.
    wp۰apply+ (array٠unsafe_getｰspec (index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦) with "Hbuckets") as "Hbuckets"; [lia | done | lia |].
    wp۰load.
    wp۰apply (hashtbl٠bucket٠assocｰspec with "[$Hvalid_equal $Hkey $Hbucket]") as "Hbucket".
    iDestruct ("Hbuckets_models" with "Hbucket") as "Hbuckets_models".
    rewrite -Hlookup.

    iApply "HΦ".
    iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [mem]. *)

  Lemma hashtbl٠memｰspec t m key 𝑘𝑒𝑦 :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠mem t key
    {{{
      RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
      hashtbl۰model t m
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hkey) HΦ".

    wp۰rec.
    wp۰apply+ (hashtbl٠findｰspec with "[$Hmodel $Hkey]") as "Hmodel".
    destruct (m !! 𝑘𝑒𝑦) as [v |] eqn:Hlookup.

    - wp۰pures.
      rewrite (bool_decide_eq_true_2 (𝑘𝑒𝑦 ∈ dom m)); first by apply elem_of_dom.
      iApply ("HΦ" with "Hmodel").

    - wp۰pures.
      rewrite (bool_decide_eq_false_2 (𝑘𝑒𝑦 ∈ dom m)); first by apply not_elem_of_dom.
      iApply ("HΦ" with "Hmodel").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [resize]. *)

  #[local] Lemma hashtbl٠resizeｰspec t m :
    {{{
      hashtbl۰model t m
    }}}
      hashtbl٠resize t
    {{{
      RET ();
      hashtbl۰model t m
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    pose proof (inv۰pure۰cap Hinv) as Hcap.
    pose proof (is_pow2ｰpos _ Hcap).
    pose proof (inv۰pure۰length Hinv) as Hcontents_length.
    iDestruct (big_sepL2_length with "Hbuckets_models") as %Hlength.

    wp۰rec.
    wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hbuckets") as "Hbuckets".
    rewrite Hlength Hcontents_length.
    destruct hashtbl٠max_capacityｰspec as (max_capacity & ->).
    wp۰load.
    wp۰pures.
    rewrite (_ : Z.shiftl ⁺cap 1 = ⁺(2 * cap))%Z.
    { rewrite Z.shiftl_mul_pow2 // Z.pow_1_r. lia. }
    case_bool_decide as Hsize.

    - wp۰pures.
      case_bool_decide as Hmax.

      + wp۰apply+ (array٠makeｰspec with "[//]") as "%new_buckets (_ & Hnew_buckets)".
        rewrite Nat2Z.id.

        wp۰apply+ (forｰspecｰnat (λ i _,
          l.[buckets] ↦ buckets ∗
          array۰model buckets (DfracOwn 1) bucket_vals ∗
          ( [∗ list] bucket; entries ∈ bucket_vals; contents,
            bucket۰model bucket entries
          ) ∗
          ∃ new_bucket_vals,
          array۰model new_buckets (DfracOwn 1) new_bucket_vals ∗
          [∗ list] bucket; entries ∈ new_bucket_vals; contents۰resize 𝘩𝑎𝑠𝘩 cap contents i,
            bucket۰model bucket entries
        )%I 0 cap with "[$Hl_buckets $Hbuckets $Hbuckets_models Hnew_buckets]") as "(Hl_buckets & _ & _ & %new_bucket_vals & Hnew_buckets & Hnew_buckets_models)"; first lia.
        { iSplitL.
          { iFrame. rewrite contents۰resizeｰ0. iApply bucket۰modelｰreplicate. }

          iIntros "!> %i %δ _ %Hi (Hl_buckets & Hbuckets & Hbuckets_models & %new_bucket_vals & Hnew_buckets & Hnew_buckets_models)".
          destruct (lookup_lt_is_Some_2 contents i) as (entries & Hcontents_lookup); first lia.
          iDestruct (big_sepL2ｰlookupｰaccｰr with "Hbuckets_models") as "(%bucket & %Hbucket_vals_lookup & Hbucket & Hbuckets_models)"; first done.
          iDestruct (big_sepL2_length with "Hnew_buckets_models") as %Hnew_length.
          rewrite contents۰resizeｰlength in Hnew_length.

          wp۰load.
          wp۰apply+ (array٠unsafe_getｰspec i with "Hbuckets") as "Hbuckets"; [lia | done | lia |].
          wp۰apply+ (hashtbl٠bucket٠filterｰspec (λ 𝑘𝑒𝑦, Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = 0)%Z with "[$Hbucket]") as "%new_bucket_1 (Hbucket & Hnew_bucket_1)".
          { iIntros "!> %key %𝑘𝑒𝑦 #Hkey".
            wp۰rec.
            wp۰load.
            wp۰apply+ (wpｰwand with "(Hvalid_hash Hkey)") as (res) "->".
            iSteps.
          }
          wp۰apply+ (hashtbl٠bucket٠filterｰspec (λ 𝑘𝑒𝑦, Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = ⁺cap)%Z with "[$Hbucket]") as "%new_bucket_2 (Hbucket & Hnew_bucket_2)".
          { iIntros "!> %key %𝑘𝑒𝑦 #Hkey".
            wp۰rec.
            wp۰load.
            wp۰apply+ (wpｰwand with "(Hvalid_hash Hkey)") as (res) "->".
            iSteps.
          }
          iDestruct ("Hbuckets_models" with "Hbucket") as "Hbuckets_models".
          wp۰apply+ (array٠unsafe_setｰspec with "Hnew_buckets") as "Hnew_buckets"; first lia.
          wp۰apply+ (array٠unsafe_setｰspec with "Hnew_buckets") as "Hnew_buckets".
          { rewrite length_insert. lia. }
          rewrite Nat2Z.id (_ : ₊(⁺i + ⁺cap) = i + cap); first lia.
          iDestruct (big_sepL2ｰinsert i with "Hnew_buckets_models Hnew_bucket_1") as "Hnew_buckets_models"; first lia.
          iDestruct (big_sepL2ｰinsert (i + cap) with "Hnew_buckets_models Hnew_bucket_2") as "Hnew_buckets_models".
          { rewrite length_insert. lia. }
          rewrite contents۰resizeｰstep //.
          iSteps.
        }

        rewrite contents۰resizeｰcap //.
        wp۰store.
        wp۰store.
        wp۰pures.

        iApply "HΦ".
        iExists l, hash, 𝘩𝑎𝑠𝘩, equal, new_buckets, (2 * cap), new_bucket_vals, (contents۰split 𝘩𝑎𝑠𝘩 cap contents).
        iFrameSteps. iPureIntro.
        apply inv۰pureｰsplit. done.

      + wp۰pures.
        iApply "HΦ". iFrameSteps.

    - wp۰pures.
      iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [add]. *)

  Lemma hashtbl٠addｰspec t m key 𝑘𝑒𝑦 v :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠add t key v
    {{{
      RET #(bool_decide (𝑘𝑒𝑦 ∉ dom m));
      hashtbl۰model t (if decide (𝑘𝑒𝑦 ∈ dom m) then m else <[𝑘𝑒𝑦 := v]> m)
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Hkey) HΦ".

    pose proof (inv۰pure۰cap Hinv) as Hcap.
    destruct (inv۰pureｰlookup 𝑘𝑒𝑦 Hinv) as (entries & Hcontents_lookup & Hlookup).
    iDestruct (big_sepL2ｰinsertｰaccｰr with "Hbuckets_models") as "(%bucket & %Hbucket_vals_lookup & Hbucket & Hbuckets_models)"; first done.
    pose proof (lookup_lt_Some _ _ _ Hbucket_vals_lookup).

    wp۰rec.
    wp۰apply+ (hashtbl٠indexｰspec with "[$Hl_hash $Hl_mask $Hvalid_hash $Hkey]") as "Hl_mask"; first done.
    wp۰load.
    wp۰apply+ (array٠unsafe_getｰspec (index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦) with "Hbuckets") as "Hbuckets"; [lia | done | lia |].
    wp۰load.
    wp۰apply (hashtbl٠bucket٠memｰspec with "[$Hvalid_equal $Hkey $Hbucket]") as "Hbucket".
    destruct (decide (is_Some (entries۰lookup 𝑘𝑒𝑦 entries))) as [Hmem | Hmem].

    - rewrite (bool_decide_eq_true_2 (is_Some (entries۰lookup 𝑘𝑒𝑦 entries))) //.
      assert (𝑘𝑒𝑦 ∈ dom m) as Hdom.
      { rewrite elem_of_dom Hlookup //. }
      wp۰pures.
      iDestruct ("Hbuckets_models" with "Hbucket") as "Hbuckets_models".
      rewrite !list_insert_id // decide_True // bool_decide_eq_false_2; first naive.
      iApply "HΦ". iFrameSteps.

    - rewrite (bool_decide_eq_false_2 (is_Some (entries۰lookup 𝑘𝑒𝑦 entries))) //.
      apply eq_None_not_Some in Hmem.
      assert (𝑘𝑒𝑦 ∉ dom m) as Hdom.
      { rewrite not_elem_of_dom Hlookup //. }
      wp۰apply+ (hashtbl٠bucket٠addｰspec with "[$Hkey $Hbucket]") as "%bucket' Hbucket'".
      wp۰load.
      wp۰apply (array٠unsafe_setｰspec with "Hbuckets") as "Hbuckets"; first lia.
      iDestruct ("Hbuckets_models" with "Hbucket'") as "Hbuckets_models".
      wp۰load.
      wp۰store.
      rewrite Nat2Z.id.
      rewrite (_ : (⁺(size m) + 1)%Z = ⁺(size (<[𝑘𝑒𝑦 := v]> m))).
      { rewrite map_size_insert_None; first by apply not_elem_of_dom. lia. }
      wp۰apply+ (hashtbl٠resizeｰspec _ (<[𝑘𝑒𝑦 := v]> m) with "[- HΦ]") as "Hmodel".
      { iFrameSteps. iPureIntro.
        apply inv۰pureｰadd; done.
      }
      wp۰pures.
      rewrite decide_False // bool_decide_eq_true_2 //.
      iApply ("HΦ" with "Hmodel").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find_and_remove]. *)

  Lemma hashtbl٠find_and_removeｰspec t m key 𝑘𝑒𝑦 :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠find_and_remove t key
    {{{
      RET m !! 𝑘𝑒𝑦;
      hashtbl۰model t (delete 𝑘𝑒𝑦 m)
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Hkey) HΦ".

    pose proof (inv۰pure۰cap Hinv) as Hcap.
    destruct (inv۰pureｰlookup 𝑘𝑒𝑦 Hinv) as (entries & Hcontents_lookup & Hlookup).
    pose proof (inv۰pureｰremove 𝑘𝑒𝑦 entries Hinv Hcontents_lookup) as Hinv'.
    iDestruct (big_sepL2ｰinsertｰaccｰr with "Hbuckets_models") as "(%bucket & %Hbucket_vals_lookup & Hbucket & Hbuckets_models)"; first done.

    wp۰rec.
    wp۰apply+ (hashtbl٠indexｰspec with "[$Hl_hash $Hl_mask $Hvalid_hash $Hkey]") as "Hl_mask"; first done.
    wp۰load.
    wp۰apply+ (array٠unsafe_getｰspec (index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦) with "Hbuckets") as "Hbuckets"; [lia | done | lia |].
    wp۰load.
    wp۰load.
    wp۰apply (hashtbl٠bucket٠removeｰspec with "[$Hvalid_equal $Hkey $Hbuckets $Hbucket]") as "%bucket' (Hbuckets & Hbucket')"; first done.
    iDestruct ("Hbuckets_models" with "Hbucket'") as "Hbuckets_models".
    rewrite -Hlookup.
    destruct (m !! 𝑘𝑒𝑦) as [v |] eqn:Hm_lookup.

    - wp۰load.
      wp۰store.
      rewrite (_ : (⁺(size m) - 1)%Z = ⁺(size (delete 𝑘𝑒𝑦 m))).
      { assert (is_Some (m !! 𝑘𝑒𝑦)) as Hm_lookup' by eauto.
        pose proof (map_size_ne_0_lookup_2 _ _ Hm_lookup').
        rewrite map_size_delete_Some //. lia.
      }
      wp۰pures.
      iApply "HΦ". iFrameSteps.

    - wp۰pures.
      rewrite delete_id // in Hinv' |- *.
      iApply "HΦ". iFrameSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [remove]. *)

  Lemma hashtbl٠removeｰspec t m key 𝑘𝑒𝑦 :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠remove t key
    {{{
      RET ();
      hashtbl۰model t (delete 𝑘𝑒𝑦 m)
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hkey) HΦ".

    wp۰rec.
    wp۰apply+ (hashtbl٠find_and_removeｰspec with "[$Hmodel $Hkey]") as "Hmodel".
    wp۰pures.
    iApply ("HΦ" with "Hmodel").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find_and_replace]. *)

  Lemma hashtbl٠find_and_replaceｰspec t m key 𝑘𝑒𝑦 v :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠find_and_replace t key v
    {{{
      RET m !! 𝑘𝑒𝑦;
      hashtbl۰model t (<[𝑘𝑒𝑦 := v]> m)
    }}}.
  Proof.
    iIntros "%Φ ((:model) & #Hkey) HΦ".

    pose proof (inv۰pure۰cap Hinv) as Hcap.
    destruct (inv۰pureｰlookup 𝑘𝑒𝑦 Hinv) as (entries & Hcontents_lookup & Hlookup).
    iDestruct (big_sepL2ｰinsertｰaccｰr with "Hbuckets_models") as "(%bucket & %Hbucket_vals_lookup & Hbucket & Hbuckets_models)"; first done.
    pose proof (lookup_lt_Some _ _ _ Hbucket_vals_lookup).

    wp۰rec.
    wp۰apply+ (hashtbl٠indexｰspec with "[$Hl_hash $Hl_mask $Hvalid_hash $Hkey]") as "Hl_mask"; first done.
    wp۰load.
    wp۰apply+ (array٠unsafe_getｰspec (index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦) with "Hbuckets") as "Hbuckets"; [lia | done | lia |].
    wp۰load.
    wp۰apply (hashtbl٠bucket٠replaceｰspec with "[$Hvalid_equal $Hkey $Hbucket]") as "Hbucket".
    rewrite -Hlookup.
    destruct (m !! 𝑘𝑒𝑦) as [v' |] eqn:Hm_lookup.

    - wp۰pures.
      iDestruct ("Hbuckets_models" with "Hbucket") as "Hbuckets_models".
      rewrite list_insert_id //.
      assert (is_Some (m !! 𝑘𝑒𝑦)) as Hm_lookup' by eauto.
      pose proof (inv۰pureｰreplace 𝑘𝑒𝑦 entries v Hinv Hcontents_lookup ltac:(rewrite -Hlookup //)).
      iApply "HΦ".
      rewrite /hashtbl۰model map_size_insert_Some //.
      iFrameSteps.

    - rewrite entries۰replaceｰNone; first congruence.
      wp۰apply+ (hashtbl٠bucket٠addｰspec with "[$Hkey $Hbucket]") as "%bucket' Hbucket'".
      wp۰load.
      wp۰apply (array٠unsafe_setｰspec with "Hbuckets") as "Hbuckets"; first lia.
      iDestruct ("Hbuckets_models" with "Hbucket'") as "Hbuckets_models".
      wp۰load.
      wp۰store.
      rewrite Nat2Z.id.
      rewrite (_ : (⁺(size m) + 1)%Z = ⁺(size (<[𝑘𝑒𝑦 := v]> m))).
      { rewrite map_size_insert_None //. lia. }
      wp۰apply+ (hashtbl٠resizeｰspec _ (<[𝑘𝑒𝑦 := v]> m) with "[- HΦ]") as "Hmodel".
      { iFrameSteps. iPureIntro.
        apply inv۰pureｰadd; [done | done | congruence].
      }
      wp۰pures.
      iApply ("HΦ" with "Hmodel").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [replace]. *)

  Lemma hashtbl٠replaceｰspec t m key 𝑘𝑒𝑦 v :
    {{{
      hashtbl۰model t m ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      hashtbl٠replace t key v
    {{{
      RET ();
      hashtbl۰model t (<[𝑘𝑒𝑦 := v]> m)
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hkey) HΦ".

    wp۰rec.
    wp۰apply+ (hashtbl٠find_and_replaceｰspec with "[$Hmodel $Hkey]") as "Hmodel".
    wp۰pures.
    iApply ("HΦ" with "Hmodel").
  Qed.
End zoo۰G.

Require zoo_std.hashtbl__opaque.

Please opacify.
