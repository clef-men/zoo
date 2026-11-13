Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.math.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.mono_gset.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.htbl__code.
Require Import zoo_saturn.htbl__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v key hash equal backoff : val.

(* ------------------------------------------------------------------------ *)
(* Buckets. *)

(* A bucket without [Init] or [Resize], as a list of key-value pairs. *)
#[local] Fixpoint bucket۰to_val (bucket : list (val * val)) :=
  match bucket with
  | [] =>
      §htbl٠bucket٠Nil%V
  | (key, v) :: bucket =>
      ‘htbl٠bucket٠Cons[ key, v, bucket۰to_val bucket ]%V
  end.
#[local] Arguments bucket۰to_val !_ / : assert.

#[local] Instance bucket۰to_valｰinj :
  Inj (=) (=) bucket۰to_val.
Proof.
  intros bucket1. induction bucket1 as [| (key1, v1) bucket1 IH]; intros [| (key2, v2) bucket2]; try done.
  intros [= -> -> ->%IH]. done.
Qed.
#[local] Lemma bucket۰to_valｰsimilar bucket1 bucket2 :
  bucket۰to_val bucket1 ≈ bucket۰to_val bucket2 →
  bucket1 = bucket2.
Proof.
  destruct bucket1 as [| (key1, v1) bucket1], bucket2 as [| (key2, v2) bucket2]; try done.
  intros (_ & _ & [= -> -> ->%(inj _)]). done.
Qed.

(* The tag of a bucket value. *)
#[local] Definition bucket۰tag bucket :=
  match bucket۰to_val bucket with
  | ValBlock _ tag _ =>
      tag
  | _ =>
      Tag0
  end.
#[local] Arguments bucket۰tag !_ / : assert.

(* None of the branches [brs] matches a bucket value (same tag and same
   arity), so that a [match] on a bucket value takes its fallback branch. *)
#[local] Definition branches۰bucket۰fallback (brs : list branch) :=
  forallb (λ br, negb (br.1.(pattern۰tag) ≟ bucket۰tag [] && length br.1.(pattern۰fields) ≟ 0)) brs &&
  forallb (λ br, negb (br.1.(pattern۰tag) ≟ bucket۰tag [(()%V, ()%V)] && length br.1.(pattern۰fields) ≟ 3)) brs.
#[local] Arguments branches۰bucket۰fallback !_ / : assert.

(* This instance lets [wp۰pures] reduce a [match] on [bucket۰to_val bucket]
   when [bucket] is abstract. *)
#[local] Instance pureｰmatchｰbucket bucket x_fb e_fb brs :
  PureExec
    (branches۰bucket۰fallback brs = true)
    1
    (Match (Val $ bucket۰to_val bucket) x_fb e_fb brs)
    (subst' x_fb (bucket۰to_val bucket) e_fb).
Proof.
  intros (Hnil & Hcons)%andb_true_iff.
  destruct bucket as [| (key, v) bucket].
  - apply pureｰmatch, exec۰matchｰfallback, Hnil.
  - apply pureｰmatch, exec۰matchｰfallback, Hcons.
Qed.

(* ------------------------------------------------------------------------ *)
(* Entries and cells. *)

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

#[local] Definition entry۰binding {Key} (entry : entry Key) :=
  (entry.(entry۰key), entry.(entry۰value)).
#[local] Arguments entry۰binding _ !_ / : assert.

#[local] Abbreviation entries۰bucket entries :=
  (entry۰binding <$> entries).
#[local] Abbreviation entries۰𝑘𝑒𝑦𝑠 entries :=
  (entry۰𝑘𝑒𝑦 <$> entries).

Section entries.
  Context {Key : Type} `{Countable Key}.

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type 𝘩𝑎𝑠𝘩 : Key → Z.
  Implicit Type entry : entry Key.
  Implicit Type entries : list (entry Key).

  (* The value of the first binding of [𝑘𝑒𝑦], as found by
     [htbl٠bucket٠assoc]. *)
  #[local] Fixpoint entries۰lookup 𝑘𝑒𝑦 entries : option val :=
    match entries with
    | [] =>
        None
    | Entry _ v 𝑘𝑒𝑦' :: entries =>
        if decide (𝑘𝑒𝑦 = 𝑘𝑒𝑦') then Some v else entries۰lookup 𝑘𝑒𝑦 entries
    end.

  #[local] Lemma entries۰lookupｰNone 𝑘𝑒𝑦 entries :
    entries۰lookup 𝑘𝑒𝑦 entries = None ↔
    𝑘𝑒𝑦 ∉ entries۰𝑘𝑒𝑦𝑠 entries.
  Proof.
    induction entries as [| [key v 𝑘𝑒𝑦'] entries IH]; first set_solver.
    rewrite /= elem_of_cons. case_decide; naive.
  Qed.
  #[local] Lemma entries۰lookupｰSome 𝑘𝑒𝑦 entries v :
    entries۰lookup 𝑘𝑒𝑦 entries = Some v →
      ∃ key,
      Entry key v 𝑘𝑒𝑦 ∈ entries.
  Proof.
    induction entries as [| [key v' 𝑘𝑒𝑦'] entries IH]; first done.
    rewrite /=. case_decide as Hkey.
    - intros [= ->]. subst. exists key. set_solver.
    - intros (key' & ?)%IH. exists key'. set_solver.
  Qed.
  #[local] Lemma entries۰lookupｰSomeｰNoDup 𝑘𝑒𝑦 entries key v :
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries) →
    Entry key v 𝑘𝑒𝑦 ∈ entries →
    entries۰lookup 𝑘𝑒𝑦 entries = Some v.
  Proof.
    induction entries as [| [key' v' 𝑘𝑒𝑦'] entries IH]; first set_solver.
    rewrite fmap_cons NoDup_cons elem_of_cons /=.
    intros (Hnotin & Hnodup) [[= -> -> ->] | Hin].
    - rewrite decide_True //.
    - rewrite decide_False; last auto.
      intros ->. apply Hnotin, list_elem_of_fmap. exists (Entry key v 𝑘𝑒𝑦'). done.
  Qed.
  #[local] Lemma entries۰lookupｰapp 𝑘𝑒𝑦 entries1 entries2 :
    entries۰lookup 𝑘𝑒𝑦 (entries1 ++ entries2) =
      match entries۰lookup 𝑘𝑒𝑦 entries1 with
      | Some v =>
          Some v
      | None =>
          entries۰lookup 𝑘𝑒𝑦 entries2
      end.
  Proof.
    induction entries1 as [| [key v 𝑘𝑒𝑦'] entries1 IH]; first done.
    rewrite /=. case_decide; done.
  Qed.
  #[local] Lemma entries۰lookupｰfilter 𝑘𝑒𝑦 (P : entry Key → Prop) `{!∀ entry, Decision (P entry)} entries :
    ( ∀ entry,
      entry ∈ entries →
      entry.(entry۰𝑘𝑒𝑦) = 𝑘𝑒𝑦 →
      P entry
    ) →
    entries۰lookup 𝑘𝑒𝑦 (filter P entries) = entries۰lookup 𝑘𝑒𝑦 entries.
  Proof.
    induction entries as [| [key v 𝑘𝑒𝑦'] entries IH]; first done.
    intros HP.
    rewrite filter_cons /=.
    case_decide as HP'.
    - rewrite /=. case_decide; first done.
      apply IH. set_solver.
    - rewrite decide_False.
      { intros ->. apply HP', HP; set_solver. }
      apply IH. set_solver.
  Qed.

  #[local] Definition entries۰index 𝘩𝑎𝑠𝘩 (cap : nat) 𝑘𝑒𝑦 : nat :=
    ₊(𝘩𝑎𝑠𝘩 𝑘𝑒𝑦 `mod` ⁺cap).

  #[local] Lemma entries۰indexｰlt 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 :
    0 < cap →
    entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 < cap.
  Proof.
    intros Hcap.
    pose proof (Z.mod_pos_bound (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap ltac:(lia)).
    rewrite /entries۰index. lia.
  Qed.
  #[local] Lemma entries۰indexｰZ 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 :
    0 < cap →
    ⁺(entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦) = (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦 `mod` ⁺cap)%Z.
  Proof.
    intros Hcap.
    pose proof (Z.mod_pos_bound (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap ltac:(lia)).
    rewrite /entries۰index. lia.
  Qed.
  #[local] Lemma entries۰indexｰdouble 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 :
    is_pow2 cap →
    entries۰index 𝘩𝑎𝑠𝘩 (2 * cap) 𝑘𝑒𝑦 =
    entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 + (if bool_decide (Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = ⁺cap) then cap else 0).
  Proof.
    intros Hcap. pose proof (is_pow2ｰpos _ Hcap).
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_add entries۰indexｰZ; first lia.
    rewrite entries۰indexｰZ; first lia.
    rewrite Zｰmodｰpow2ｰdouble // Zｰlandｰpow2 //.
    destruct (Z.testbit _ _) => /=.
    - rewrite bool_decide_eq_true_2; lia.
    - rewrite bool_decide_eq_false_2; lia.
  Qed.
  #[local] Lemma entries۰indexｰhalf 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 :
    is_pow2 cap →
    entries۰index 𝘩𝑎𝑠𝘩 (2 * cap) 𝑘𝑒𝑦 `mod` cap = entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦.
  Proof.
    intros Hcap. pose proof (is_pow2ｰpos _ Hcap).
    rewrite entries۰indexｰdouble //.
    pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ltac:(lia)).
    case_bool_decide.
    - rewrite -{2}(Nat.mul_1_l cap) Nat.Div0.mod_add Nat.mod_small //.
    - rewrite Nat.add_0_r Nat.mod_small //.
  Qed.
  #[local] Lemma entries۰indexｰland 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 :
    is_pow2 cap →
      Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = 0%Z
    ∨ Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = ⁺cap.
  Proof.
    intros Hcap.
    rewrite Zｰlandｰpow2 //.
    destruct (Z.testbit _ _); [right | left]; simpl; lia.
  Qed.

  #[local] Definition entries۰wf 𝘩𝑎𝑠𝘩 cap i entries :=
    Forall (λ entry, entries۰index 𝘩𝑎𝑠𝘩 cap entry.(entry۰𝑘𝑒𝑦) = i) entries ∧
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries).

  #[local] Lemma entries۰wfｰlookup {𝘩𝑎𝑠𝘩 cap i entries 𝑘𝑒𝑦} :
    entries۰wf 𝘩𝑎𝑠𝘩 cap i entries →
    entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ≠ i →
    entries۰lookup 𝑘𝑒𝑦 entries = None.
  Proof.
    intros (Hentries & _) Hi.
    apply entries۰lookupｰNone.
    intros (entry & -> & Hin)%list_elem_of_fmap.
    rewrite Forall_forall in Hentries. apply Hi, (Hentries _ Hin).
  Qed.

  Inductive cell :=
    | CellInit
    | CellActive entries
    | CellFrozen entries.
  Implicit Type cell : cell.
  Implicit Type cells : list cell.

  #[local] Instance cellｰinhabited :
    Inhabited cell.
  Proof.
    exact (populate CellInit).
  Qed.

  #[local] Definition cell۰entries cell :=
    match cell with
    | CellInit =>
        []
    | CellActive entries
    | CellFrozen entries =>
        entries
    end.

  #[local] Definition cell۰to_val cell :=
    match cell with
    | CellInit =>
        §htbl٠bucket٠Init%V
    | CellActive entries =>
        bucket۰to_val (entries۰bucket entries)
    | CellFrozen entries =>
        ‘htbl٠bucket٠Resize( bucket۰to_val (entries۰bucket entries) )%V
    end.

  #[local] Lemma cellｰinitｰcases cell :
    cell = CellInit ∨ cell ≠ CellInit.
  Proof.
    destruct cell; [left | right..]; done.
  Qed.

  #[local] Definition cell۰is_frozen cell :=
    ∃ entries,
    cell = CellFrozen entries.
  #[local] Definition cell۰is_active cell :=
    ∃ entries,
    cell = CellActive entries.

  #[local] Definition cells۰wf 𝘩𝑎𝑠𝘩 cells :=
    ∀ i cell,
    cells !! i = Some cell →
    entries۰wf 𝘩𝑎𝑠𝘩 (length cells) i (cell۰entries cell).

  #[local] Definition cells۰lookup 𝘩𝑎𝑠𝘩 cells 𝑘𝑒𝑦 :=
    entries۰lookup 𝑘𝑒𝑦 (cell۰entries (cells !!! entries۰index 𝘩𝑎𝑠𝘩 (length cells) 𝑘𝑒𝑦)).

  #[local] Definition split۰entries 𝘩𝑎𝑠𝘩 (cap : nat) (hi : bool) entries :=
    filter (λ entry, Z.land (𝘩𝑎𝑠𝘩 entry.(entry۰𝑘𝑒𝑦)) ⁺cap = if hi then ⁺cap else 0%Z) entries.

  #[local] Definition cells۰pending۰split 𝘩𝑎𝑠𝘩 cells j cell' :=
      cell' = CellInit
    ∨ ∃ entries,
      cells !! (j `mod` length cells) = Some (CellFrozen entries) ∧
      cell' = CellActive (split۰entries 𝘩𝑎𝑠𝘩 (length cells) (bool_decide (length cells ≤ j)) entries).
  #[local] Definition cells۰pending۰merge cells cap' j cell' :=
      cell' = CellInit
    ∨ ∃ entries1 entries2,
      cells !! j = Some (CellFrozen entries1) ∧
      cells !! (j + cap') = Some (CellFrozen entries2) ∧
      cell' = CellActive (entries2 ++ entries1).
  #[local] Definition cells۰pending 𝘩𝑎𝑠𝘩 cells cells' :=
    ( length cells' = 2 * length cells ∧
        ∀ j cell',
        cells' !! j = Some cell' →
        cells۰pending۰split 𝘩𝑎𝑠𝘩 cells j cell'
    ) ∨ (
      length cells = 2 * length cells' ∧
        ∀ j cell',
        cells' !! j = Some cell' →
        cells۰pending۰merge cells (length cells') j cell'
    ).

  #[local] Lemma entries۰wfｰsublist 𝘩𝑎𝑠𝘩 cap i entries1 entries2 :
    entries1 `sublist_of` entries2 →
    entries۰wf 𝘩𝑎𝑠𝘩 cap i entries2 →
    entries۰wf 𝘩𝑎𝑠𝘩 cap i entries1.
  Proof.
    intros Hsub (Hentries2 & Hnodup). split.
    - rewrite Forall_forall in Hentries2.
      apply Forall_forall. intros entry Hentry.
      apply Hentries2, (elem_of_sublist _ _ _ Hentry Hsub).
    - apply (sublist_NoDup _ (entries۰𝑘𝑒𝑦𝑠 entries2)); first done.
      apply fmap_sublist. done.
  Qed.

  #[local] Lemma entries۰lookupｰdelete 𝑘𝑒𝑦 entries k 𝑘𝑒𝑦' :
    NoDup (entries۰𝑘𝑒𝑦𝑠 entries) →
    entries۰𝑘𝑒𝑦𝑠 entries !! k = Some 𝑘𝑒𝑦 →
    entries۰lookup 𝑘𝑒𝑦' (delete k entries) =
      if decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦) then None else entries۰lookup 𝑘𝑒𝑦' entries.
  Proof.
    revert k. induction entries as [| [key v 𝑘𝑒𝑦''] entries IH]; first done.
    intros [| k] Hnodup Hlookup; rewrite fmap_cons NoDup_cons in Hnodup; destruct Hnodup as (Hnotin & Hnodup).
    - injection Hlookup as ->. rewrite /=.
      case_decide as Heq; last done.
      subst. apply entries۰lookupｰNone. done.
    - rewrite /= IH //.
      case_decide as Heq1; case_decide as Heq2; try done; subst.
      exfalso. apply Hnotin, list_elem_of_lookup_2 with k. done.
  Qed.

  #[local] Lemma cells۰lookupｰinsert 𝘩𝑎𝑠𝘩 cells i cell 𝑘𝑒𝑦 :
    i < length cells →
    cells۰lookup 𝘩𝑎𝑠𝘩 (<[i := cell]> cells) 𝑘𝑒𝑦 =
      if decide (entries۰index 𝘩𝑎𝑠𝘩 (length cells) 𝑘𝑒𝑦 = i) then
        entries۰lookup 𝑘𝑒𝑦 (cell۰entries cell)
      else
        cells۰lookup 𝘩𝑎𝑠𝘩 cells 𝑘𝑒𝑦.
  Proof.
    intros Hi.
    rewrite /cells۰lookup length_insert.
    case_decide as Heq.
    - rewrite Heq list_lookup_total_insert decide_True //.
    - rewrite list_lookup_total_insert_ne //.
  Qed.

  #[local] Lemma cells۰wfｰinsert 𝘩𝑎𝑠𝘩 cells i cell :
    entries۰wf 𝘩𝑎𝑠𝘩 (length cells) i (cell۰entries cell) →
    cells۰wf 𝘩𝑎𝑠𝘩 cells →
    cells۰wf 𝘩𝑎𝑠𝘩 (<[i := cell]> cells).
  Proof.
    intros Hcell Hcells j cell'.
    rewrite length_insert list_lookup_insert_Some.
    intros [(<- & <- & _) | (_ & Hlookup)]; first done.
    apply Hcells. done.
  Qed.

  #[local] Lemma cells۰pendingｰwf 𝘩𝑎𝑠𝘩 cells cells' :
    is_pow2 (length cells) →
    is_pow2 (length cells') →
    cells۰wf 𝘩𝑎𝑠𝘩 cells →
    cells۰pending 𝘩𝑎𝑠𝘩 cells cells' →
    cells۰wf 𝘩𝑎𝑠𝘩 cells'.
  Proof.
    intros Hcap Hcap' Hcells Hpending j cell' Hlookup.
    pose proof (is_pow2ｰpos _ Hcap).
    pose proof (is_pow2ｰpos _ Hcap').
    pose proof (lookup_lt_Some _ _ _ Hlookup).
    destruct Hpending as [(Hlen & Hpending) | (Hlen & Hpending)];
      opose proof* (Hpending j cell') as [-> | Hcell']; try done;
      try (split; [apply Forall_nil | apply NoDup_nil]; done).
    - destruct Hcell' as (entries & Hentries & ->).
      opose proof* (Hcells (j `mod` length cells)) as (Hentries1 & Hentries2); first done.
      split; last first.
      { apply (sublist_NoDup _ (entries۰𝑘𝑒𝑦𝑠 entries)); first done.
        apply fmap_sublist, sublist_filter.
      }
      rewrite /= /split۰entries Forall_forall.
      rewrite Forall_forall in Hentries1.
      intros entry (Hland & Hentry)%list_elem_of_filter.
      opose proof* (Hentries1 entry Hentry) as Hindex.
      rewrite Hlen entries۰indexｰdouble // Hindex.
      case_bool_decide as Hj.
      + rewrite bool_decide_eq_true_2 //.
        assert (j `div` length cells = 1) as Hdiv.
        { symmetry. apply Nat.div_unique with (j - length cells); lia. }
        pose proof (Nat.div_mod j (length cells) ltac:(lia)). lia.
      + rewrite bool_decide_eq_false_2; first lia.
        rewrite Nat.add_0_r Nat.mod_small //. lia.
    - destruct Hcell' as (entries1 & entries2 & Hentries1 & Hentries2 & ->).
      opose proof* (Hcells j) as (Hentries1_1 & Hentries1_2); first done.
      opose proof* (Hcells (j + length cells')) as (Hentries2_1 & Hentries2_2); first done.
      rewrite Hlen /= in Hentries1_1 Hentries2_1.
      rewrite Forall_forall in Hentries1_1.
      rewrite Forall_forall in Hentries2_1.
      split.
      + rewrite /= Forall_app !Forall_forall. split.
        * intros entry Hentry.
          rewrite -entries۰indexｰhalf // (Hentries2_1 _ Hentry).
          rewrite -{1}(Nat.mul_1_l (length cells')) Nat.Div0.mod_add Nat.mod_small //.
        * intros entry Hentry.
          rewrite -entries۰indexｰhalf // (Hentries1_1 _ Hentry) Nat.mod_small //.
      + rewrite /= fmap_app NoDup_app. split_and!; try done.
        intros 𝑘𝑒𝑦 (entry2 & -> & Hentry2)%list_elem_of_fmap (entry1 & Heq & Hentry1)%list_elem_of_fmap.
        opose proof* (Hentries1_1 _ Hentry1) as Hi1.
        opose proof* (Hentries2_1 _ Hentry2) as Hi2.
        rewrite Heq in Hi2. lia.
  Qed.

  #[local] Lemma cells۰pendingｰinstall 𝘩𝑎𝑠𝘩 cells cells' :
    is_pow2 (length cells) →
    is_pow2 (length cells') →
    cells۰wf 𝘩𝑎𝑠𝘩 cells →
    cells۰pending 𝘩𝑎𝑠𝘩 cells cells' →
    ( ∀ j cell',
      cells' !! j = Some cell' →
      cell' ≠ CellInit
    ) →
      ( ∀ i cell,
        cells !! i = Some cell →
        cell۰is_frozen cell
      ) ∧
      ( ∀ j cell',
        cells' !! j = Some cell' →
        cell۰is_active cell'
      ) ∧
      ( ∀ 𝑘𝑒𝑦,
        cells۰lookup 𝘩𝑎𝑠𝘩 cells' 𝑘𝑒𝑦 = cells۰lookup 𝘩𝑎𝑠𝘩 cells 𝑘𝑒𝑦
      ).
  Proof.
    intros Hcap Hcap' Hcells Hpending Hinit.
    pose proof (is_pow2ｰpos _ Hcap).
    pose proof (is_pow2ｰpos _ Hcap').
    destruct Hpending as [(Hlen & Hpending) | (Hlen & Hpending)]; split_and!.
    - intros i cell Hlookup.
      pose proof (lookup_lt_Some _ _ _ Hlookup).
      destruct (lookup_lt_is_Some_2 cells' i) as (cell' & Hlookup'); first lia.
      opose proof* (Hpending i cell' Hlookup') as [? | (entries & Hentries & _)]; [by exfalso; eapply Hinit; [eassumption | done] | ].
      rewrite Nat.mod_small // in Hentries. simplify_eq. by eexists.
    - intros j cell' Hlookup.
      opose proof* (Hpending j cell' Hlookup) as [? | (entries & _ & ?)]; try subst cell'; [by exfalso; eapply Hinit; [eassumption | done] | by eexists].
    - intros 𝑘𝑒𝑦.
      rewrite /cells۰lookup Hlen.
      pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 (2 * length cells) 𝑘𝑒𝑦 ltac:(lia)) as Hlt.
      destruct (lookup_lt_is_Some_2 cells' (entries۰index 𝘩𝑎𝑠𝘩 (2 * length cells) 𝑘𝑒𝑦)) as (cell' & Hlookup'); first lia.
      opose proof* (Hpending _ cell' Hlookup') as [? | (entries & Hentries & ?)]; try subst cell'; [by exfalso; eapply Hinit; [eassumption | done] | ].
      rewrite (list_lookup_total_correct _ _ _ Hlookup').
      rewrite entries۰indexｰhalf // in Hentries.
      rewrite (list_lookup_total_correct _ _ _ Hentries) /=.
      apply entries۰lookupｰfilter.
      intros entry Hentry <-.
      rewrite entries۰indexｰdouble //.
      pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 (length cells) entry.(entry۰𝑘𝑒𝑦) ltac:(lia)).
      pose proof (entries۰indexｰland 𝘩𝑎𝑠𝘩 (length cells) entry.(entry۰𝑘𝑒𝑦) Hcap) as [Hland | Hland];
        rewrite Hland; repeat case_bool_decide; lia.
    - intros i cell Hlookup.
      pose proof (lookup_lt_Some _ _ _ Hlookup).
      destruct (decide (i < length cells')).
      + destruct (lookup_lt_is_Some_2 cells' i) as (cell' & Hlookup'); first lia.
        opose proof* (Hpending i cell' Hlookup') as [? | (entries1 & entries2 & Hentries1 & _ & _)]; [by exfalso; eapply Hinit; [eassumption | done] | ].
        simplify_eq. by eexists.
      + destruct (lookup_lt_is_Some_2 cells' (i - length cells')) as (cell' & Hlookup'); first lia.
        opose proof* (Hpending _ cell' Hlookup') as [? | (entries1 & entries2 & _ & Hentries2 & _)]; [by exfalso; eapply Hinit; [eassumption | done] | ].
        rewrite Nat.sub_add in Hentries2; first lia.
        simplify_eq. by eexists.
    - intros j cell' Hlookup.
      opose proof* (Hpending j cell' Hlookup) as [? | (entries1 & entries2 & _ & _ & ?)]; try subst cell'; [by exfalso; eapply Hinit; [eassumption | done] | by eexists].
    - intros 𝑘𝑒𝑦.
      rewrite /cells۰lookup Hlen.
      pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 (length cells') 𝑘𝑒𝑦 ltac:(lia)) as Hlt.
      destruct (lookup_lt_is_Some_2 cells' (entries۰index 𝘩𝑎𝑠𝘩 (length cells') 𝑘𝑒𝑦)) as (cell' & Hlookup'); first lia.
      opose proof* (Hpending _ cell' Hlookup') as [? | (entries1 & entries2 & Hentries1 & Hentries2 & ?)]; try subst cell'; [by exfalso; eapply Hinit; [eassumption | done] | ].
      rewrite (list_lookup_total_correct _ _ _ Hlookup') /= entries۰lookupｰapp.
      opose proof* (Hcells _ _ Hentries1) as Hwf1.
      opose proof* (Hcells _ _ Hentries2) as Hwf2.
      rewrite Hlen in Hwf1 Hwf2.
      pose proof (entries۰indexｰdouble 𝘩𝑎𝑠𝘩 (length cells') 𝑘𝑒𝑦 Hcap') as Hidx.
      rewrite Hidx.
      case_bool_decide.
      + rewrite (entries۰wfｰlookup Hwf1); first lia.
        rewrite (list_lookup_total_correct _ _ _ Hentries2) /=.
        destruct (entries۰lookup _ _); done.
      + rewrite Nat.add_0_r.
        rewrite (entries۰wfｰlookup Hwf2); first lia.
        rewrite (list_lookup_total_correct _ _ _ Hentries1) //.
  Qed.

  #[local] Lemma cells۰pendingｰinsert 𝘩𝑎𝑠𝘩 cells cells' j cell' :
    cells۰pending 𝘩𝑎𝑠𝘩 cells cells' →
    (length cells' = 2 * length cells → cells۰pending۰split 𝘩𝑎𝑠𝘩 cells j cell') →
    (length cells = 2 * length cells' → cells۰pending۰merge cells (length cells') j cell') →
    cells۰pending 𝘩𝑎𝑠𝘩 cells (<[j := cell']> cells').
  Proof.
    intros [(Hlen & Hpending) | (Hlen & Hpending)] Hsplit Hmerge.
    - left. rewrite length_insert. split; first done.
      intros j' cell'' [(<- & <- & _) | (_ & Hj')]%list_lookup_insert_Some.
      + apply Hsplit. done.
      + apply Hpending. done.
    - right. rewrite length_insert. split; first done.
      intros j' cell'' [(<- & <- & _) | (_ & Hj')]%list_lookup_insert_Some.
      + apply Hmerge. done.
      + apply Hpending. done.
  Qed.
End entries.

#[local] Existing Instance cellｰinhabited.

#[local] Arguments cell : clear implicits.
#[local] Arguments CellInit {_}.

Section htbl۰valid.
  Context `{zoo۰G : !ZooG Σ}.

  (* Abstract keys: [key۰model key 𝑘𝑒𝑦] means that the key value [key]
     represents the abstract key [𝑘𝑒𝑦]. *)
  Context {Key : Type} `{!EqDecision Key}.
  Context (key۰model : val → Key → iProp Σ).

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type 𝘩𝑎𝑠𝘩 : Key → Z.

  (* A key value represents at most one abstract key. *)
  Definition htbl۰valid۰functional : iProp Σ :=
    □ ∀ key 𝑘𝑒𝑦1 𝑘𝑒𝑦2,
      key۰model key 𝑘𝑒𝑦1 -∗
      key۰model key 𝑘𝑒𝑦2 -∗
      ⌜𝑘𝑒𝑦1 = 𝑘𝑒𝑦2⌝.

  (* [hash] implements the pure function [𝘩𝑎𝑠𝘩] on abstract keys. *)
  Definition htbl۰valid۰hash hash 𝘩𝑎𝑠𝘩 : iProp Σ :=
    □ ∀ key 𝑘𝑒𝑦,
      key۰model key 𝑘𝑒𝑦 -∗
      WP hash key {{ res,
        ⌜res = #(𝘩𝑎𝑠𝘩 𝑘𝑒𝑦)⌝
      }}.

  (* [equal] decides equality of abstract keys. *)
  Definition htbl۰valid۰equal equal : iProp Σ :=
    □ ∀ key1 𝑘𝑒𝑦1 key2 𝑘𝑒𝑦2,
      key۰model key1 𝑘𝑒𝑦1 -∗
      key۰model key2 𝑘𝑒𝑦2 -∗
      WP equal key1 key2 {{ res,
        ⌜res = #(bool_decide (𝑘𝑒𝑦1 = 𝑘𝑒𝑦2))⌝
      }}.

  Definition htbl۰valid hash 𝘩𝑎𝑠𝘩 equal : iProp Σ :=
    htbl۰valid۰functional ∗
    htbl۰valid۰hash hash 𝘩𝑎𝑠𝘩 ∗
    htbl۰valid۰equal equal.
End htbl۰valid.

(* ------------------------------------------------------------------------ *)
(* Constants. *)

#[local] Definition min_buckets :=
  val۰to_nat' htbl٠min_buckets.
#[local] Lemma min_bucketsｰis_pow2 :
  is_pow2 min_buckets.
Proof.
  exists 4. done.
Qed.
#[local] Lemma htbl٠min_bucketsｰunfold :
  htbl٠min_buckets = #min_buckets.
Proof.
  done.
Qed.
Opaque htbl٠min_buckets.
Opaque min_buckets.

#[local] Lemma htbl٠max_bucketsｰspec :
  ∃ n : Z,
  htbl٠max_buckets = #n.
Proof.
  destruct sys٠max_array_lengthｰspec as (n & Hn).
  exists n. rewrite /htbl٠max_buckets Hn //.
Qed.

(* ------------------------------------------------------------------------ *)
(* States. *)

#[local] Definition status۰to_val (o : option (val * nat)) :=
  match o with
  | None =>
      §htbl٠Normal%V
  | Some (buckets, cap) =>
      ‘htbl٠Resizing( buckets, #(⁺cap - 1) )%V
  end.

#[local] Definition state۰to_val (buckets : val) (cap : nat) o :=
  (buckets, #(⁺cap - 1), status۰to_val o)%V.

#[local] Lemma status۰to_valｰsimilarｰNormal o :
  status۰to_val o ≈ §htbl٠Normal%V →
  o = None.
Proof.
  destruct o as [[] |]; done.
Qed.

#[local] Lemma state۰to_valｰsimilar buckets1 cap1 o1 buckets2 cap2 o2 :
  state۰to_val buckets1 cap1 o1 ≈ state۰to_val buckets2 cap2 o2 →
    buckets1 ≈ buckets2 ∧
    cap1 = cap2 ∧
    (o1 = None ↔ o2 = None).
Proof.
  intros H.
  destruct o1 as [(buckets1', cap1') |], o2 as [(buckets2', cap2') |];
    cbn in H; destruct_and! H; simplify_eq; try done.

  - split; first done. split; [lia | done].

  - split; first done. split; [lia | done].
Qed.

(* ------------------------------------------------------------------------ *)
(* Ghost state. *)

Zoo name :=
  { self : location
  ; inv : namespace
  ; model : gname
  ; generations : gname
  ; current : gname
  ; frozen : gname
  ; inited : gname
  ; waiters : gname
  }.

Record waiter :=
  { waiter۰generation : nat
  ; waiter۰key : val
  }.

Zoo global Key `{Countable Key} :=
  { model : twins (leibnizO (gmap Key val))
  ; generations : mono_list (val * nat)
  ; current : auth_nat_max
  ; frozen : ghost_map (nat * nat) (list (entry Key)) : iris
  ; inited : mono_gset (nat * nat)
  ; waiters : ghost_map gname waiter : iris
  ; waiter۰post : saved_pred (option val)
  }.

Section htbl۰G.
  Context `{htbl۰G : HtblG Σ Key}.
  Context (key۰model : val → Key → iProp Σ).
  Context `{key۰modelｰpersistent : !∀ key 𝑘𝑒𝑦, Persistent (key۰model key 𝑘𝑒𝑦)}.

  Implicit Type 𝑘𝑒𝑦 : Key.
  Implicit Type 𝘩𝑎𝑠𝘩 : Key → Z.
  Implicit Type m : gmap Key val.
  Implicit Type entry : entry Key.
  Implicit Type entries : list (entry Key).
  Implicit Type cell : cell Key.
  Implicit Type cells : list (cell Key).
  Implicit Type gen : val * list (cell Key).
  Implicit Type gens : list (val * list (cell Key)).
  Implicit Type η : gname.
  Implicit Type waiter : waiter.
  Implicit Type waiters : gmap gname waiter.
  Implicit Type cur g i j : nat.

  #[local] Definition entries۰model entries : iProp Σ :=
    [∗ list] entry ∈ entries, key۰model entry.(entry۰key) entry.(entry۰𝑘𝑒𝑦).

  #[local] Instance entries۰modelｰpersistent entries :
    Persistent (entries۰model entries).
  Proof.
    apply _.
  Qed.

  #[local] Definition model₁' (γ_model : gname) m :=
    twins۰twin₁ γ_model (DfracOwn 1) m.
  #[local] Definition model₁ γ :=
    model₁' γ.(htbl۰name۰model).
  #[local] Definition model₂' (γ_model : gname) m :=
    twins۰twin₂ γ_model m.
  #[local] Definition model₂ γ :=
    model₂' γ.(htbl۰name۰model).

  #[local] Definition generations۰phys gens :=
    (λ gen, (gen.1, length gen.2)) <$> gens.
  #[local] Definition generations۰auth' (γ_generations : gname) gens :=
    mono_list۰auth γ_generations (DfracOwn 1) (generations۰phys gens).
  #[local] Definition generations۰auth γ :=
    generations۰auth' γ.(htbl۰name۰generations).
  #[local] Definition generations۰at γ g (buckets : val) (cap : nat) :=
    mono_list۰at γ.(htbl۰name۰generations) g (buckets, cap).

  #[local] Definition current۰auth' (γ_current : gname) :=
    auth_nat_max۰auth γ_current (DfracOwn 1).
  #[local] Definition current۰auth γ :=
    current۰auth' γ.(htbl۰name۰current).
  #[local] Definition current۰lb γ :=
    auth_nat_max۰lb γ.(htbl۰name۰current).

  #[local] Definition frozen۰auth' (γ_frozen : gname) (frozen : gmap (nat * nat) (list (entry Key))) :=
    ghost_map_auth γ_frozen (DfracOwn 1) frozen.
  #[local] Definition frozen۰auth γ :=
    frozen۰auth' γ.(htbl۰name۰frozen).
  #[local] Definition frozen۰elem γ (g i : nat) entries :=
    ghost_map_elem γ.(htbl۰name۰frozen) (g, i) DfracDiscarded entries.

  #[local] Definition inited۰auth' (γ_inited : gname) :=
    mono_gset۰auth γ_inited (DfracOwn 1).
  #[local] Definition inited۰auth γ :=
    inited۰auth' γ.(htbl۰name۰inited).
  #[local] Definition inited۰elem γ (g j : nat) :=
    mono_gset۰elem γ.(htbl۰name۰inited) (g, j).

  #[local] Definition waiters۰auth' (γ_waiters : gname) waiters :=
    ghost_map_auth γ_waiters (DfracOwn 1) waiters.
  #[local] Definition waiters۰auth γ :=
    waiters۰auth' γ.(htbl۰name۰waiters).
  #[local] Definition waiters۰elem γ η waiter :=
    ghost_map_elem γ.(htbl۰name۰waiters) η (DfracOwn 1) waiter.

  #[local] Definition generations۰state gens cur (resizing : bool) :=
    let gen := gens !!! cur in
    let gen' := gens !!! ˖cur in
    state۰to_val gen.1 (length gen.2) (if resizing then Some (gen'.1, length gen'.2) else None).

  Record inv۰pure 𝘩𝑎𝑠𝘩 gens cur (resizing : bool) m (frozen : gmap (nat * nat) (list (entry Key))) (inited : gset (nat * nat)) waiters : Prop :=
    { inv۰pure۰length :
        length gens = ˖cur + Nat.b2n resizing
    ; inv۰pure۰nodup :
        NoDup gens.*1
    ; inv۰pure۰pow2 g gen :
        gens !! g = Some gen →
        is_pow2 (length gen.2)
    ; inv۰pure۰caps g gen gen' :
        gens !! g = Some gen →
        gens !! ˖g = Some gen' →
          length gen'.2 = 2 * length gen.2
        ∨ length gen.2 = 2 * length gen'.2
    ; inv۰pure۰wf g gen :
        gens !! g = Some gen →
        cells۰wf 𝘩𝑎𝑠𝘩 gen.2
    ; inv۰pure۰old g gen i cell :
        g < cur →
        gens !! g = Some gen →
        gen.2 !! i = Some cell →
        cell۰is_frozen cell
    ; inv۰pure۰cur gen i cell :
        gens !! cur = Some gen →
        gen.2 !! i = Some cell →
        if resizing then cell ≠ CellInit else cell۰is_active cell
    ; inv۰pure۰pending gen gen' :
        resizing →
        gens !! cur = Some gen →
        gens !! ˖cur = Some gen' →
        cells۰pending 𝘩𝑎𝑠𝘩 gen.2 gen'.2
    ; inv۰pure۰model gen 𝑘𝑒𝑦 :
        gens !! cur = Some gen →
        m !! 𝑘𝑒𝑦 = cells۰lookup 𝘩𝑎𝑠𝘩 gen.2 𝑘𝑒𝑦
    ; inv۰pure۰frozen g i bucket :
        frozen !! (g, i) = Some bucket ↔
          ∃ gen entries,
          gens !! g = Some gen ∧
          gen.2 !! i = Some (CellFrozen entries) ∧
          entries = bucket
    ; inv۰pure۰inited g j :
        (g, j) ∈ inited →
          ∃ gen cell,
          gens !! g = Some gen ∧
          gen.2 !! j = Some cell ∧
          cell ≠ CellInit
    ; inv۰pure۰waiters η waiter :
        waiters !! η = Some waiter →
        waiter.(waiter۰generation) ≤ cur
    }.
  #[local] Arguments inv۰pure۰length {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰nodup {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰pow2 {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰caps {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰wf {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰old {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰cur {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰pending {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰model {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰frozen {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰inited {_ _ _ _ _ _ _ _}.
  #[local] Arguments inv۰pure۰waiters {_ _ _ _ _ _ _ _}.

  #[local] Definition waiter۰au γ 𝑘𝑒𝑦 (Ψ : option val → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ m,
      model₁ γ m
    }> @ ⊤ ∖ ↑γ.(htbl۰name۰inv), ∅ <{
      model₁ γ m
    , COMM
      Ψ (m !! 𝑘𝑒𝑦)
    }>.
  #[local] Definition waiter۰model γ 𝘩𝑎𝑠𝘩 gens cur η waiter : iProp Σ :=
    ∃ 𝑘𝑒𝑦 Ψ,
    key۰model waiter.(waiter۰key) 𝑘𝑒𝑦 ∗
    saved_pred η Ψ ∗
    if decide (waiter.(waiter۰generation) = cur) then
      waiter۰au γ 𝑘𝑒𝑦 Ψ
    else
      Ψ (cells۰lookup 𝘩𝑎𝑠𝘩 (gens !!! waiter.(waiter۰generation)).2 𝑘𝑒𝑦).

  #[local] Definition inv۰inner γ 𝘩𝑎𝑠𝘩 : iProp Σ :=
    ∃ gens cur resizing m frozen inited waiters,
    γ.(htbl۰name۰self).[state] ↦ generations۰state gens cur resizing ∗
    model₂ γ m ∗
    generations۰auth γ gens ∗
    current۰auth γ cur ∗
    frozen۰auth γ frozen ∗
    ( [∗ map] gi ↦ bucket ∈ frozen,
      frozen۰elem γ gi.1 gi.2 bucket
    ) ∗
    inited۰auth γ inited ∗
    waiters۰auth γ waiters ∗
    ( [∗ list] gen ∈ gens,
      array۰model gen.1 (DfracOwn 1) (cell۰to_val <$> gen.2)
    ) ∗
    ( [∗ list] gen ∈ gens,
      [∗ list] cell ∈ gen.2,
      entries۰model (cell۰entries cell)
    ) ∗
    ⌜inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters⌝ ∗
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ 𝘩𝑎𝑠𝘩 gens cur η waiter
    ).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %gens{}
      & %cur{}
      & %resizing{}
      & %m{}
      & %frozen{}
      & %inited{}
      & %waiters{}
      & >Hself_state
      & >Hmodel₂
      & >Hgens_auth
      & >Hcurrent_auth
      & >Hfrozen_auth
      & >#Hfrozen_elems
      & >Hinited_auth
      & >Hwaiters_auth
      & >Harrays
      & #Hentries_models
      & >%Hinv{}
      & Hwaiters
      )
    ".
  #[local] Definition inv' γ 𝘩𝑎𝑠𝘩 :=
    inv γ.(htbl۰name۰inv) (inv۰inner γ 𝘩𝑎𝑠𝘩).
  Please Definition htbl۰inv γ ι : iProp Σ :=
    ∃ hash 𝘩𝑎𝑠𝘩 equal sizes (sz : nat),
    ⌜ι = γ.(htbl۰name۰inv)⌝ ∗
    γ.(htbl۰name۰self).[hash] ↦□ hash ∗
    γ.(htbl۰name۰self).[equal] ↦□ equal ∗
    γ.(htbl۰name۰self).[sizes] ↦□ sizes ∗
    ⌜0 < sz⌝ ∗
    itype۰array itype۰int sz sizes ∗
    htbl۰valid key۰model hash 𝘩𝑎𝑠𝘩 equal ∗
    inv' γ 𝘩𝑎𝑠𝘩.
  #[local] Instance : CustomIpat "inv" :=
    " ( %hash
      & %𝘩𝑎𝑠𝘩
      & %equal
      & %sizes
      & %sz
      & ->
      & #Hself_hash
      & #Hself_equal
      & #Hself_sizes
      & %Hsz
      & #Hsizes
      & #(#Hvalid_functional & #Hvalid_hash & #Hvalid_equal)
      & #Hinv
      )
    ".

  Please Definition htbl۰model γ m : iProp Σ :=
    model₁ γ m.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  Zoo derive Timeless for htbl۰model.

  Zoo derive Persistent for htbl۰inv.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ m1 m2 :
    model₁ γ m1 -∗
    model₁ γ m2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ m1 m2 :
    model₁ γ m1 -∗
    model₂ γ m2 -∗
    ⌜m1 = m2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twinsｰagreeｰL with "Hmodel₁ Hmodel₂") as %?.
    iSteps.
  Qed.
  #[local] Lemma modelｰupdate {γ m1 m2} m :
    model₁ γ m1 -∗
    model₂ γ m2 ==∗
      model₁ γ m ∗
      model₂ γ m.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma generationsｰalloc gens :
    ⊢ |==>
      ∃ γ_generations,
      generations۰auth' γ_generations gens.
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma generations۰atｰget {γ gens} g gen :
    gens !! g = Some gen →
    generations۰auth γ gens ⊢
    generations۰at γ g gen.1 (length gen.2).
  Proof.
    intros Hlookup.
    apply mono_list۰atｰget.
    rewrite list_lookup_fmap Hlookup //.
  Qed.
  #[local] Lemma generations۰atｰvalid γ gens g buckets cap :
    generations۰auth γ gens -∗
    generations۰at γ g buckets cap -∗
      ∃ cells,
      ⌜gens !! g = Some (buckets, cells)⌝ ∗
      ⌜length cells = cap⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (mono_list۰atｰvalid with "Hauth Hat") as %(gen & [= -> ->] & Hlookup)%list_lookup_fmap_Some.
    destruct gen as (buckets, cells).
    iSteps.
  Qed.
  #[local] Lemma generationsｰupdate {γ gens} gen :
    generations۰auth γ gens ⊢ |==>
      generations۰auth γ (gens ++ [gen]) ∗
      generations۰at γ (length gens) gen.1 (length gen.2).
  Proof.
    iIntros "Hauth".
    iMod (mono_listｰupdateｰsnoc (gen.1, length gen.2) with "Hauth") as "Hauth".
    assert (generations۰phys gens ++ [(gen.1, length gen.2)] = generations۰phys (gens ++ [gen])) as ->.
    { rewrite /generations۰phys fmap_app //. }
    iDestruct (generations۰atｰget (length gens) gen with "Hauth") as "#Hat".
    { rewrite lookup_snoc_Some. naive. }
    iSteps.
  Qed.

  #[local] Lemma currentｰalloc :
    ⊢ |==>
      ∃ γ_current,
      current۰auth' γ_current 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
  #[local] Lemma current۰lbｰget γ cur :
    current۰auth γ cur ⊢
    current۰lb γ cur.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  #[local] Lemma current۰lbｰvalid γ cur g :
    current۰auth γ cur -∗
    current۰lb γ g -∗
    ⌜g ≤ cur⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.
  #[local] Lemma currentｰupdate {γ cur} cur' :
    cur ≤ cur' →
    current۰auth γ cur ⊢ |==>
    current۰auth γ cur'.
  Proof.
    apply auth_nat_maxｰupdate.
  Qed.

  #[local] Lemma frozenｰalloc :
    ⊢ |==>
      ∃ γ_frozen,
      frozen۰auth' γ_frozen ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma frozen۰elemｰvalid γ frozen g i entries :
    frozen۰auth γ frozen -∗
    frozen۰elem γ g i entries -∗
    ⌜frozen !! (g, i) = Some (entries)⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma frozenｰinsert {γ frozen} g i entries :
    frozen !! (g, i) = None →
    frozen۰auth γ frozen ⊢ |==>
      frozen۰auth γ (<[(g, i) := entries]> frozen) ∗
      frozen۰elem γ g i entries.
  Proof.
    iIntros "%Hlookup Hauth".
    iMod (ghost_map_insert with "Hauth") as "($ & Helem)"; first done.
    iApply (ghost_map_elem_persist with "Helem").
  Qed.

  #[local] Lemma initedｰalloc :
    ⊢ |==>
      ∃ γ_inited,
      inited۰auth' γ_inited ∅.
  Proof.
    apply mono_gsetｰalloc.
  Qed.
  #[local] Lemma inited۰elemｰvalid γ inited g j :
    inited۰auth γ inited -∗
    inited۰elem γ g j -∗
    ⌜(g, j) ∈ inited⌝.
  Proof.
    apply mono_gset۰elemｰvalid.
  Qed.
  #[local] Lemma initedｰinsert {γ inited} g j :
    inited۰auth γ inited ⊢ |==>
      inited۰auth γ ({[(g, j)]} ∪ inited) ∗
      inited۰elem γ g j.
  Proof.
    apply mono_gsetｰinsert'.
  Qed.

  #[local] Lemma waitersｰalloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters۰auth' γ_waiters ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma waiters۰elemｰvalid γ waiters η waiter :
    waiters۰auth γ waiters -∗
    waiters۰elem γ η waiter -∗
    ⌜waiters !! η = Some waiter⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma waitersｰinsert {γ waiters} η waiter :
    waiters !! η = None →
    waiters۰auth γ waiters ⊢ |==>
      waiters۰auth γ (<[η := waiter]> waiters) ∗
      waiters۰elem γ η waiter.
  Proof.
    iIntros "%Hlookup Hauth".
    iApply (ghost_map_insert with "Hauth"). done.
  Qed.
  #[local] Lemma waitersｰdelete γ waiters η waiter :
    waiters۰auth γ waiters -∗
    waiters۰elem γ η waiter ==∗
    waiters۰auth γ (delete η waiters).
  Proof.
    apply ghost_map_delete.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Pure invariant: updates. *)

  #[local] Lemma cells۰pendingｰmono 𝘩𝑎𝑠𝘩 cells1 cells2 cells' :
    length cells1 = length cells2 →
    ( ∀ k entries,
      cells1 !! k = Some (CellFrozen entries) →
      cells2 !! k = Some (CellFrozen entries)
    ) →
    cells۰pending 𝘩𝑎𝑠𝘩 cells1 cells' →
    cells۰pending 𝘩𝑎𝑠𝘩 cells2 cells'.
  Proof.
    intros Hlen Hfrozen [(Hlen' & Hpending) | (Hlen' & Hpending)].
    - left. split; first lia.
      intros j cell' Hlookup.
      destruct (Hpending j cell' Hlookup) as [-> | (entries & Hentries & ->)]; first by left.
      right. exists entries. rewrite -Hlen. split; last done.
      apply Hfrozen. done.
    - right. split; first lia.
      intros j cell' Hlookup.
      destruct (Hpending j cell' Hlookup) as [-> | (entries1 & entries2 & Hentries1 & Hentries2 & ->)]; first by left.
      right. exists entries1, entries2. split_and!; [apply Hfrozen.. | ]; done.
  Qed.

  #[local] Lemma inv۰pureｰlookup {𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters} :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
      ∃ gen,
      gens !! cur = Some gen.
  Proof.
    intros Hinv.
    apply lookup_lt_is_Some_2. rewrite (inv۰pure۰length Hinv). lia.
  Qed.

  #[local] Lemma inv۰pureｰfreeze 𝘩𝑎𝑠𝘩 gens cur m frozen inited waiters buckets cells i entries :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur true m frozen inited waiters →
    gens !! cur = Some (buckets, cells) →
    cells !! i = Some (CellActive entries) →
    inv۰pure 𝘩𝑎𝑠𝘩
      (<[cur := (buckets, <[i := CellFrozen entries]> cells)]> gens)
      cur true m
      (<[(cur, i) := entries]> frozen)
      inited waiters.
  Proof.
    intros [Hlength Hnodup Hpow2 Hcaps Hwf Hold Hcur Hpending Hmodel Hfrozen Hinited Hwaiters] Hlookup Hi.
    pose proof (lookup_lt_Some _ _ _ Hi).
    pose proof (lookup_lt_Some _ _ _ Hlookup).
    pose proof (Hgen := λ g gen, list_lookup_insert_Some gens cur (buckets, <[i := CellFrozen entries]> cells) g gen).
    split.
    - rewrite length_insert //.
    - rewrite list_fmap_insert /= list_insert_id //.
      rewrite list_lookup_fmap Hlookup //.
    - intros g gen [(<- & <- & _) | (_ & Hlookup')]%Hgen.
      + rewrite /= length_insert.
        apply (Hpow2 cur _ Hlookup).
      + apply (Hpow2 g _ Hlookup').
    - intros g gen gen' Hg Hg'.
      assert (
        ∀ g gen,
        <[cur := (buckets, <[i := CellFrozen entries]> cells)]> gens !! g = Some gen →
          ∃ gen0,
          gens !! g = Some gen0 ∧
          length gen.2 = length gen0.2
      ) as Hlen.
      { intros g0 gen0 [(<- & <- & _) | (_ & Hlookup')]%Hgen.
        - exists (buckets, cells). rewrite /= length_insert //.
        - exists gen0. done.
      }
      destruct (Hlen _ _ Hg) as (gen0 & Hg0 & ->).
      destruct (Hlen _ _ Hg') as (gen0' & Hg0' & ->).
      apply (Hcaps g); done.
    - intros g gen [(<- & <- & _) | (_ & Hlookup')]%Hgen.
      + apply cells۰wfｰinsert.
        * rewrite /=. apply (Hwf _ _ Hlookup _ _ Hi).
        * apply (Hwf _ _ Hlookup).
      + apply (Hwf _ _ Hlookup').
    - intros g gen i' cell Hg [(-> & _) | (_ & Hlookup')]%Hgen; first lia.
      apply (Hold g gen i' cell Hg Hlookup').
    - intros gen i' cell [(_ & <- & _) | (? & _)]%Hgen; last done.
      rewrite /= list_lookup_insert_Some.
      intros [(_ & <- & _) | (_ & Hlookup')]; first done.
      apply (Hcur _ _ _ Hlookup Hlookup').
    - intros gen gen' Hresizing [(_ & <- & _) | (? & _)]%Hgen; last done.
      intros [(? & _) | (_ & Hlookup')]%Hgen; first lia.
      apply (cells۰pendingｰmono _ cells); [rewrite length_insert // | | apply (Hpending _ _ Hresizing Hlookup Hlookup')].
      intros k entries' Hk.
      rewrite list_lookup_insert_ne //. congruence.
    - intros gen 𝑘𝑒𝑦 [(_ & <- & _) | (? & _)]%Hgen; last done.
      rewrite (Hmodel _ 𝑘𝑒𝑦 Hlookup) /= cells۰lookupｰinsert //.
      case_decide as Hidx; last done.
      rewrite /cells۰lookup Hidx (list_lookup_total_correct _ _ _ Hi) //.
    - intros g i' bucket.
      rewrite lookup_insert_Some Hfrozen.
      split.
      + intros [([= <- <-] & <-) | (Hne & gen & entries' & Hg & Hi' & <-)].
        * exists (buckets, <[i := CellFrozen entries]> cells), entries.
          rewrite list_lookup_insert_eq // /= list_lookup_insert_eq //.
        * destruct (decide (g = cur)) as [-> |].
          -- rewrite Hlookup in Hg. injection Hg as <-.
             exists (buckets, <[i := CellFrozen entries]> cells), entries'.
             rewrite list_lookup_insert_eq // /= list_lookup_insert_ne //.
             intros ->. congruence.
          -- exists gen, entries'. rewrite list_lookup_insert_ne //.
      + intros (gen & entries' & [(<- & <- & _) | (Hne & Hg)]%Hgen & Hi' & <-).
        * rewrite /= list_lookup_insert_Some in Hi'.
          destruct Hi' as [(<- & [= <-] & _) | (Hne & Hi')]; first by left.
          right. split; first congruence.
          exists (buckets, cells), entries'. done.
        * right. split; first congruence.
          exists gen, entries'. done.
    - intros g j HI.
      destruct (Hinited g j HI) as (gen & cell & Hg & Hj & Hcell).
      destruct (decide (g = cur)) as [-> |].
      + rewrite Hlookup in Hg. injection Hg as <-.
        exists (buckets, <[i := CellFrozen entries]> cells), (if decide (j = i) then CellFrozen entries else cell).
        rewrite list_lookup_insert_eq //.
        split; first done.
        rewrite /= list_lookup_insert_Some.
        case_decide as Hji.
        * subst. split; last done.
          left. split_and!; [done | done | eapply lookup_lt_Some; done].
        * split; last done.
          right. done.
      + exists gen, cell. rewrite list_lookup_insert_ne //.
    - done.
  Qed.

  #[local] Lemma inv۰pureｰupdate 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters buckets cells i entries entries' m' :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    gens !! cur = Some (buckets, cells) →
    cells !! i = Some (CellActive entries) →
    entries۰wf 𝘩𝑎𝑠𝘩 (length cells) i entries' →
    ( ∀ 𝑘𝑒𝑦,
      m' !! 𝑘𝑒𝑦 =
        if decide (entries۰index 𝘩𝑎𝑠𝘩 (length cells) 𝑘𝑒𝑦 = i) then
          entries۰lookup 𝑘𝑒𝑦 entries'
        else
          m !! 𝑘𝑒𝑦
    ) →
    inv۰pure 𝘩𝑎𝑠𝘩
      (<[cur := (buckets, <[i := CellActive entries']> cells)]> gens)
      cur resizing m' frozen inited waiters.
  Proof.
    intros [Hlength Hnodup Hpow2 Hcaps Hwf Hold Hcur Hpending Hmodel Hfrozen Hinited Hwaiters] Hlookup Hi Hentries' Hm'.
    pose proof (lookup_lt_Some _ _ _ Hi).
    pose proof (lookup_lt_Some _ _ _ Hlookup).
    pose proof (Hgen := λ g gen, list_lookup_insert_Some gens cur (buckets, <[i := CellActive entries']> cells) g gen).
    split.
    - rewrite length_insert //.
    - rewrite list_fmap_insert /= list_insert_id //.
      rewrite list_lookup_fmap Hlookup //.
    - intros g gen [(<- & <- & _) | (_ & Hlookup')]%Hgen.
      + rewrite /= length_insert.
        apply (Hpow2 cur _ Hlookup).
      + apply (Hpow2 g _ Hlookup').
    - intros g gen gen' Hg Hg'.
      assert (
        ∀ g gen,
        <[cur := (buckets, <[i := CellActive entries']> cells)]> gens !! g = Some gen →
          ∃ gen0,
          gens !! g = Some gen0 ∧
          length gen.2 = length gen0.2
      ) as Hlen.
      { intros g0 gen0 [(<- & <- & _) | (_ & Hlookup')]%Hgen.
        - exists (buckets, cells). rewrite /= length_insert //.
        - exists gen0. done.
      }
      destruct (Hlen _ _ Hg) as (gen0 & Hg0 & ->).
      destruct (Hlen _ _ Hg') as (gen0' & Hg0' & ->).
      apply (Hcaps g); done.
    - intros g gen [(<- & <- & _) | (_ & Hlookup')]%Hgen.
      + apply cells۰wfｰinsert; first done.
        apply (Hwf _ _ Hlookup).
      + apply (Hwf _ _ Hlookup').
    - intros g gen i' cell Hg [(-> & _) | (_ & Hlookup')]%Hgen; first lia.
      apply (Hold g gen i' cell Hg Hlookup').
    - intros gen i' cell [(_ & <- & _) | (? & _)]%Hgen; last done.
      rewrite /= list_lookup_insert_Some.
      intros [(_ & <- & _) | (_ & Hlookup')].
      + destruct resizing; [done | by eexists].
      + apply (Hcur _ _ _ Hlookup Hlookup').
    - intros gen gen' Hresizing [(_ & <- & _) | (? & _)]%Hgen; last done.
      intros [(? & _) | (_ & Hlookup')]%Hgen; first lia.
      apply (cells۰pendingｰmono _ cells); [rewrite length_insert // | | apply (Hpending _ _ Hresizing Hlookup Hlookup')].
      intros k entries'' Hk.
      rewrite list_lookup_insert_ne //. congruence.
    - intros gen 𝑘𝑒𝑦 [(_ & <- & _) | (? & _)]%Hgen; last done.
      rewrite Hm' /= cells۰lookupｰinsert //.
      case_decide; first done.
      apply (Hmodel _ _ Hlookup).
    - intros g i' bucket.
      rewrite Hfrozen.
      split.
      + intros (gen & entries'' & Hg & Hi' & <-).
        destruct (decide (g = cur)) as [-> |].
        * rewrite Hlookup in Hg. injection Hg as <-.
          exists (buckets, <[i := CellActive entries']> cells), entries''.
          rewrite list_lookup_insert_eq // /= list_lookup_insert_ne //.
          intros ->. simpl in Hi'. congruence.
        * exists gen, entries''. rewrite list_lookup_insert_ne //.
      + intros (gen & entries'' & [(<- & <- & _) | (Hne & Hg)]%Hgen & Hi' & <-).
        * rewrite /= list_lookup_insert_Some in Hi'.
          destruct Hi' as [(<- & [=] & _) | (Hne & Hi')].
          exists (buckets, cells), entries''. done.
        * exists gen, entries''. done.
    - intros g j HI.
      destruct (Hinited g j HI) as (gen & cell & Hg & Hj & Hcell).
      destruct (decide (g = cur)) as [-> |].
      + rewrite Hlookup in Hg. injection Hg as <-.
        exists (buckets, <[i := CellActive entries']> cells), (if decide (j = i) then CellActive entries' else cell).
        rewrite list_lookup_insert_eq //.
        split; first done.
        rewrite /= list_lookup_insert_Some.
        case_decide as Hji.
        * subst. split; last done.
          left. split_and!; [done | done | eapply lookup_lt_Some; done].
        * split; last done.
          right. done.
      + exists gen, cell. rewrite list_lookup_insert_ne //.
    - done.
  Qed.

  #[local] Lemma inv۰pureｰinit 𝘩𝑎𝑠𝘩 gens cur m frozen inited waiters buckets cells buckets' cells' j entries' :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur true m frozen inited waiters →
    gens !! cur = Some (buckets, cells) →
    gens !! ˖cur = Some (buckets', cells') →
    cells' !! j = Some CellInit →
    cells۰pending 𝘩𝑎𝑠𝘩 cells (<[j := CellActive entries']> cells') →
    inv۰pure 𝘩𝑎𝑠𝘩
      (<[˖cur := (buckets', <[j := CellActive entries']> cells')]> gens)
      cur true m frozen
      ({[(˖cur, j)]} ∪ inited)
      waiters.
  Proof.
    intros [Hlength Hnodup Hpow2 Hcaps Hwf Hold Hcur Hpending Hmodel Hfrozen Hinited Hwaiters] Hlookup Hlookup' Hj Hpending'.
    pose proof (lookup_lt_Some _ _ _ Hj).
    pose proof (lookup_lt_Some _ _ _ Hlookup').
    pose proof (Hgen := λ g gen, list_lookup_insert_Some gens ˖cur (buckets', <[j := CellActive entries']> cells') g gen).
    assert (
      ∀ g gen,
      <[˖cur := (buckets', <[j := CellActive entries']> cells')]> gens !! g = Some gen →
        ∃ gen0,
        gens !! g = Some gen0 ∧
        length gen.2 = length gen0.2
    ) as Hlen.
    { intros g0 gen0 [(<- & <- & _) | (_ & Hlookup'')]%Hgen.
      - exists (buckets', cells'). rewrite /= length_insert //.
      - exists gen0. done.
    }
    split.
    - rewrite length_insert //.
    - rewrite list_fmap_insert /= list_insert_id //.
      rewrite list_lookup_fmap Hlookup' //.
    - intros g gen (gen0 & Hg0 & ->)%Hlen. apply (Hpow2 _ _ Hg0).
    - intros g gen gen' (gen0 & Hg0 & ->)%Hlen (gen0' & Hg0' & ->)%Hlen.
      apply (Hcaps g); done.
    - intros g gen [(<- & <- & _) | (_ & Hlookup'')]%Hgen.
      + apply (cells۰pendingｰwf _ cells); last done.
        * apply (Hpow2 _ _ Hlookup).
        * rewrite length_insert. apply (Hpow2 _ _ Hlookup').
        * apply (Hwf _ _ Hlookup).
      + apply (Hwf _ _ Hlookup'').
    - intros g gen i' cell Hg [(? & _) | (_ & Hlookup'')]%Hgen; first lia.
      apply (Hold g gen i' cell Hg Hlookup'').
    - intros gen i' cell [(? & _) | (_ & Hlookup'')]%Hgen; first lia.
      apply (Hcur _ _ _ Hlookup'').
    - intros gen gen' _ [(? & _) | (_ & Hlookup'')]%Hgen; first lia.
      rewrite Hlookup in Hlookup''. injection Hlookup'' as <-.
      intros [(_ & <- & _) | (? & _)]%Hgen; last done.
      done.
    - intros gen 𝑘𝑒𝑦 [(? & _) | (_ & Hlookup'')]%Hgen; first lia.
      apply (Hmodel _ _ Hlookup'').
    - intros g i' bucket.
      rewrite Hfrozen.
      split.
      + intros (gen & entries'' & Hg & Hi' & <-).
        destruct (decide (g = ˖cur)) as [-> |].
        * rewrite Hlookup' in Hg. injection Hg as <-.
          exists (buckets', <[j := CellActive entries']> cells'), entries''.
          rewrite list_lookup_insert_eq // /= list_lookup_insert_ne //.
          intros ->. simpl in Hi'. congruence.
        * exists gen, entries''. rewrite list_lookup_insert_ne //.
      + intros (gen & entries'' & [(<- & <- & _) | (Hne & Hg)]%Hgen & Hi' & <-).
        * rewrite /= list_lookup_insert_Some in Hi'.
          destruct Hi' as [(<- & [=] & _) | (Hne & Hi')].
          exists (buckets', cells'), entries''. done.
        * exists gen, entries''. done.
    - intros g j' [[= -> ->]%elem_of_singleton | HI]%elem_of_union.
      + exists (buckets', <[j := CellActive entries']> cells'), (CellActive entries').
        rewrite list_lookup_insert_eq // /= list_lookup_insert_eq //.
      + destruct (Hinited g j' HI) as (gen & cell & Hg & Hj' & Hcell).
        destruct (decide (g = ˖cur)) as [-> |].
        * rewrite Hlookup' in Hg. injection Hg as <-.
          exists (buckets', <[j := CellActive entries']> cells'), (if decide (j' = j) then CellActive entries' else cell).
          rewrite list_lookup_insert_eq //.
          split; first done.
          rewrite /= list_lookup_insert_Some.
          case_decide as Hji.
          -- subst. split; last done.
             left. split_and!; [done | done | eapply lookup_lt_Some; done].
          -- split; last done.
             right. done.
        * exists gen, cell. rewrite list_lookup_insert_ne //.
    - done.
  Qed.

  #[local] Lemma inv۰pureｰinited {𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters g j gen cell} :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    gens !! g = Some gen →
    gen.2 !! j = Some cell →
    cell ≠ CellInit →
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen ({[(g, j)]} ∪ inited) waiters.
  Proof.
    intros [Hlength Hnodup Hpow2 Hcaps Hwf Hold Hcur Hpending Hmodel Hfrozen Hinited Hwaiters] Hg Hj Hcell.
    split; try done.
    intros g' j' [[= -> ->]%elem_of_singleton | HI]%elem_of_union.
    - exists gen, cell. done.
    - apply Hinited. done.
  Qed.

  #[local] Lemma inv۰pureｰresize 𝘩𝑎𝑠𝘩 gens cur m frozen inited waiters buckets cells buckets' cap' :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur false m frozen inited waiters →
    gens !! cur = Some (buckets, cells) →
    buckets' ∉ gens.*1 →
    is_pow2 cap' →
    cap' = 2 * length cells ∨ length cells = 2 * cap' →
    inv۰pure 𝘩𝑎𝑠𝘩 (gens ++ [(buckets', replicate cap' CellInit)]) cur true m frozen inited waiters.
  Proof.
    intros [Hlength Hnodup Hpow2 Hcaps Hwf Hold Hcur Hpending Hmodel Hfrozen Hinited Hwaiters] Hlookup Hbuckets' Hcap' Hrel.
    simpl in Hlength.
    pose proof (Hgen := λ g gen, lookup_snoc_Some (buckets', replicate cap' CellInit) gens g gen).
    split.
    - rewrite length_app /=. lia.
    - rewrite fmap_app NoDup_app. split_and!; [done | | apply NoDup_singleton].
      intros b Hb ->%list_elem_of_singleton. done.
    - intros g gen [(_ & Hg) | (_ & <-)]%Hgen.
      + apply (Hpow2 _ _ Hg).
      + rewrite /= length_replicate //.
    - intros g gen gen' [(_ & Hg) | (? & <-)]%Hgen [(_ & Hg') | (Heq & <-)]%Hgen.
      + apply (Hcaps g); done.
      + assert (g = cur) as -> by lia.
        rewrite Hlookup in Hg. injection Hg as <-.
        rewrite /= length_replicate. lia.
      + apply lookup_lt_Some in Hg'. lia.
      + lia.
    - intros g gen [(_ & Hg) | (_ & <-)]%Hgen.
      + apply (Hwf _ _ Hg).
      + intros i cell (-> & _)%lookup_replicate.
        split; [apply Forall_nil | apply NoDup_nil]; done.
    - intros g gen i cell Hg [(_ & Hg') | (? & _)]%Hgen; last lia.
      apply (Hold g gen i cell Hg Hg').
    - intros gen i cell [(_ & Hg) | (? & _)]%Hgen Hi; last lia.
      destruct (Hcur _ _ _ Hg Hi) as (entries & ->). done.
    - intros gen gen' _ [(_ & Hg) | (? & _)]%Hgen; last lia.
      rewrite Hlookup in Hg. injection Hg as <-.
      intros [(? & _) | (_ & <-)]%Hgen; first lia.
      rewrite /cells۰pending /= length_replicate.
      destruct Hrel as [Hrel | Hrel]; [left | right]; (split; first lia);
        intros j cell' (-> & _)%lookup_replicate; left; done.
    - intros gen 𝑘𝑒𝑦 [(_ & Hg) | (? & _)]%Hgen; last lia.
      apply (Hmodel _ _ Hg).
    - intros g i bucket.
      rewrite Hfrozen.
      split.
      + intros (gen & entries & Hg & Hi & <-).
        exists gen, entries. split_and!; try done.
        apply lookup_app_l_Some. done.
      + intros (gen & entries & [(_ & Hg) | (_ & <-)]%Hgen & Hi & <-).
        * exists gen, entries. done.
        * apply lookup_replicate in Hi as (? & _). done.
    - intros g j HI.
      destruct (Hinited g j HI) as (gen & cell & Hg & Hj & Hcell).
      exists gen, cell. split_and!; try done.
      apply lookup_app_l_Some. done.
    - done.
  Qed.

  #[local] Lemma inv۰pureｰinstall {𝘩𝑎𝑠𝘩 gens cur m frozen inited waiters buckets cells buckets' cells'} :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur true m frozen inited waiters →
    gens !! cur = Some (buckets, cells) →
    gens !! ˖cur = Some (buckets', cells') →
    ( ∀ j cell',
      cells' !! j = Some cell' →
      cell' ≠ CellInit
    ) →
      inv۰pure 𝘩𝑎𝑠𝘩 gens ˖cur false m frozen inited waiters ∧
      ( ∀ 𝑘𝑒𝑦,
        cells۰lookup 𝘩𝑎𝑠𝘩 cells' 𝑘𝑒𝑦 = cells۰lookup 𝘩𝑎𝑠𝘩 cells 𝑘𝑒𝑦
      ).
  Proof.
    intros Hinv Hlookup Hlookup' Hinit.
    destruct Hinv as [Hlength Hnodup Hpow2 Hcaps Hwf Hold Hcur Hpending Hmodel Hfrozen Hinited Hwaiters].
    opose proof* (cells۰pendingｰinstall 𝘩𝑎𝑠𝘩 cells cells') as (Hfrozen' & Hactive' & Hlookups).
    { apply (Hpow2 _ _ Hlookup). }
    { apply (Hpow2 _ _ Hlookup'). }
    { apply (Hwf _ _ Hlookup). }
    { apply (Hpending _ _ ltac:(done) Hlookup Hlookup'). }
    { done. }
    split; last done.
    split; try done.
    - rewrite Hlength /=. lia.
    - intros g gen i cell Hg Hgen Hi.
      destruct (decide (g = cur)) as [-> |].
      + rewrite Hlookup in Hgen. injection Hgen as <-.
        apply (Hfrozen' _ _ Hi).
      + apply (Hold g gen i cell); [lia | done..].
    - intros gen i cell Hgen Hi.
      rewrite Hlookup' in Hgen. injection Hgen as <-.
      apply (Hactive' _ _ Hi).
    - intros gen 𝑘𝑒𝑦 Hgen.
      rewrite Hlookup' in Hgen. injection Hgen as <-.
      rewrite Hlookups. apply (Hmodel _ _ Hlookup).
    - intros η waiter Hwaiter.
      opose proof* Hwaiters; first done. lia.
  Qed.

  #[local] Lemma inv۰pureｰwaitersｰinsert 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters η waiter :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    waiter.(waiter۰generation) ≤ cur →
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited (<[η := waiter]> waiters).
  Proof.
    intros [] Hwaiter. split; try done.
    intros η' waiter' [(<- & <-) | (_ & Hwaiter')]%lookup_insert_Some; first done.
    naive.
  Qed.
  #[local] Lemma inv۰pureｰwaitersｰdelete 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters η :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited (delete η waiters).
  Proof.
    intros []. split; try done.
    intros η' waiter' (_ & Hwaiter')%lookup_delete_Some. naive.
  Qed.

  #[local] Lemma inv۰pureｰcreate 𝘩𝑎𝑠𝘩 buckets :
    inv۰pure 𝘩𝑎𝑠𝘩 [(buckets, replicate min_buckets (CellActive []))] 0 false ∅ ∅ ∅ ∅.
  Proof.
    pose proof (is_pow2ｰpos _ min_bucketsｰis_pow2).
    split.
    - done.
    - apply NoDup_singleton.
    - intros g gen (-> & <-)%list_lookup_singleton_Some.
      apply min_bucketsｰis_pow2.
    - intros g gen gen' _ (? & _)%list_lookup_singleton_Some. lia.
    - intros g gen (-> & <-)%list_lookup_singleton_Some i cell (-> & _)%lookup_replicate.
      split; [apply Forall_nil | apply NoDup_nil]; done.
    - intros. lia.
    - intros gen i cell (_ & <-)%list_lookup_singleton_Some (-> & _)%lookup_replicate.
      by eexists.
    - done.
    - intros gen 𝑘𝑒𝑦 (_ & <-)%list_lookup_singleton_Some.
      rewrite lookup_empty /cells۰lookup list_lookup_total_alt.
      cbn [snd].
      rewrite lookup_replicate_2; last done.
      rewrite length_replicate. apply entries۰indexｰlt. lia.
    - intros g i bucket. rewrite lookup_empty. split; first done.
      intros (gen & entries & (_ & <-)%list_lookup_singleton_Some & (? & _)%lookup_replicate & _).
      done.
    - set_solver.
    - done.
  Qed.

  (* Knowledge of a generation. *)
  #[local] Definition gen۰witness γ g buckets cap : iProp Σ :=
    generations۰at γ g buckets cap ∗
    array۰inv buckets cap ∗
    ⌜is_pow2 cap⌝.
  #[local] Instance : CustomIpat "gen۰witness" :=
    " ( #Hgens_at{_{}}
      & #Harray_inv{_{}}
      & %Hpow2{_{}}
      )
    ".

  (* Knowledge of a state value: its generation, its array and, if it is
     resizing, the next generation. *)
  #[local] Definition state۰witness γ s g buckets cap o : iProp Σ :=
    ⌜s = state۰to_val buckets cap o⌝ ∗
    current۰lb γ g ∗
    gen۰witness γ g buckets cap ∗
    match o with
    | None =>
        True
    | Some (buckets', cap') =>
        gen۰witness γ ˖g buckets' cap' ∗
        ⌜(cap' = 2 * cap ∨ cap = 2 * cap')%nat⌝
    end.
  #[local] Instance : CustomIpat "state۰witness" :=
    " ( ->
      & #Hcurrent_lb
      & (:gen۰witness)
      & Ho
      )
    ".

  (* ------------------------------------------------------------------------ *)
  (* Invariant helpers. *)

  #[local] Lemma inv۰pureｰle {𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters g gen} :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    gens !! ˖g = Some gen →
    g ≤ cur.
  Proof.
    intros Hinv Hg%lookup_lt_Some.
    rewrite (inv۰pure۰length Hinv) in Hg.
    destruct resizing; simpl in Hg; lia.
  Qed.

  #[local] Lemma inv۰pureｰnot_init {𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters g gen i cell} :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    gens !! g = Some gen →
    g ≤ cur →
    gen.2 !! i = Some cell →
    cell ≠ CellInit.
  Proof.
    intros Hinv Hg Hgcur Hi.
    destruct (decide (g = cur)) as [-> |].
    - opose proof* (inv۰pure۰cur Hinv) as Hcell; [done.. |].
      destruct resizing; first done.
      destruct Hcell as (entries & ->). done.
    - opose proof* (inv۰pure۰old Hinv g) as (entries & ->); [lia | done.. |].
      done.
  Qed.

  #[local] Lemma entries۰modelｰlookup {gens g gen i cell} :
    gens !! g = Some gen →
    gen.2 !! i = Some cell →
    ( [∗ list] gen ∈ gens,
      [∗ list] cell ∈ gen.2,
      entries۰model (cell۰entries cell)
    ) ⊢
    entries۰model (cell۰entries cell).
  Proof.
    iIntros "%Hg %Hi Hentries_models".
    iDestruct (big_sepL_lookup with "Hentries_models") as "Hentries_models"; first done.
    iApply (big_sepL_lookup with "Hentries_models"). done.
  Qed.

  #[local] Lemma entries۰modelｰagree entries1 entries2 :
    entries۰bucket entries1 = entries۰bucket entries2 →
    htbl۰valid۰functional key۰model -∗
    entries۰model entries1 -∗
    entries۰model entries2 -∗
    ⌜entries1 = entries2⌝.
  Proof.
    iIntros "%Heq #Hfunctional Hentries1 Hentries2".
    iInduction entries1 as [| [key1 v1 k1] entries1] "IH" forall (entries2 Heq);
      destruct entries2 as [| [key2 v2 k2] entries2]; try done.
    simpl in Heq. injection Heq as -> -> Heq.
    rewrite /entries۰model !big_sepL_cons /=.
    iDestruct "Hentries1" as "(Hkey1 & Hentries1)".
    iDestruct "Hentries2" as "(Hkey2 & Hentries2)".
    iDestruct ("Hfunctional" with "Hkey1 Hkey2") as %->.
    iDestruct ("IH" with "[//] Hentries1 Hentries2") as %<-.
    iSteps.
  Qed.

  #[local] Lemma state۰witnessｰget γ 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    generations۰auth γ gens -∗
    current۰auth γ cur -∗
    ( [∗ list] gen ∈ gens,
      array۰model gen.1 (DfracOwn 1) (cell۰to_val <$> gen.2)
    ) -∗
      generations۰auth γ gens ∗
      current۰auth γ cur ∗
      ( [∗ list] gen ∈ gens,
        array۰model gen.1 (DfracOwn 1) (cell۰to_val <$> gen.2)
      ) ∗
      ∃ buckets cap o,
      state۰witness γ (generations۰state gens cur resizing) cur buckets cap o ∗
      ⌜if resizing then is_Some o else o = None⌝.
  Proof.
    iIntros "%Hinv Hgens_auth Hcurrent_auth Harrays".
    destruct (inv۰pureｰlookup Hinv) as ((buckets, cells) & Hlookup).
    iDestruct (generations۰atｰget with "Hgens_auth") as "#Hgens_at"; first done.
    iDestruct (current۰lbｰget with "Hcurrent_auth") as "#Hcurrent_lb".
    iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & Harrays)"; first done.
    iDestruct (array۰modelｰtoｰinv with "Hmodel") as "#Harray_inv".
    iDestruct ("Harrays" with "Hmodel") as "Harrays".
    rewrite length_fmap.
    pose proof (inv۰pure۰pow2 Hinv _ _ Hlookup) as Hpow2.
    destruct resizing.
    - assert (is_Some (gens !! ˖cur)) as ((buckets', cells') & Hlookup').
      { apply lookup_lt_is_Some_2. rewrite (inv۰pure۰length Hinv) /=. lia. }
      iDestruct (generations۰atｰget with "Hgens_auth") as "#Hgens_at'"; first done.
      iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel' & Harrays)"; first done.
      iDestruct (array۰modelｰtoｰinv with "Hmodel'") as "#Harray_inv'".
      iDestruct ("Harrays" with "Hmodel'") as "Harrays".
      rewrite length_fmap.
      pose proof (inv۰pure۰pow2 Hinv _ _ Hlookup') as Hpow2'.
      pose proof (inv۰pure۰caps Hinv _ _ _ Hlookup Hlookup') as Hcaps.
      iFrame "Hgens_auth Hcurrent_auth Harrays".
      iExists buckets, (length cells), (Some (buckets', length cells')).
      rewrite /generations۰state (list_lookup_total_correct _ _ _ Hlookup) (list_lookup_total_correct _ _ _ Hlookup').
      iFrameSteps.
    - iFrame "Hgens_auth Hcurrent_auth Harrays".
      iExists buckets, (length cells), None.
      rewrite /generations۰state (list_lookup_total_correct _ _ _ Hlookup).
      iFrameSteps.
  Qed.

  #[local] Lemma state۰witnessｰsimilar {γ 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters s} g buckets cap o :
    inv۰pure 𝘩𝑎𝑠𝘩 gens cur resizing m frozen inited waiters →
    generations۰state gens cur resizing ≈ s →
    generations۰auth γ gens -∗
    state۰witness γ s g buckets cap o -∗
      ⌜g = cur⌝ ∗
      ⌜if resizing then is_Some o else o = None⌝.
  Proof.
    iIntros "%Hinv %Hs Hgens_auth (:state۰witness)".
    iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hlookup & _).
    destruct (inv۰pureｰlookup Hinv) as ((buckets0, cells0) & Hlookup0).
    rewrite /generations۰state (list_lookup_total_correct _ _ _ Hlookup0) /= in Hs.
    apply state۰to_valｰsimilar in Hs as (Hbuckets & _ & Ho).
    iDestruct (array۰invｰsimilar _ _ buckets0 with "Harray_inv") as %<-; first done.
    iPureIntro. split.
    - apply (NoDup_lookup gens.*1 g cur buckets0).
      + apply (inv۰pure۰nodup Hinv).
      + rewrite list_lookup_fmap Hlookup //.
      + rewrite list_lookup_fmap Hlookup0 //.
    - destruct resizing, o; naive_solver.
  Qed.

  #[local] Lemma cell۰to_valｰsimilarｰbucket cell bucket :
    cell۰to_val cell ≈ bucket۰to_val bucket →
      ∃ entries,
      cell = CellActive entries ∧
      entries۰bucket entries = bucket.
  Proof.
    destruct cell as [| entries | entries].
    - destruct bucket as [| (key, v) bucket]; cbn; done.
    - intros Heq%bucket۰to_valｰsimilar. eexists. done.
    - destruct bucket as [| (key, v) bucket]; cbn; done.
  Qed.

  #[local] Lemma cell۰to_valｰsimilarｰInit cell :
    cell۰to_val cell ≈ §htbl٠bucket٠Init%V →
    cell = CellInit.
  Proof.
    destruct cell as [| entries | entries]; first done.
    - destruct entries as [| [key v 𝑘𝑒𝑦] entries]; cbn; done.
    - cbn. done.
  Qed.

  #[local] Lemma entries۰modelsｰinsert {gens g buckets cells i cell} cell' :
    gens !! g = Some (buckets, cells) →
    cells !! i = Some cell →
    ( [∗ list] gen ∈ gens,
      [∗ list] cell ∈ gen.2,
      entries۰model (cell۰entries cell)
    ) -∗
    entries۰model (cell۰entries cell') -∗
    [∗ list] gen ∈ <[g := (buckets, <[i := cell']> cells)]> gens,
      [∗ list] cell ∈ gen.2,
      entries۰model (cell۰entries cell).
  Proof.
    iIntros "%Hg %Hi Hentries_models Hcell'".
    iDestruct (big_sepL_insert_acc with "Hentries_models") as "(Hcells & Hentries_models)"; first done.
    iApply "Hentries_models".
    iDestruct (big_sepL_insert_acc with "Hcells") as "(_ & Hcells)"; first done.
    iApply ("Hcells" with "Hcell'").
  Qed.

  #[local] Lemma waiter۰modelsｰmono γ 𝘩𝑎𝑠𝘩 gens gens' cur waiters :
    ( ∀ g,
      g < cur →
      gens' !!! g = gens !!! g
    ) →
    ( ∀ η waiter,
      waiters !! η = Some waiter →
      waiter.(waiter۰generation) ≤ cur
    ) →
    ( [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ 𝘩𝑎𝑠𝘩 gens cur η waiter
    ) -∗
    [∗ map] η ↦ waiter ∈ waiters,
      waiter۰model γ 𝘩𝑎𝑠𝘩 gens' cur η waiter.
  Proof.
    iIntros "%Hgens %Hwaiters Hwaiters".
    iApply (big_sepM_impl with "Hwaiters").
    iIntros "!> %η %waiter %Hwaiter (%𝑘𝑒𝑦 & %Ψ & Hkey & Hη & H)".
    iExists 𝑘𝑒𝑦, Ψ. iFrame.
    case_decide; first done.
    rewrite Hgens //.
    opose proof* Hwaiters; first done. lia.
  Qed.

  #[local] Lemma generations۰physｰinsert {gens k buckets cells cells'} :
    gens !! k = Some (buckets, cells) →
    length cells' = length cells →
    generations۰phys (<[k := (buckets, cells')]> gens) = generations۰phys gens.
  Proof.
    intros Hk Hlen.
    rewrite /generations۰phys list_fmap_insert /= Hlen list_insert_id //.
    rewrite list_lookup_fmap Hk //.
  Qed.

  #[local] Lemma generations۰stateｰinsert {gens k buckets cells cells' cur resizing} :
    gens !! k = Some (buckets, cells) →
    length cells' = length cells →
    generations۰state (<[k := (buckets, cells')]> gens) cur resizing = generations۰state gens cur resizing.
  Proof.
    intros Hk Hlen.
    assert (
      ∀ g,
      (<[k := (buckets, cells')]> gens !!! g).1 = (gens !!! g).1
    ) as Hfst.
    { intros g. rewrite list_lookup_total_insert. case_decide as Hg; last done.
      destruct Hg as (<- & _). rewrite (list_lookup_total_correct _ _ _ Hk) //.
    }
    assert (
      ∀ g,
      length (<[k := (buckets, cells')]> gens !!! g).2 = length (gens !!! g).2
    ) as Hsnd.
    { intros g. rewrite list_lookup_total_insert. case_decide as Hg; last done.
      destruct Hg as (<- & _). rewrite (list_lookup_total_correct _ _ _ Hk) //.
    }
    rewrite /generations۰state !Hfst !Hsnd //.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Buckets. *)

  #[local] Definition node۰result node (o : option val) :=
    match o with
    | None =>
        node = §htbl٠bucket٠Nil%V
    | Some v =>
        ∃ key rest,
        node = ‘htbl٠bucket٠Cons[ key, v, rest ]%V
    end.

  #[local] Lemma htbl٠bucket٠assocｰspecｰbucket equal key 𝑘𝑒𝑦 entries :
    {{{
      htbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      entries۰model entries
    }}}
      htbl٠bucket٠assoc equal key (bucket۰to_val (entries۰bucket entries))
    {{{
      node
    , RET node;
      ⌜node۰result node (entries۰lookup 𝑘𝑒𝑦 entries)⌝
    }}}.
  Proof.
    iIntros "%Φ (#Hequal & #Hkey & #Hentries) HΦ".

    iInduction entries as [| [key' v 𝑘𝑒𝑦'] entries] "IH" forall (Φ).

    - wp۰rec.
      iSteps.

    - wp۰rec.
      rewrite /entries۰model big_sepL_cons.
      iDestruct "Hentries" as "(Hkey' & Hentries)".
      wp۰apply+ (wpｰwand with "(Hequal Hkey Hkey')") as (res) "->".
      rewrite /=. case_decide.
      + rewrite bool_decide_eq_true_2 //.
        iSteps.
      + rewrite bool_decide_eq_false_2 //.
        wp۰apply+ ("IH" with "Hentries HΦ").
  Qed.

  #[local] Lemma htbl٠bucket٠assocｰspec equal key 𝑘𝑒𝑦 cell :
    cell ≠ CellInit →
    {{{
      htbl۰valid۰equal key۰model equal ∗
      key۰model key 𝑘𝑒𝑦 ∗
      entries۰model (cell۰entries cell)
    }}}
      htbl٠bucket٠assoc equal key (cell۰to_val cell)
    {{{
      node
    , RET node;
      ⌜node۰result node (entries۰lookup 𝑘𝑒𝑦 (cell۰entries cell))⌝
    }}}.
  Proof.
    iIntros "%Hcell %Φ (#Hequal & #Hkey & #Hentries) HΦ".
    destruct cell as [| entries | entries]; first done; simpl.
    - wp۰apply (htbl٠bucket٠assocｰspecｰbucket with "[$Hequal $Hkey $Hentries] HΦ").
    - wp۰rec.
      wp۰apply+ (htbl٠bucket٠assocｰspecｰbucket with "[$Hequal $Hkey $Hentries] HΦ").
  Qed.

  (* [htbl٠bucket٠dissoc] removes the first binding whose key is equal to
     [key] according to [equal], which is called as [equal key key'] on keys
     of the bucket, as in [htbl٠bucket٠assoc]. *)
  #[local] Lemma htbl٠bucket٠dissocｰspec equal key 𝑘𝑒𝑦 bucket 𝑘𝑒𝑦𝑠 Φ :
    length 𝑘𝑒𝑦𝑠 = length bucket →
    htbl۰valid۰equal key۰model equal -∗
    □ key۰model key 𝑘𝑒𝑦 -∗
    □ ([∗ list] key'; 𝑘𝑒𝑦' ∈ bucket.*1; 𝑘𝑒𝑦𝑠, key۰model key' 𝑘𝑒𝑦') -∗
    ▷ Φ (
      option۰to_val (
        (λ '(i, _), bucket۰to_val (delete i bucket)) <$>
        list_find (λ 𝑘𝑒𝑦', 𝑘𝑒𝑦 = 𝑘𝑒𝑦') 𝑘𝑒𝑦𝑠
      )
    ) -∗
    WP htbl٠bucket٠dissoc equal key (bucket۰to_val bucket) {{ Φ }}.
  Proof.
    iIntros "%Hlen #Hequal #Hkey #Hbucket HΦ".
    iInduction bucket as [| (key', v) bucket] "IH" forall (𝑘𝑒𝑦𝑠 Hlen Φ).

    - destruct 𝑘𝑒𝑦𝑠; last done.
      wp۰rec.
      iSteps.

    - destruct 𝑘𝑒𝑦𝑠 as [| 𝑘𝑒𝑦' 𝑘𝑒𝑦𝑠]; first done.
      iEval (rewrite fmap_cons big_sepL2_cons) in "Hbucket".
      iDestruct "Hbucket" as "(Hkey' & Hbucket')".
      wp۰rec.
      wp۰apply+ (wpｰwand with "(Hequal Hkey Hkey')") as (res) "->".
      rewrite /=. case_decide.

      + rewrite bool_decide_eq_true_2 //.
        iSteps.

      + rewrite bool_decide_eq_false_2 //.
        wp۰apply+ ("IH" $! 𝑘𝑒𝑦𝑠 with "[] Hbucket'"); first auto with lia.
        destruct (list_find _ 𝑘𝑒𝑦𝑠) as [(i, 𝑘𝑒𝑦'') |] => /=.

        * iSteps.

        * iSteps.
  Qed.

  #[local] Lemma htbl٠bucket٠filterｰspec (P : entry Key → Prop) `{!∀ entry, Decision (P entry)} (pred : val) entries :
    {{{
      □ (
        ∀ key v 𝑘𝑒𝑦,
        ⌜Entry key v 𝑘𝑒𝑦 ∈ entries⌝ -∗
        WP pred key {{ res,
          ⌜res = #(bool_decide (P (Entry key v 𝑘𝑒𝑦)))⌝
        }}
      )
    }}}
      htbl٠bucket٠filter pred (bucket۰to_val (entries۰bucket entries))
    {{{
      RET bucket۰to_val (entries۰bucket (filter P entries));
      True
    }}}.
  Proof.
    iIntros "%Φ #Hpred HΦ".

    iInduction entries as [| [key v 𝑘𝑒𝑦] entries] "IH" forall (Φ).

    - wp۰rec.
      iSteps.

    - wp۰rec.
      iDestruct ("Hpred" $! key v 𝑘𝑒𝑦 with "[%]") as "Hpred'"; first set_solver.
      wp۰apply+ (wpｰwand with "Hpred'") as (res) "->".
      rewrite filter_cons.
      case_decide.
      + rewrite bool_decide_eq_true_2 //.
        wp۰apply+ ("IH" with "[]") as "_".
        { iIntros "!> %key' %v' %𝑘𝑒𝑦' %Hentry". iApply "Hpred". iPureIntro. set_solver. }
        iSteps.
      + rewrite bool_decide_eq_false_2 //.
        wp۰apply+ ("IH" with "[] HΦ").
        { iIntros "!> %key' %v' %𝑘𝑒𝑦' %Hentry". iApply "Hpred". iPureIntro. set_solver. }
  Qed.

  #[local] Lemma htbl٠bucket٠mergeｰspec entries1 entries2 :
    {{{
      True
    }}}
      htbl٠bucket٠merge (bucket۰to_val (entries۰bucket entries1)) (bucket۰to_val (entries۰bucket entries2))
    {{{
      RET bucket۰to_val (entries۰bucket (entries2 ++ entries1));
      True
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iInduction entries2 as [| [key v 𝑘𝑒𝑦] entries2] "IH" forall (Φ).

    - wp۰rec.
      iSteps.

    - wp۰rec.
      wp۰apply+ "IH".
      iSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [cas_init]. *)

  (* What a thread knows about the content of cell [j] of the next generation
     [˖g], after taking the corresponding source cells of generation [g]. *)
  #[local] Definition pending۰proof γ 𝘩𝑎𝑠𝘩 g (cap cap' : nat) j entries' : iProp Σ :=
    ( ⌜(cap' = 2 * cap)%nat⌝ ∗
      ∃ entries,
      frozen۰elem γ g (j `mod` cap) entries ∗
      ⌜entries' = split۰entries 𝘩𝑎𝑠𝘩 cap (bool_decide (cap ≤ j)) entries⌝
    ) ∨ (
      ⌜(cap = 2 * cap')%nat⌝ ∗
      ∃ entries1 entries2,
      frozen۰elem γ g j entries1 ∗
      frozen۰elem γ g (j + cap') entries2 ∗
      ⌜entries' = entries2 ++ entries1⌝
    ).

  #[local] Lemma htbl٠buckets٠cas_initｰspec γ 𝘩𝑎𝑠𝘩 g buckets cap buckets' cap' (j : nat) entries' :
    j < cap' →
    {{{
      inv' γ 𝘩𝑎𝑠𝘩 ∗
      gen۰witness γ g buckets cap ∗
      gen۰witness γ ˖g buckets' cap' ∗
      entries۰model entries' ∗
      pending۰proof γ 𝘩𝑎𝑠𝘩 g cap cap' j entries'
    }}}
      htbl٠buckets٠cas_init buckets' #j (bucket۰to_val (entries۰bucket entries'))
    {{{
      RET ();
      inited۰elem γ ˖g j
    }}}.
  Proof.
    iIntros "%Hj %Φ (#Hinv & (:gen۰witness) & (:gen۰witness =next) & #Hentries' & Hproof) HΦ".

    wp۰rec.

    awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Harray_inv_next") without "Hproof HΦ"; first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at_next") as %(cells' & Hgens1_lookup' & <-).
    iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens1_lookup'.
    iAaccIntro with "Hmodel".
    { iIntros "Hmodel !>".
      iDestruct ("Harrays" with "Hmodel") as "Harrays".
      iSplitL; last iSteps.
      iFrameSteps.
    }
    iIntros "%𝑣 (%Hlookup & Hmodel)".
    iDestruct ("Harrays" with "Hmodel") as "Harrays".
    rewrite Nat2Z.id in Hlookup.
    apply list_lookup_fmap_Some in Hlookup as (cell & -> & Hcells'_lookup).
    simpl in Hcells'_lookup.
    destruct (cellｰinitｰcases cell) as [-> | Hcell].

    - iSplitL. { iFrameSteps. }
      iIntros "!> _ (Hproof & HΦ) {Hfrozen_elems Hentries_models}".

      awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Harray_inv_next") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at_next") as %(cells2' & Hgens2_lookup' & Hcells2').
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells2 & Hgens2_lookup & Hcells2).
      iDestruct (big_sepL_insert_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens2_lookup'.
      iAaccIntro with "Hmodel".
      { iIntros "Hmodel !>".
        iDestruct ("Harrays" $! (buckets', cells2') with "Hmodel") as "Harrays".
        rewrite list_insert_id //.
        iFrame "Hproof". iFrameSteps.
      }
      iIntros "%b %𝑣 (%Hlookup & %Hcas & Hmodel)".
      rewrite Nat2Z.id in Hlookup.
      apply list_lookup_fmap_Some in Hlookup as (cell2 & -> & Hcells2'_lookup).
      simpl in Hcells2'_lookup.
      destruct b.

      + apply cell۰to_valｰsimilarｰInit in Hcas as ->.
        assert (g = cur2 ∧ resizing2 = true) as (-> & ->).
        { destruct (decide (˖g ≤ cur2)).
          - exfalso. by eapply (inv۰pureｰnot_init Hinv2 Hgens2_lookup').
          - pose proof (lookup_lt_Some _ _ _ Hgens2_lookup') as Hlt.
            rewrite (inv۰pure۰length Hinv2) in Hlt.
            destruct resizing2; simpl in Hlt; [split; [lia | done] | lia].
        }
        pose proof (inv۰pure۰pending Hinv2 _ _ ltac:(done) Hgens2_lookup Hgens2_lookup') as Hpending.
        simpl in Hpending.
        pose proof (is_pow2ｰpos _ Hpow2).
        iAssert ⌜cells۰pending 𝘩𝑎𝑠𝘩 cells2 (<[j := CellActive entries']> cells2')⌝%I as %Hpending'.
        { iDestruct "Hproof" as "[(%Hcap & %entries & Hfrozen_elem & ->) | (%Hcap & %entries1 & %entries2 & Hfrozen_elem1 & Hfrozen_elem2 & ->)]".
          - iDestruct (frozen۰elemｰvalid with "Hfrozen_auth Hfrozen_elem") as %Hfrozen.
            apply (inv۰pure۰frozen Hinv2) in Hfrozen as (gen & entries0 & Hgen & Hentries0 & ->).
            rewrite Hgens2_lookup in Hgen. injection Hgen as <-.
            iPureIntro. apply cells۰pendingｰinsert; first done.
            + intros _. right. exists entries. rewrite Hcells2. done.
            + intros Hlen. lia.
          - iDestruct (frozen۰elemｰvalid with "Hfrozen_auth Hfrozen_elem1") as %Hfrozen1.
            iDestruct (frozen۰elemｰvalid with "Hfrozen_auth Hfrozen_elem2") as %Hfrozen2.
            apply (inv۰pure۰frozen Hinv2) in Hfrozen1 as (gen1 & entries1' & Hgen1 & Hentries1 & ->).
            apply (inv۰pure۰frozen Hinv2) in Hfrozen2 as (gen2 & entries2' & Hgen2 & Hentries2 & ->).
            rewrite Hgens2_lookup in Hgen1. injection Hgen1 as <-.
            rewrite Hgens2_lookup in Hgen2. injection Hgen2 as <-.
            iPureIntro. apply cells۰pendingｰinsert; first done.
            + intros Hlen. lia.
            + intros _. right. exists entries1, entries2. rewrite Hcells2'. done.
        }
        iMod (initedｰinsert ˖cur2 j with "Hinited_auth") as "(Hinited_auth & #Hinited_elem)".
        iDestruct ("Harrays" $! (buckets', <[j := CellActive entries']> cells2') with "[Hmodel]") as "Harrays".
        { iEval (rewrite Nat2Z.id) in "Hmodel". rewrite /= list_fmap_insert //. }
        iSplitL.
        { iIntros "!> !>".
          iExists (<[˖cur2 := (buckets', <[j := CellActive entries']> cells2')]> gens2), cur2, true, m2, frozen2, ({[(˖cur2, j)]} ∪ inited2), waiters2.
          rewrite (generations۰stateｰinsert Hgens2_lookup'); first rewrite length_insert //.
          rewrite /generations۰auth /generations۰auth' (generations۰physｰinsert Hgens2_lookup'); first rewrite length_insert //.
          iFrame "∗#".
          iSplitR.
          { iApply (entries۰modelsｰinsert (CellActive entries') Hgens2_lookup' Hcells2'_lookup with "Hentries_models Hentries'"). }
          iSplitR.
          { iPureIntro. eapply inv۰pureｰinit; done. }
          iApply (waiter۰modelsｰmono with "Hwaiters").
          - intros g' Hg'. rewrite list_lookup_total_insert_ne //. lia.
          - apply (inv۰pure۰waiters Hinv2).
        }
        iIntros "!> _ HΦ".

        wp۰pures.
        iApply "HΦ". done.

      + assert (cell2 ≠ CellInit) as Hcell2.
        { intros ->. cbn in Hcas. done. }
        iMod (initedｰinsert ˖g j with "Hinited_auth") as "(Hinited_auth & #Hinited_elem)".
        pose proof (inv۰pureｰinited Hinv2 Hgens2_lookup' Hcells2'_lookup Hcell2) as Hinv2'.
        iDestruct ("Harrays" $! (buckets', cells2') with "Hmodel") as "Harrays".
        rewrite list_insert_id //.
        iSplitL. { iFrameSteps. }
        iIntros "!> _ HΦ".

        wp۰pures.
        iApply "HΦ". done.

    - iMod (initedｰinsert ˖g j with "Hinited_auth") as "(Hinited_auth & #Hinited_elem)".
      pose proof (inv۰pureｰinited Hinv1 Hgens1_lookup' Hcells'_lookup Hcell) as Hinv1'.
      iSplitL. { iFrameSteps. }
      iIntros "!> _ (Hproof & HΦ)".

      wp۰equal as _ | Hsuc.
      + wp۰pures.
        iApply "HΦ". done.
      + apply cell۰to_valｰsimilarｰInit in Hsuc. done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [take]. *)

  #[local] Lemma htbl٠buckets٠take₁ｰspec γ 𝘩𝑎𝑠𝘩 g buckets cap buckets' cap' (i : nat) backoff :
    i < cap →
    {{{
      inv' γ 𝘩𝑎𝑠𝘩 ∗
      gen۰witness γ g buckets cap ∗
      generations۰at γ ˖g buckets' cap' ∗
      backoff۰model backoff
    }}}
      htbl٠buckets٠take₁ buckets #i backoff
    {{{
      entries
    , RET bucket۰to_val (entries۰bucket entries);
      frozen۰elem γ g i entries ∗
      entries۰model entries ∗
      ⌜entries۰wf 𝘩𝑎𝑠𝘩 cap i entries⌝
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Hinv & (:gen۰witness) & #Hgens_at' & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec.

    awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Harray_inv") without "Hbackoff HΦ"; first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hgens1_lookup & <-).
    iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at'") as %(cells' & Hgens1_lookup' & _).
    iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens1_lookup.
    iAaccIntro with "Hmodel".
    { iIntros "Hmodel !>".
      iDestruct ("Harrays" with "Hmodel") as "Harrays".
      iSplitL; last iSteps.
      iFrameSteps.
    }
    iIntros "%𝑣 (%Hlookup & Hmodel)".
    iDestruct ("Harrays" with "Hmodel") as "Harrays".
    rewrite Nat2Z.id in Hlookup.
    apply list_lookup_fmap_Some in Hlookup as (cell & -> & Hcells_lookup).
    simpl in Hcells_lookup.
    pose proof (inv۰pureｰle Hinv1 Hgens1_lookup') as Hg.
    destruct cell as [| entries | entries].

    - exfalso. by eapply (inv۰pureｰnot_init Hinv1 Hgens1_lookup Hg Hcells_lookup).

    - iSplitL. { iFrameSteps. }
      iIntros "!> _ (Hbackoff & HΦ) {Hfrozen_elems Hentries_models}".

      awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Harray_inv") without "Hbackoff HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells2 & Hgens2_lookup & Hcells2).
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at'") as %(cells2' & Hgens2_lookup' & _).
      iDestruct (big_sepL_insert_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens2_lookup.
      iAaccIntro with "Hmodel".
      { iIntros "Hmodel !>".
        iDestruct ("Harrays" $! (buckets, cells2) with "Hmodel") as "Harrays".
        rewrite list_insert_id //.
        iSplitL; last iSteps.
        iFrameSteps.
      }
      iIntros "%b %𝑣 (%Hlookup & %Hcas & Hmodel)".
      rewrite Nat2Z.id in Hlookup.
      apply list_lookup_fmap_Some in Hlookup as (cell & -> & Hcells2_lookup).
      simpl in Hcells2_lookup.
      destruct b.

      + apply cell۰to_valｰsimilarｰbucket in Hcas as (entries2 & -> & Hentries2).
        pose proof (inv۰pureｰle Hinv2 Hgens2_lookup') as Hg2.
        assert (g = cur2) as ->.
        { destruct (decide (g = cur2)); first done.
          opose proof* (inv۰pure۰old Hinv2 g) as (? & ?); [lia | done | done | done].
        }
        assert (resizing2 = true) as ->.
        { apply lookup_lt_Some in Hgens2_lookup'.
          rewrite (inv۰pure۰length Hinv2) in Hgens2_lookup'.
          destruct resizing2; simpl in *; [done | lia].
        }
        assert (frozen2 !! (cur2, i) = None) as HF.
        { apply eq_None_not_Some. intros (bucket & Hbucket).
          apply (inv۰pure۰frozen Hinv2) in Hbucket as (gen & entries' & Hgen & Hi' & _).
          rewrite Hgens2_lookup in Hgen. injection Hgen as <-.
          simpl in Hi'. congruence.
        }
        iMod (frozenｰinsert cur2 i entries2 with "Hfrozen_auth") as "(Hfrozen_auth & #Hfrozen_elem)"; first done.
        iAssert (▷ entries۰model entries2)%I as "#Hentries2".
        { iNext. iApply (entries۰modelｰlookup Hgens2_lookup Hcells2_lookup with "Hentries_models"). }
        pose proof (inv۰pure۰wf Hinv2 _ _ Hgens2_lookup _ _ Hcells2_lookup) as Hwf.
        iDestruct ("Harrays" $! (buckets, <[i := CellFrozen entries2]> cells2) with "[Hmodel]") as "Harrays".
        { iEval (rewrite Nat2Z.id) in "Hmodel". rewrite /= list_fmap_insert /= Hentries2 //. }
        iSplitL.
        { iIntros "!> !>".
          iExists (<[cur2 := (buckets, <[i := CellFrozen entries2]> cells2)]> gens2), cur2, true, m2, (<[(cur2, i) := entries2]> frozen2), inited2, waiters2.
          rewrite (generations۰stateｰinsert Hgens2_lookup); first rewrite length_insert //.
          rewrite /generations۰auth /generations۰auth' (generations۰physｰinsert Hgens2_lookup); first rewrite length_insert //.
          iFrame "∗#".
          iSplitR.
          { iApply big_sepM_insert; first done. iFrame "#". }
          iSplitR.
          { iApply (entries۰modelsｰinsert (CellFrozen entries2) Hgens2_lookup Hcells2_lookup with "Hentries_models Hentries2"). }
          iSplitR.
          { iPureIntro. apply inv۰pureｰfreeze; done. }
          iApply (waiter۰modelsｰmono with "Hwaiters").
          - intros g' Hg'. rewrite list_lookup_total_insert_ne //. lia.
          - apply (inv۰pure۰waiters Hinv2).
        }
        iIntros "!> H£ (Hbackoff & HΦ)".
        iMod (lc_fupd_elim_later with "H£ Hentries2") as "#Hentries2'".
        wp۰pures.
        rewrite -Hentries2.
        iApply ("HΦ" $! entries2).
        rewrite Hcells2 /= in Hwf.
        iFrame "#". done.

      + iDestruct ("Harrays" $! (buckets, cells2) with "Hmodel") as "Harrays".
        rewrite list_insert_id //.
        iSplitL. { iFrameSteps. }
        iIntros "!> _ (Hbackoff & HΦ)".

        wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as (backoff') "Hbackoff".
        wp۰apply ("HLöb" with "Hbackoff HΦ").

    - iAssert (▷ entries۰model entries)%I as "#Hentries".
      { iNext. iApply (entries۰modelｰlookup Hgens1_lookup Hcells_lookup with "Hentries_models"). }
      opose proof* (proj2 (inv۰pure۰frozen Hinv1 g i (entries))) as HF.
      { eexists _, entries. done. }
      iDestruct (big_sepM_lookup with "Hfrozen_elems") as "#Hfrozen_elem"; first done.
      pose proof (inv۰pure۰wf Hinv1 _ _ Hgens1_lookup _ _ Hcells_lookup) as Hwf.
      simpl in Hwf.
      iSplitL. { iFrameSteps. }
      iIntros "!> H£ (Hbackoff & HΦ)".
      iMod (lc_fupd_elim_later with "H£ Hentries") as "#Hentries'".
      wp۰pures.
      iApply ("HΦ" $! entries).
      iFrame "#". done.
  Qed.

  #[local] Lemma htbl٠buckets٠takeｰspec γ 𝘩𝑎𝑠𝘩 g buckets cap buckets' cap' (i : nat) :
    i < cap →
    {{{
      inv' γ 𝘩𝑎𝑠𝘩 ∗
      gen۰witness γ g buckets cap ∗
      generations۰at γ ˖g buckets' cap'
    }}}
      htbl٠buckets٠take buckets #i
    {{{
      entries
    , RET bucket۰to_val (entries۰bucket entries);
      frozen۰elem γ g i entries ∗
      entries۰model entries ∗
      ⌜entries۰wf 𝘩𝑎𝑠𝘩 cap i entries⌝
    }}}.
  Proof.
    iIntros "%Hi %Φ (#Hinv & #Hwitness & #Hgens_at') HΦ".

    wp۰rec.
    wp۰apply+ (htbl٠buckets٠take₁ｰspec with "[$Hinv $Hwitness $Hgens_at'] HΦ"); first done.
    iApply backoff٠defaultｰspec.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [create]. *)

  Lemma htbl۰modelｰexclusive γ m1 m2 :
    htbl۰model γ m1 -∗
    htbl۰model γ m2 -∗
    False.
  Proof.
    iIntros "Hmodel₁_1 Hmodel₁_2".
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma htbl٠createｰspec ι hash 𝘩𝑎𝑠𝘩 equal :
    {{{
      htbl۰valid key۰model hash 𝘩𝑎𝑠𝘩 equal
    }}}
      htbl٠create hash equal
    {{{
      γ
    , RET γ;
      htbl۰inv γ ι ∗
      htbl۰model γ ∅
    }}}.
  Proof.
    iIntros "%Φ (#Hvalid_functional & #Hvalid_hash & #Hvalid_equal) HΦ".

    wp۰rec.
    rewrite htbl٠min_bucketsｰunfold.
    wp۰apply+ domain٠recommended_domain_countｰspec as "%sz %Hsz !>".
    wp۰apply (array٠makeｰtype itype۰int with "[]") as (sizes) "(_ & #Hsizes)".
    { iSteps. }
    wp۰apply+ (array٠makeｰspec with "[//]") as (buckets) "(_ & Hbuckets)".
    iEval (rewrite Nat2Z.id) in "Hbuckets".
    wp۰block t as "#Ht_hash #Ht_equal #Ht_sizes Ht_state".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod (generationsｰalloc [(buckets, replicate min_buckets (CellActive []))]) as "(%γ_generations & Hgens_auth)".
    iMod currentｰalloc as "(%γ_current & Hcurrent_auth)".
    iMod frozenｰalloc as "(%γ_frozen & Hfrozen_auth)".
    iMod initedｰalloc as "(%γ_inited & Hinited_auth)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ :=
      {|htbl۰name۰self := t
      ; htbl۰name۰inv := ι
      ; htbl۰name۰model := γ_model
      ; htbl۰name۰generations := γ_generations
      ; htbl۰name۰current := γ_current
      ; htbl۰name۰frozen := γ_frozen
      ; htbl۰name۰inited := γ_inited
      ; htbl۰name۰waiters := γ_waiters
      |}.

    iApply ("HΦ" $! γ).
    iSplitR "Hmodel₁"; last iFrame.
    iExists hash, 𝘩𝑎𝑠𝘩, equal, sizes, ₊⁺sz.
    iFrame "#".
    iSplitR; first done.
    iSplitR; first (iPureIntro; lia).
    iApply inv_alloc. iNext.
    iExists [(buckets, replicate min_buckets (CellActive []))], 0, false, ∅, ∅, ∅, ∅.
    rewrite /generations۰state /= length_replicate fmap_replicate.
    iFrame.
    iSplitR. { iApply big_sepM_empty. done. }
    iSplitR.
    { iSplitL; last done.
      iApply big_sepL_intro. iIntros "!> %k %cell %Hcell".
      apply lookup_replicate in Hcell as (-> & _).
      rewrite /entries۰model //.
    }
    iSplitR. { iPureIntro. apply (inv۰pureｰcreate 𝘩𝑎𝑠𝘩 buckets). }
    iApply big_sepM_empty. done.
    iSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [index]. *)

  #[local] Lemma htbl٠indexｰspec γ hash 𝘩𝑎𝑠𝘩 buckets cap o key 𝑘𝑒𝑦 :
    is_pow2 cap →
    {{{
      γ.(htbl۰name۰self).[hash] ↦□ hash ∗
      htbl۰valid۰hash key۰model hash 𝘩𝑎𝑠𝘩 ∗
      key۰model key 𝑘𝑒𝑦
    }}}
      htbl٠index γ (state۰to_val buckets cap o) key
    {{{
      RET #(entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦);
      True
    }}}.
  Proof.
    iIntros "%Hpow2 %Φ (#Hself_hash & #Hvalid_hash & #Hkey) HΦ".
    pose proof (is_pow2ｰpos _ Hpow2).

    wp۰rec.
    rewrite /state۰to_val.
    wp۰load.
    wp۰apply+ (wpｰwand with "(Hvalid_hash Hkey)") as (res) "->".
    wp۰pures.
    rewrite Zｰlandｰpow2ｰpred // -entries۰indexｰZ //.
    iApply "HΦ". done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find_node]. *)

  #[local] Lemma htbl٠find_nodeｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      htbl۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      htbl۰model γ m
    >>>
      htbl٠find_node γ key
      @ ↑ι
    <<<
      htbl۰model γ m
    | node,
      RET node;
      ⌜node۰result node (m !! 𝑘𝑒𝑦)⌝
    >>>.
  Proof.
    iIntros "%Φ (#Hhtbl & #Hkey) HΦ".
    iPoseProof "Hhtbl" as "(:inv)".
    set Ψ := (λ o, ∀ node, ⌜node۰result node o⌝ -∗ Φ node)%I.

    wp۰rec. wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (state۰witnessｰget with "Hgens_auth Hcurrent_auth Harrays") as "(Hgens_auth & Hcurrent_auth & Harrays & %buckets & %cap & %o & #Hwitness & _)"; first done.
    iMod (saved_predｰallocｰcofinite (dom waiters1) Ψ) as "(%η & %Hη & #Hη)".
    apply not_elem_of_dom in Hη.
    iMod (waitersｰinsert η {| waiter۰generation := cur1; waiter۰key := key |} with "Hwaiters_auth") as "(Hwaiters_auth & Hwaiters_elem)"; first done.
    iSplitR "Hwaiters_elem".
    { iIntros "!> !>".
      iExists gens1, cur1, resizing1, m1, frozen1, inited1, (<[η := {| waiter۰generation := cur1; waiter۰key := key |}]> waiters1).
      iFrame "∗#".
      iSplitR. { iPureIntro. apply inv۰pureｰwaitersｰinsert; done. }
      iApply big_sepM_insert; first done.
      iFrame.
      iExists 𝑘𝑒𝑦, Ψ. iFrame "#".
      rewrite decide_True //.
    }
    iIntros "!> {Hfrozen_elems Hentries_models}".

    iPoseProof "Hwitness" as "(:state۰witness)".
    pose proof (is_pow2ｰpos _ Hpow2).
    wp۰apply+ (htbl٠indexｰspec with "[$Hself_hash $Hvalid_hash $Hkey]") as "_"; first done.
    pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ltac:(lia)) as Hi.
    set i := entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦.
    rewrite /state۰to_val.
    wp۰pure credit:"H£1".

    awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Harray_inv"); first lia.
    iInv "Hinv" as "(:inv۰inner =2)".
    iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hgens2_lookup & <-).
    iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens2_lookup.
    iAaccIntro with "Hmodel".
    { iIntros "Hmodel !>".
      iDestruct ("Harrays" with "Hmodel") as "Harrays".
      iFrame "Hwaiters_elem H£1". iFrameSteps.
    }
    iIntros "%𝑣 (%Hlookup & Hmodel)".
    rewrite difference_empty_L.
    iMod (lc_fupd_elim_later with "H£1 Hwaiters") as "Hwaiters".
    iDestruct ("Harrays" with "Hmodel") as "Harrays".
    rewrite Nat2Z.id in Hlookup.
    apply list_lookup_fmap_Some in Hlookup as (cell & -> & Hcells_lookup).
    simpl in Hcells_lookup.
    iDestruct (current۰lbｰvalid with "Hcurrent_auth Hcurrent_lb") as %Hle.
    pose proof (inv۰pureｰnot_init Hinv2 Hgens2_lookup Hle Hcells_lookup) as Hcell.
    iDestruct (waiters۰elemｰvalid with "Hwaiters_auth Hwaiters_elem") as %Hwaiters2.
    iDestruct (big_sepM_delete with "Hwaiters") as "((%𝑘𝑒𝑦' & %Ψ' & #Hkey' & #Hη' & HΨ') & Hwaiters)"; first done.
    iDestruct ("Hvalid_functional" with "Hkey Hkey'") as %<-.
    iMod (waitersｰdelete with "Hwaiters_auth Hwaiters_elem") as "Hwaiters_auth".
    set r := entries۰lookup 𝑘𝑒𝑦 (cell۰entries cell).
    iAssert (model₂ γ m2 ∗ Ψ' r)%I with "[> HΨ' Hmodel₂]" as "(Hmodel₂ & HΨ')".
    { simpl.
      destruct (decide (cur1 = cur2)) as [<- | Hne].
      - iMod "HΨ'" as "(%m & Hmodel₁ & _ & HΨ')".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ'" with "Hmodel₁") as "HΨ'".
        iFrame.
        rewrite (inv۰pure۰model Hinv2 _ _ Hgens2_lookup) /cells۰lookup /= (list_lookup_total_correct _ _ _ Hcells_lookup) //.
      - iFrame.
        rewrite (list_lookup_total_correct _ _ _ Hgens2_lookup) /cells۰lookup /= (list_lookup_total_correct _ _ _ Hcells_lookup) //.
    }
    iAssert (▷ entries۰model (cell۰entries cell))%I as "#Hentries".
    { iNext. iApply (entries۰modelｰlookup Hgens2_lookup Hcells_lookup with "Hentries_models"). }
    iSplitR "HΨ'".
    { iIntros "!> !>".
      iExists gens2, cur2, resizing2, m2, frozen2, inited2, (delete η waiters2).
      iFrame "∗#".
      iPureIntro. apply inv۰pureｰwaitersｰdelete. done.
    }
    iIntros "!> H£2 {Hfrozen_elems Hentries_models}".
    iMod (lc_fupd_elim_later with "H£2 Hentries") as "#Hentries'".

    wp۰pure credit:"H£3".
    iDestruct (saved_predｰagree r with "Hη Hη'") as "Hagree".
    iMod (lc_fupd_elim_later with "H£3 Hagree") as "#Hagree'".
    iRewrite -"Hagree'" in "HΨ'".
    wp۰load.
    wp۰apply (htbl٠bucket٠assocｰspec _ key 𝑘𝑒𝑦 cell with "[$Hvalid_equal $Hkey $Hentries']") as (node) "%Hnode"; first done.
    iApply ("HΨ'" with "[//]").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [find] and [mem]. *)

  Lemma htbl٠findｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      htbl۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      htbl۰model γ m
    >>>
      htbl٠find γ key
      @ ↑ι
    <<<
      htbl۰model γ m
    | RET m !! 𝑘𝑒𝑦;
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hhtbl & #Hkey) HΦ".

    wp۰rec.
    awp۰apply+ (htbl٠find_nodeｰspec with "[$Hhtbl $Hkey]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%m Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iFrame. iIntros "HΦ !> %node %Hnode".
    destruct (m !! 𝑘𝑒𝑦) as [v' |]; simpl in Hnode.

    - destruct Hnode as (k & rest & ->).
      wp۰pures.
      iApply "HΦ". done.

    - subst node.
      wp۰pures.
      iApply "HΦ". done.
  Qed.

  Lemma htbl٠memｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      htbl۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      htbl۰model γ m
    >>>
      htbl٠mem γ key
      @ ↑ι
    <<<
      htbl۰model γ m
    | RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hhtbl & #Hkey) HΦ".

    wp۰rec.
    awp۰apply+ (htbl٠find_nodeｰspec with "[$Hhtbl $Hkey]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%m Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iFrame. iIntros "HΦ !> %node %Hnode".
    destruct (m !! 𝑘𝑒𝑦) as [v' |] eqn:Hlookup; simpl in Hnode.

    - destruct Hnode as (k & rest & ->).
      wp۰pures.
      rewrite bool_decide_eq_true_2; first (apply elem_of_dom; naive).
      iApply "HΦ". done.

    - subst node.
      wp۰pures.
      rewrite bool_decide_eq_false_2; first (apply not_elem_of_dom; done).
      iApply "HΦ". done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [split_buckets] and [merge_buckets]. *)

  #[local] Lemma entries۰modelｰfilter (P : entry Key → Prop) `{!∀ entry, Decision (P entry)} entries :
    entries۰model entries ⊢
    entries۰model (filter P entries).
  Proof.
    rewrite /entries۰model.
    induction entries as [| entry entries IH]; first iSteps.
    rewrite filter_cons big_sepL_cons.
    iIntros "(Hentry & Hentries)".
    case_decide.
    - rewrite big_sepL_cons. iFrame. iApply (IH with "Hentries").
    - iApply (IH with "Hentries").
  Qed.
  #[local] Lemma entries۰modelｰapp entries1 entries2 :
    entries۰model entries1 -∗
    entries۰model entries2 -∗
    entries۰model (entries1 ++ entries2).
  Proof.
    rewrite /entries۰model big_sepL_app. iSteps.
  Qed.

  #[local] Lemma htbl٠split_bucketsｰspec γ ι s g buckets cap buckets' cap' (n : nat) (step : Z) :
    cap' = 2 * cap →
    Z.Odd step →
    {{{
      htbl۰inv γ ι ∗
      state۰witness γ s g buckets cap (Some (buckets', cap')) ∗
      [∗ list] a ∈ seq 1 n,
        inited۰elem γ ˖g ₊((⁺a * step) `mod` ⁺cap) ∗
        inited۰elem γ ˖g (₊((⁺a * step) `mod` ⁺cap) + cap)
    }}}
      htbl٠split_buckets γ s buckets' #(⁺cap - 1) #((⁺n * step) `mod` ⁺cap) #step
    {{{
      b
    , RET #b;
      if b then
        ∀ j,
        ⌜j < cap'⌝ -∗
        inited۰elem γ ˖g j
      else
        True
    }}}.
  Proof.
    iIntros (-> Hstep) "%Φ ((:inv) & #Hwitness & #Hinited) HΦ".
    iDestruct "Hwitness" as "(:state۰witness)".
    iDestruct "Ho" as "((:gen۰witness =next) & %Hcaps)".
    pose proof (is_pow2ｰpos _ Hpow2).

    iLöb as "HLöb" forall (n) "Hinited".

    wp۰rec. wp۰pures.
    assert (Z.land ((⁺n * step) `mod` ⁺cap + step) (⁺cap - 1) = (⁺˖n * step) `mod` ⁺cap)%Z as ->.
    { rewrite Zｰlandｰpow2ｰpred // Zplus_mod_idemp_l. f_equal. lia. }
    pose proof (Z.mod_pos_bound (⁺˖n * step) ⁺cap ltac:(lia)) as Hi.
    set i := ₊((⁺˖n * step) `mod` ⁺cap).
    assert ((⁺˖n * step) `mod` ⁺cap = ⁺i)%Z as Hi' by lia.
    rewrite Hi'.
    rewrite /state۰to_val /status۰to_val.

    wp۰apply+ (htbl٠buckets٠takeｰspec _ 𝘩𝑎𝑠𝘩 g buckets cap buckets' (2 * cap) i with "[]") as (entries) "(#Hfrozen & #Hentries & %Hwf)"; first lia.
    { iFrameSteps. }
    wp۰apply+ (array٠sizeｰspecｰinv with "Harray_inv") as "_".
    wp۰pures.

    iAssert (
      ∀ target : Z,
      □ (
        ∀ key v 𝑘𝑒𝑦,
        ⌜Entry key v 𝑘𝑒𝑦 ∈ entries⌝ -∗
        WP (𝗳𝘂𝗻 "key" -> γ.{hash} "key" 𝗹𝗮𝗻𝗱 #⁺cap == #target)%V key {{ res,
          ⌜res = #(bool_decide (Z.land (𝘩𝑎𝑠𝘩 𝑘𝑒𝑦) ⁺cap = target))⌝
        }}
      )
    )%I as "#Hpred".
    { iIntros "%target !> %key %v %𝑘𝑒𝑦 %Hin".
      iDestruct (big_sepL_elem_of with "Hentries") as "Hkey"; first done.
      wp۰load.
      wp۰apply+ (wpｰwand with "(Hvalid_hash Hkey)") as (res) "->".
      iSteps.
    }
    wp۰apply (htbl٠bucket٠filterｰspec (λ entry, Z.land (𝘩𝑎𝑠𝘩 entry.(entry۰𝑘𝑒𝑦)) ⁺cap = 0)%Z _ entries) as "_".
    { iApply ("Hpred" $! 0%Z). }
    wp۰apply+ (htbl٠bucket٠filterｰspec (λ entry, Z.land (𝘩𝑎𝑠𝘩 entry.(entry۰𝑘𝑒𝑦)) ⁺cap = ⁺cap)%Z _ entries) as "_".
    { iApply ("Hpred" $! ⁺cap). }
    wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {Hfrozen_elems Hentries_models}".

    wp۰equal as _ | _; wp۰pures.

    - iApply "HΦ". done.

    - wp۰apply (htbl٠buckets٠cas_initｰspec _ 𝘩𝑎𝑠𝘩 g buckets cap buckets' (2 * cap) i (filter (λ entry, Z.land (𝘩𝑎𝑠𝘩 entry.(entry۰𝑘𝑒𝑦)) ⁺cap = 0%Z) entries) with "[]") as "#Hinited1"; first lia.
      { iFrame "#".
        iSplit; first done.
        iSplit; first (iPureIntro; apply is_pow2ｰdouble; done).
        iSplit; first iApply (entries۰modelｰfilter with "Hentries").
        iLeft. iSplit; first done.
        iExists entries. rewrite Nat.mod_small; first lia. iFrame "#". iPureIntro.
        rewrite /split۰entries bool_decide_eq_false_2 //. lia.
      }
      wp۰pures.
      rewrite -Nat2Z.inj_add.
      wp۰apply (htbl٠buckets٠cas_initｰspec _ 𝘩𝑎𝑠𝘩 g buckets cap buckets' (2 * cap) (i + cap) (filter (λ entry, Z.land (𝘩𝑎𝑠𝘩 entry.(entry۰𝑘𝑒𝑦)) ⁺cap = ⁺cap) entries) with "[]") as "#Hinited2"; first lia.
      { iFrame "#".
        iSplit; first done.
        iSplit; first (iPureIntro; apply is_pow2ｰdouble; done).
        iSplit; first iApply (entries۰modelｰfilter with "Hentries").
        iLeft. iSplit; first done.
        iExists entries. replace (i + cap) with (i + 1 * cap) by lia. rewrite Nat.Div0.mod_add Nat.mod_small; first lia. iFrame "#". iPureIntro.
        rewrite /split۰entries bool_decide_eq_true_2 //. lia.
      }
      iAssert (
        [∗ list] a ∈ seq 1 ˖n,
          inited۰elem γ ˖g ₊((⁺a * step) `mod` ⁺cap) ∗
          inited۰elem γ ˖g (₊((⁺a * step) `mod` ⁺cap) + cap)
      )%I as "#Hinited'".
      { rewrite seq_S big_sepL_app /=. iFrame "#". }
      wp۰pures.
      case_bool_decide as Hi0; wp۰pures.

      + iApply "HΦ".
        iIntros "!> %j %Hj".
        assert ((⁺˖n * step) `mod` ⁺cap = 0)%Z as Hzero by lia.
        destruct (Zｰcoverage cap step ˖n ⁺(j `mod` cap) Hpow2 Hstep ltac:(lia) Hzero) as (a & Ha & Haj).
        { pose proof (Nat.mod_upper_bound j cap ltac:(lia)). lia. }
        iDestruct (big_sepL_elem_of _ _ a with "Hinited'") as "(Hinited_lo & Hinited_hi)".
        { apply elem_of_seq. lia. }
        iEval (rewrite Haj Nat2Z.id) in "Hinited_lo".
        iEval (rewrite Haj Nat2Z.id) in "Hinited_hi".
        destruct (decide (j < cap)).
        * assert (j `mod` cap = j) as Hjm by (apply Nat.mod_small; lia).
          iEval (rewrite Hjm) in "Hinited_lo".
          iFrame "Hinited_lo".
        * assert (j `mod` cap + cap = j) as Hjm.
          { pose proof (Nat.div_mod j cap ltac:(lia)).
            assert (j `div` cap = 1) as Hdiv.
            { symmetry. apply Nat.div_unique with (j - cap); lia. }
            lia.
          }
          iEval (rewrite Hjm) in "Hinited_hi".
          iFrame "Hinited_hi".

      + rewrite -Hi'.
        iApply ("HLöb" $! ˖n with "HΦ Hinited'").
  Qed.

  #[local] Lemma htbl٠merge_bucketsｰspec γ ι s g buckets cap buckets' cap' (n : nat) (step : Z) :
    cap = 2 * cap' →
    Z.Odd step →
    {{{
      htbl۰inv γ ι ∗
      state۰witness γ s g buckets cap (Some (buckets', cap')) ∗
      [∗ list] a ∈ seq 1 n,
        inited۰elem γ ˖g ₊((⁺a * step) `mod` ⁺cap')
    }}}
      htbl٠merge_buckets γ s buckets' #(⁺cap' - 1) #((⁺n * step) `mod` ⁺cap') #step
    {{{
      b
    , RET #b;
      if b then
        ∀ j,
        ⌜j < cap'⌝ -∗
        inited۰elem γ ˖g j
      else
        True
    }}}.
  Proof.
    iIntros (-> Hstep) "%Φ ((:inv) & #Hwitness & #Hinited) HΦ".
    iDestruct "Hwitness" as "(:state۰witness)".
    iDestruct "Ho" as "((:gen۰witness =next) & %Hcaps)".
    pose proof (is_pow2ｰpos _ Hpow2_next).

    iLöb as "HLöb" forall (n) "Hinited".

    wp۰rec. wp۰pures.
    assert (Z.land ((⁺n * step) `mod` ⁺cap' + step) (⁺cap' - 1) = (⁺˖n * step) `mod` ⁺cap')%Z as ->.
    { rewrite Zｰlandｰpow2ｰpred // Zplus_mod_idemp_l. f_equal. lia. }
    pose proof (Z.mod_pos_bound (⁺˖n * step) ⁺cap' ltac:(lia)) as Hi.
    set i := ₊((⁺˖n * step) `mod` ⁺cap').
    assert ((⁺˖n * step) `mod` ⁺cap' = ⁺i)%Z as Hi' by lia.
    rewrite Hi'.
    rewrite /state۰to_val /status۰to_val.

    wp۰apply+ (htbl٠buckets٠takeｰspec _ 𝘩𝑎𝑠𝘩 g buckets (2 * cap') buckets' cap' i with "[]") as (entries1) "(#Hfrozen1 & #Hentries1 & _)"; first lia.
    { iFrameSteps. }
    wp۰apply+ (array٠sizeｰspecｰinv with "Harray_inv_next") as "_".
    wp۰pures.
    rewrite -Nat2Z.inj_add.
    wp۰apply (htbl٠buckets٠takeｰspec _ 𝘩𝑎𝑠𝘩 g buckets (2 * cap') buckets' cap' (i + cap') with "[]") as (entries2) "(#Hfrozen2 & #Hentries2 & _)"; first lia.
    { iFrameSteps. }
    wp۰apply+ (htbl٠bucket٠mergeｰspec entries1 entries2 with "[//]") as "_".
    wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {Hfrozen_elems Hentries_models}".

    wp۰equal as _ | _; wp۰pures.

    - iApply "HΦ". done.

    - wp۰apply (htbl٠buckets٠cas_initｰspec _ 𝘩𝑎𝑠𝘩 g buckets (2 * cap') buckets' cap' i (entries2 ++ entries1) with "[]") as "#Hinited1"; first lia.
      { iFrame "#".
        iSplit; first (iPureIntro; apply is_pow2ｰdouble; done).
        iSplit; first done.
        iRight. iSplit; done.
      }
      iAssert (
        [∗ list] a ∈ seq 1 ˖n,
          inited۰elem γ ˖g ₊((⁺a * step) `mod` ⁺cap')
      )%I as "#Hinited'".
      { rewrite seq_S big_sepL_app /=. iFrame "#". }
      wp۰pures.
      case_bool_decide as Hi0; wp۰pures.

      + iApply "HΦ".
        iIntros "!> %j %Hj".
        assert ((⁺˖n * step) `mod` ⁺cap' = 0)%Z as Hzero by lia.
        destruct (Zｰcoverage cap' step ˖n ⁺j Hpow2_next Hstep ltac:(lia) Hzero) as (a & Ha & Haj); first lia.
        iDestruct (big_sepL_elem_of _ _ a with "Hinited'") as "Hinited_a".
        { apply elem_of_seq. lia. }
        iEval (rewrite Haj Nat2Z.id) in "Hinited_a".
        iFrame "Hinited_a".

      + rewrite -Hi'.
        iApply ("HLöb" $! ˖n with "HΦ Hinited'").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [finish_as] and [finish]. *)

  #[local] Lemma htbl٠finish_asｰfinishｰspec γ ι :
    ⊢ (
      ∀ s g buckets cap o,
      {{{
        htbl۰inv γ ι ∗
        state۰witness γ s g buckets cap o
      }}}
        htbl٠finish_as γ s
      {{{
        RET ();
        True
      }}}
    ) ∧ (
      {{{
        htbl۰inv γ ι
      }}}
        htbl٠finish γ
      {{{
        RET ();
        True
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHfinish_as & IHfinish)".
    iSplit.

    { iIntros "%s %g %buckets %cap %o !> %Φ (#Hhtbl & #Hwitness) HΦ".
      iPoseProof "Hhtbl" as "(:inv)".

      wp۰rec.
      iPoseProof "Hwitness" as "(:state۰witness)".
      destruct o as [(buckets', cap') |].

      - iDestruct "Ho" as "((:gen۰witness =next) & %Hcaps)".
        rewrite /state۰to_val /status۰to_val.
        wp۰apply+ (array٠sizeｰspecｰinv with "Harray_inv") as "_".
        wp۰apply+ (array٠sizeｰspecｰinv with "Harray_inv_next") as "_".
        wp۰apply+ random٠bitsｰspec as "%k".
        wp۰pures.

        wp۰bind (𝗶𝗳 #(bool_decide (⁺cap < ⁺cap')) 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
        wp۰apply (wpｰwand (λ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then
            ∀ j,
            ⌜j < cap'⌝ -∗
            inited۰elem γ ˖g j
          else
            True
        )%I with "[]") as "%res (%b & -> & Hb)".
        { case_bool_decide as Hlt; wp۰pures.
          - assert (cap' = 2 * cap) as -> by lia.
            wp۰apply (htbl٠split_bucketsｰspec γ _ _ g buckets cap buckets' (2 * cap) 0 (Z.lor k 1) with "[]"); [done | apply Zｰlorｰ1ｰodd | |].
            { iFrame "#". iSteps. }
            iSteps.
          - assert (cap = 2 * cap') as -> by lia.
            wp۰apply (htbl٠merge_bucketsｰspec γ _ _ g buckets (2 * cap') buckets' cap' 0 (Z.lor k 1) with "[]"); [done | apply Zｰlorｰ1ｰodd | |].
            { iFrame "#". iSteps. }
            iSteps.
        }

        destruct b; wp۰pures; last first.
        { wp۰apply ("IHfinish" with "Hhtbl HΦ"). }

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =2)".
        wp۰cas as _ | Hsuc.

        + iSplitR "HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ ("IHfinish" with "Hhtbl HΦ").

        + iDestruct (state۰witnessｰsimilar g buckets cap (Some (buckets', cap')) Hinv2 Hsuc with "Hgens_auth []") as "(<- & %Hresizing2)".
          { iFrame "#". iSteps. }
          destruct resizing2; last done.
          iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hgens2_lookup & <-).
          iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at_next") as %(cells' & Hgens2_lookup' & <-).
          iAssert ⌜
            ∀ j cell',
            cells' !! j = Some cell' →
            cell' ≠ CellInit
          ⌝%I as %Hinit.
          { iIntros (j cell' Hj).
            iDestruct ("Hb" $! j with "[%]") as "Hinited_elem".
            { eapply lookup_lt_Some. done. }
            iDestruct (inited۰elemｰvalid with "Hinited_auth Hinited_elem") as %(gen & cell & Hgen & Hcell & Hcell')%(inv۰pure۰inited Hinv2).
            rewrite Hgens2_lookup' in Hgen. injection Hgen as <-.
            rewrite Hj in Hcell. injection Hcell as <-.
            done.
          }
          destruct (inv۰pureｰinstall Hinv2 Hgens2_lookup Hgens2_lookup' Hinit) as (Hinv2' & Hlookups).
          iMod (currentｰupdate ˖g with "Hcurrent_auth") as "Hcurrent_auth"; first lia.
          iMod (big_sepMｰimplｰthreadｰfupd (model₂ γ m2) (waiter۰model γ 𝘩𝑎𝑠𝘩 gens2 ˖g) with "Hwaiters Hmodel₂ []") as "(Hwaiters & Hmodel₂)".
          { iIntros "!> %η %waiter %Hwaiter (%𝑘𝑒𝑦 & %Ψ & #Hkey & #Hη & HΨ) Hmodel₂".
            pose proof (inv۰pure۰waiters Hinv2 _ _ Hwaiter).
            assert (waiter.(waiter۰generation) ≠ ˖g) as Hne by lia.
            destruct (decide (waiter.(waiter۰generation) = g)) as [Hwaiter1 | Hwaiter1].
            - iMod "HΨ" as "(%m & Hmodel₁ & _ & HΨ)".
              iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
              iMod ("HΨ" with "Hmodel₁") as "HΨ".
              iFrame "Hmodel₂". iExists 𝑘𝑒𝑦, Ψ. iFrame "#".
              rewrite (decide_False _ _ Hne) Hwaiter1 (list_lookup_total_correct _ _ _ Hgens2_lookup) /=.
              rewrite (inv۰pure۰model Hinv2 _ _ Hgens2_lookup) //.
            - iFrame "Hmodel₂". iExists 𝑘𝑒𝑦, Ψ. iFrame "#".
              rewrite (decide_False _ _ Hne). iFrame. done.
          }
          iSplitR "HΦ".
          { iIntros "!> !>".
            iExists gens2, ˖g, false, m2, frozen2, inited2, waiters2.
            rewrite /generations۰state (list_lookup_total_correct _ _ _ Hgens2_lookup') /=.
            iFrameSteps.
          }
          iModIntro.

          wp۰pures.
          iApply "HΦ". done.

      - rewrite /state۰to_val /status۰to_val.
        wp۰pures.
        iApply "HΦ". done.
    }

    { iIntros "!> %Φ #Hhtbl HΦ".
      iPoseProof "Hhtbl" as "(:inv)".

      wp۰rec.

      wp۰bind (_.{state})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (state۰witnessｰget with "Hgens_auth Hcurrent_auth Harrays") as "(Hgens_auth & Hcurrent_auth & Harrays & %buckets1 & %cap1 & %o1 & #Hwitness1 & _)"; first done.
      iSplitR "HΦ". { iFrameSteps. }
      iModIntro.

      wp۰apply ("IHfinish_as" with "[$Hhtbl $Hwitness1] HΦ").
    }
  Qed.
  #[local] Lemma htbl٠finish_asｰspec γ ι s g buckets cap o :
    {{{
      htbl۰inv γ ι ∗
      state۰witness γ s g buckets cap o
    }}}
      htbl٠finish_as γ s
    {{{
      RET ();
      True
    }}}.
  Proof.
    iDestruct htbl٠finish_asｰfinishｰspec as "(H & _)".
    iApply "H".
  Qed.
  #[local] Lemma htbl٠finishｰspec γ ι :
    {{{
      htbl۰inv γ ι
    }}}
      htbl٠finish γ
    {{{
      RET ();
      True
    }}}.
  Proof.
    iDestruct htbl٠finish_asｰfinishｰspec as "(_ & H)".
    iApply "H".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [resize]. *)

  #[local] Lemma htbl٠resize₁ｰspec γ ι s g buckets cap (new_cap : nat) :
    is_pow2 new_cap →
    new_cap = 2 * cap ∨ cap = 2 * new_cap →
    {{{
      htbl۰inv γ ι ∗
      state۰witness γ s g buckets cap None
    }}}
      htbl٠resize₁ γ s #new_cap
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hpow2' %Hrel %Φ (#Hhtbl & #Hwitness) HΦ".
    iPoseProof "Hhtbl" as "(:inv)".
    iPoseProof "Hwitness" as "(:state۰witness)".
    pose proof (is_pow2ｰpos _ Hpow2').

    wp۰rec.
    wp۰apply+ (array٠makeｰspec with "[//]") as (new) "(_ & Hnew)".
    rewrite Nat2Z.id.
    iDestruct (array۰modelｰtoｰinv with "Hnew") as "#Hnew_inv".
    rewrite length_replicate.
    rewrite /state۰to_val /status۰to_val.
    wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰cas as _ | Hsuc.

    - iSplitR "HΦ". { iFrameSteps. }
      iModIntro.

      wp۰pures.
      iApply "HΦ". done.

    - iDestruct (state۰witnessｰsimilar g buckets cap None Hinv1 Hsuc with "Hgens_auth []") as "(<- & %Hresizing1)".
      { iFrame "#". iSteps. }
      destruct resizing1; first by destruct Hresizing1.
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hgens1_lookup & <-).
      iAssert ⌜new ∉ gens1.*1⌝%I as %Hfresh.
      { iIntros (Hin).
        apply list_elem_of_fmap in Hin as ((buckets0 & cells0) & -> & Hin).
        apply list_elem_of_lookup in Hin as (g0 & Hg0).
        iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & _)"; first exact Hg0.
        iDestruct (array۰modelｰne with "Hnew Hmodel") as %?; first (rewrite length_replicate; lia).
        done.
      }
      pose proof (inv۰pure۰length Hinv1) as Hlength. simpl in Hlength. rewrite Nat.add_0_r in Hlength.
      iMod (generationsｰupdate (new, replicate new_cap CellInit) with "Hgens_auth") as "(Hgens_auth & #Hgens_at_new)".
      rewrite Hlength /= length_replicate.
      iSplitR "HΦ".
      { iIntros "!> !>".
        iExists (gens1 ++ [(new, replicate new_cap CellInit)]), g, true, m1, frozen1, inited1, waiters1.
        rewrite /generations۰state lookup_total_app_l; first lia.
        rewrite lookup_total_app_r; first lia.
        replace (˖g - length gens1) with 0 by lia.
        rewrite /= (list_lookup_total_correct _ _ _ Hgens1_lookup) /= length_replicate.
        rewrite big_sepL_snoc big_sepL_snoc /= fmap_replicate.
        iFrame "∗#".
        iSplitR.
        { iApply big_sepL_intro. iIntros "!> %k %cell %Hcell".
          apply lookup_replicate in Hcell as (-> & _).
          rewrite /entries۰model //.
        }
        iSplitR.
        { iPureIntro. eapply inv۰pureｰresize; done. }
        iApply (waiter۰modelsｰmono with "Hwaiters").
        - intros g' Hg'. rewrite lookup_total_app_l //. lia.
        - apply (inv۰pure۰waiters Hinv1).
      }
      iModIntro.

      wp۰apply+ (htbl٠finish_asｰspec _ _ _ g buckets (length cells) (Some (new, new_cap)) with "[$Hhtbl] HΦ").
      iFrame "#". iSteps.
  Qed.

  #[local] Lemma htbl٠resizeｰspec γ ι s g buckets cap o (delta : Z) :
    {{{
      htbl۰inv γ ι ∗
      state۰witness γ s g buckets cap o
    }}}
      htbl٠resize γ s #delta
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hhtbl & #Hwitness) HΦ".
    iPoseProof "Hhtbl" as "(:inv)".
    iPoseProof "Hwitness" as "(:state۰witness)".
    pose proof (is_pow2ｰpos _ Hpow2).
    pose proof (is_pow2ｰpos _ min_bucketsｰis_pow2).

    wp۰rec.
    wp۰load.
    wp۰apply (array٠sizeｰtype itype۰int with "Hsizes") as "_".
    wp۰apply domain٠self_indexｰspec as "%k !>".
    wp۰load.
    pose proof (Z.rem_bound_pos ⁺k ⁺sz ltac:(lia) ltac:(lia)) as Hrem.
    wp۰apply (array٠unsafe_faaｰtype with "Hsizes") as "%n _"; first lia.
    wp۰pures.
    rewrite /state۰to_val.
    destruct o as [(buckets', cap') |]; rewrite /status۰to_val; wp۰pures.

    - iApply "HΦ". done.

    - wp۰apply random٠bitsｰspec as "%r".
      wp۰pures.
      case_bool_decide; wp۰pures; last (iApply "HΦ"; done).

      wp۰bind (_.{state})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {Hfrozen_elems Hentries_models}".

      wp۰equal as _ | _; wp۰pures; first (iApply "HΦ"; done).
      wp۰load.
      wp۰apply (array٠sumｰtype with "Hsizes") as "%total _".
      wp۰apply+ (array٠sizeｰspecｰinv with "Harray_inv") as "_".
      destruct htbl٠max_bucketsｰspec as (mx & ->).
      rewrite htbl٠min_bucketsｰunfold.
      wp۰pures.

      iAssert (
        □ (
          ∀ Ψ,
          (True -∗ Ψ ()%V) -∗
          WP
            𝗶𝗳 (𝗶𝗳 #min_buckets < #⁺cap 𝘁𝗵𝗲𝗻 3 * #total < #⁺cap 𝗲𝗹𝘀𝗲 false) 𝘁𝗵𝗲𝗻 (
              htbl٠resize₁ γ (buckets, #(⁺cap - 1), §htbl٠Normal)%V (#⁺cap 𝗹𝘀𝗿 1)
            ) 𝗲𝗹𝘀𝗲 (
              ()
            )
          {{ Ψ }}
        )
      )%I as "#Hshrink".
      { iIntros "!> %Ψ HΨ".
        wp۰pures.
        case_bool_decide as Hcell1; wp۰pures; last (iApply "HΨ"; done).
        case_bool_decide as Hcell2; wp۰pures; last (iApply "HΨ"; done).
        destruct (is_pow2ｰhalf cap Hpow2) as (Hpow2' & Hhalf); first lia.
        assert (Z.shiftr ⁺cap 1 = ⁺(cap / 2))%Z as ->.
        { rewrite Z.shiftr_div_pow2; first lia. rewrite Nat2Z.inj_div //. }
        wp۰apply (htbl٠resize₁ｰspec _ _ _ g buckets cap (cap / 2) with "[] [HΨ]"); [done | right; done | | iSteps].
        iFrame "#". iSteps.
      }
      case_bool_decide as Hcell1; last (wp۰pure; wp۰pure; iApply ("Hshrink" with "HΦ")).
      wp۰pures.
      case_bool_decide as Hcell2; last (wp۰pure; iApply ("Hshrink" with "HΦ")).
      wp۰pures.
      assert (Z.shiftl ⁺cap 1 = ⁺(2 * cap))%Z as ->.
      { rewrite Z.shiftl_mul_pow2; lia. }
      wp۰apply (htbl٠resize₁ｰspec _ _ _ g buckets cap (2 * cap) with "[] HΦ"); [apply is_pow2ｰdouble; done | left; done |].
      iFrame "#". iSteps.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [add]. *)

  #[local] Lemma htbl٠add_auxｰaddｰspec γ ι key 𝑘𝑒𝑦 v :
    ⊢ (
      ∀ backoff,
      <<<
        htbl۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        backoff۰model backoff
      | ∀∀ m,
        htbl۰model γ m
      >>>
        htbl٠add_aux γ key v backoff
        @ ↑ι
      <<<
        htbl۰model γ (if decide (𝑘𝑒𝑦 ∈ dom m) then m else <[𝑘𝑒𝑦 := v]> m)
      | RET #(bool_decide (𝑘𝑒𝑦 ∉ dom m));
        True
      >>>
    ) ∧ (
      <<<
        htbl۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦
      | ∀∀ m,
        htbl۰model γ m
      >>>
        htbl٠add γ key v
        @ ↑ι
      <<<
        htbl۰model γ (if decide (𝑘𝑒𝑦 ∈ dom m) then m else <[𝑘𝑒𝑦 := v]> m)
      | RET #(bool_decide (𝑘𝑒𝑦 ∉ dom m));
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHadd_aux & IHadd)".
    iSplit.

    { iIntros "%backoff %Φ (#Hhtbl & #Hkey & Hbackoff) HΦ".
      iPoseProof "Hhtbl" as "(:inv)".

      wp۰rec. wp۰pures.

      wp۰bind (_.{state})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (state۰witnessｰget with "Hgens_auth Hcurrent_auth Harrays") as "(Hgens_auth & Hcurrent_auth & Harrays & %buckets & %cap & %o & #Hwitness & _)"; first done.
      iSplitR "Hbackoff HΦ". { iFrameSteps. }
      iIntros "!> {Hfrozen_elems Hentries_models}".

      iPoseProof "Hwitness" as "(:state۰witness)".
      pose proof (is_pow2ｰpos _ Hpow2).
      wp۰apply+ (htbl٠indexｰspec with "[$Hself_hash $Hvalid_hash $Hkey]") as "_"; first done.
      pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ltac:(lia)) as Hi.
      set i := entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦.
      rewrite /state۰to_val.

      awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Harray_inv") without "Hbackoff"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hgens2_lookup & <-).
      iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens2_lookup.
      iAaccIntro with "Hmodel".
      { iIntros "Hmodel !>".
        iDestruct ("Harrays" with "Hmodel") as "Harrays".
        iSplitL "Hgens_auth Hcurrent_auth Hmodel₂ Hself_state Hfrozen_auth Hinited_auth Hwaiters_auth Harrays Hwaiters"; last iSteps.
        iFrameSteps.
      }
      iIntros "%𝑣 (%Hlookup & Hmodel)".
      iDestruct ("Harrays" with "Hmodel") as "Harrays".
      rewrite Nat2Z.id in Hlookup.
      apply list_lookup_fmap_Some in Hlookup as (cell & -> & Hcells_lookup).
      simpl in Hcells_lookup.
      iDestruct (current۰lbｰvalid with "Hcurrent_auth Hcurrent_lb") as %Hg.
      destruct cell as [| entries | entries].

      - exfalso. by eapply (inv۰pureｰnot_init Hinv2 Hgens2_lookup Hg Hcells_lookup).

      - assert (cur1 = cur2) as <-.
        { destruct (decide (cur1 = cur2)); first done.
          opose proof* (inv۰pure۰old Hinv2 cur1) as (? & ?); [lia | done | done | done].
        }
        pose proof (inv۰pure۰model Hinv2 _ 𝑘𝑒𝑦 Hgens2_lookup) as Hm.
        rewrite /cells۰lookup /= (list_lookup_total_correct _ _ _ Hcells_lookup) /= in Hm.
        pose proof (inv۰pure۰wf Hinv2 _ _ Hgens2_lookup _ _ Hcells_lookup) as Hwf.
        simpl in Hwf.
        iAssert (▷ entries۰model entries)%I as "#Hentries".
        { iNext. iApply (entries۰modelｰlookup Hgens2_lookup Hcells_lookup with "Hentries_models"). }
        destruct (entries۰lookup 𝑘𝑒𝑦 entries) as [v'' |] eqn:Hlookup.

        + iMod "HΦ" as "(%m & Hmodel₁ & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          assert (𝑘𝑒𝑦 ∈ dom m2) as Hdom.
          { apply elem_of_dom. rewrite Hm //. }
          rewrite decide_True //.
          iMod ("HΦ" with "Hmodel₁") as "HΦ".
          iSplitR "HΦ". { iFrameSteps. }
          iIntros "!> H£ Hbackoff".
          iMod (lc_fupd_elim_later with "H£ Hentries") as "#Hentries'".
          wp۰load.
          wp۰apply (htbl٠bucket٠assocｰspecｰbucket _ key 𝑘𝑒𝑦 entries with "[$Hvalid_equal $Hkey $Hentries']") as "%node %Hnode".
          rewrite Hlookup in Hnode.
          destruct Hnode as (key'' & rest & ->).
          wp۰pures.
          rewrite bool_decide_eq_false_2; first naive.
          iApply "HΦ". done.

        + iSplitR "HΦ". { iFrameSteps. }
          iIntros "!> H£ Hbackoff {Hfrozen_elems Hentries_models}".
          iMod (lc_fupd_elim_later with "H£ Hentries") as "#Hentries'".

          wp۰load.
          wp۰apply (htbl٠bucket٠assocｰspecｰbucket _ key 𝑘𝑒𝑦 entries with "[$Hvalid_equal $Hkey $Hentries']") as "%node %Hnode".
          rewrite Hlookup in Hnode. simpl in Hnode. subst node.
          wp۰pure credit:"H£".

          awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Harray_inv") without "Hbackoff"; first lia.
          iInv "Hinv" as "(:inv۰inner =3)".
          iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells3 & Hgens3_lookup & Hcells3).
          iDestruct (big_sepL_insert_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens3_lookup.
          iAaccIntro with "Hmodel".
          { iIntros "Hmodel !>".
            iDestruct ("Harrays" $! (buckets, cells3) with "Hmodel") as "Harrays".
            rewrite list_insert_id //.
            iFrame "HΦ". iFrameSteps.
          }
          iIntros "%b %𝑣 (%Hlookup3 & %Hcas & Hmodel)".
          rewrite Nat2Z.id in Hlookup3.
          apply list_lookup_fmap_Some in Hlookup3 as (cell & -> & Hcells3_lookup).
          simpl in Hcells3_lookup.
          destruct b.

          * apply cell۰to_valｰsimilarｰbucket in Hcas as (entries3 & -> & Hentries3).
            iDestruct (current۰lbｰvalid with "Hcurrent_auth Hcurrent_lb") as %Hg3.
            assert (cur1 = cur3) as <-.
            { destruct (decide (cur1 = cur3)); first done.
              opose proof* (inv۰pure۰old Hinv3 cur1) as (? & ?); [lia | done | done | done].
            }
            iAssert (▷ entries۰model entries3)%I as "#Hentries3".
            { iNext. iApply (entries۰modelｰlookup Hgens3_lookup Hcells3_lookup with "Hentries_models"). }
            iMod (lc_fupd_elim_later with "H£ Hentries3") as "#Hentries3'".
            iDestruct (entries۰modelｰagree with "Hvalid_functional Hentries3' Hentries'") as %->; first done.
            pose proof (λ 𝑘𝑒𝑦, inv۰pure۰model Hinv3 _ 𝑘𝑒𝑦 Hgens3_lookup) as Hm3.
            assert (m3 !! 𝑘𝑒𝑦 = None) as Hm3k.
            { rewrite Hm3 /cells۰lookup /= Hcells3 (list_lookup_total_correct _ _ _ Hcells3_lookup) //. }
            iMod "HΦ" as "(%m & Hmodel₁ & _ & HΦ)".
            iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
            iMod (modelｰupdate (<[𝑘𝑒𝑦 := v]> m3) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
            assert (𝑘𝑒𝑦 ∉ dom m3) as Hdom by (apply not_elem_of_dom; done).
            iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
            { rewrite decide_False //. }
            iDestruct ("Harrays" $! (buckets, <[i := CellActive (Entry key v 𝑘𝑒𝑦 :: entries)]> cells3) with "[Hmodel]") as "Harrays".
            { iEval (rewrite Nat2Z.id) in "Hmodel". rewrite /= list_fmap_insert //. }
            iSplitR "HΦ".
            { iIntros "!> !>".
              iExists (<[cur1 := (buckets, <[i := CellActive (Entry key v 𝑘𝑒𝑦 :: entries)]> cells3)]> gens3), cur1, resizing3, (<[𝑘𝑒𝑦 := v]> m3), frozen3, inited3, waiters3.
              rewrite (generations۰stateｰinsert Hgens3_lookup); first rewrite length_insert //.
              rewrite /generations۰auth /generations۰auth' (generations۰physｰinsert Hgens3_lookup); first rewrite length_insert //.
              iFrame "∗#".
              iSplitR.
              { iApply (entries۰modelsｰinsert (CellActive (Entry key v 𝑘𝑒𝑦 :: entries)) Hgens3_lookup Hcells3_lookup with "Hentries_models").
                rewrite /entries۰model big_sepL_cons. iFrame "#".
              }
              iSplitR.
              { iPureIntro. eapply inv۰pureｰupdate; [done | done | done | |].
                - rewrite Hcells3. split.
                  + constructor; first done. apply Hwf.
                  + apply NoDup_cons. split; last apply Hwf.
                    apply entries۰lookupｰNone. done.
                - intros 𝑘𝑒𝑦'. rewrite Hcells3.
                  destruct (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦)) as [-> | Hne].
                  + rewrite lookup_insert_eq decide_True //= decide_True //.
                  + rewrite lookup_insert_ne //.
                    case_decide as Hidx; last done.
                    rewrite /= decide_False //.
                    rewrite Hm3 /cells۰lookup Hcells3 Hidx (list_lookup_total_correct _ _ _ Hcells3_lookup) //.
              }
              iApply (waiter۰modelsｰmono with "Hwaiters").
              - intros g' Hg'. rewrite list_lookup_total_insert_ne //. lia.
              - apply (inv۰pure۰waiters Hinv3).
            }
            iIntros "!> _ Hbackoff".

            wp۰apply+ (htbl٠resizeｰspec with "[$Hhtbl $Hwitness]") as "_".
            wp۰pures.
            rewrite bool_decide_eq_true_2 //.
            iApply "HΦ". done.

          * iDestruct ("Harrays" $! (buckets, cells3) with "Hmodel") as "Harrays".
            rewrite list_insert_id //.
            iSplitR "HΦ". { iFrameSteps. }
            iIntros "!> _ Hbackoff".

            wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as (backoff') "Hbackoff".
            wp۰apply ("IHadd_aux" with "[$Hhtbl $Hkey $Hbackoff] HΦ").

      - iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> _ Hbackoff".

        wp۰apply+ (htbl٠finishｰspec with "Hhtbl") as "_".
        wp۰apply+ ("IHadd" with "[$Hhtbl $Hkey] HΦ").
    }

    { iIntros "%Φ (#Hhtbl & #Hkey) HΦ".

      wp۰rec.
      wp۰apply+ ("IHadd_aux" with "[$Hhtbl $Hkey] HΦ").
      iApply backoff٠defaultｰspec.
    }
  Qed.

  Lemma htbl٠addｰspec γ ι key 𝑘𝑒𝑦 v :
    <<<
      htbl۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      htbl۰model γ m
    >>>
      htbl٠add γ key v
      @ ↑ι
    <<<
      htbl۰model γ (if decide (𝑘𝑒𝑦 ∈ dom m) then m else <[𝑘𝑒𝑦 := v]> m)
    | RET #(bool_decide (𝑘𝑒𝑦 ∉ dom m));
      True
    >>>.
  Proof.
    iDestruct (htbl٠add_auxｰaddｰspec γ ι key 𝑘𝑒𝑦 v) as "(_ & H)".
    iApply "H".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [remove]. *)

  #[local] Lemma entries۰lookupｰlist_find 𝑘𝑒𝑦 entries :
    entries۰lookup 𝑘𝑒𝑦 entries = None ↔
    list_find (λ 𝑘𝑒𝑦', 𝑘𝑒𝑦 = 𝑘𝑒𝑦') (entries۰𝑘𝑒𝑦𝑠 entries) = None.
  Proof.
    rewrite entries۰lookupｰNone list_find_None Forall_forall.
    naive.
  Qed.

  #[local] Lemma entries۰modelｰsep2 entries :
    entries۰model entries ⊢
    [∗ list] key'; 𝑘𝑒𝑦' ∈ (entries۰bucket entries).*1; entries۰𝑘𝑒𝑦𝑠 entries,
      key۰model key' 𝑘𝑒𝑦'.
  Proof.
    rewrite /entries۰model.
    induction entries as [| [key v 𝑘𝑒𝑦] entries IH]; first iSteps.
    rewrite big_sepL_cons /=. iIntros "($ & Hentries)".
    iApply (IH with "Hentries").
  Qed.

  #[local] Lemma entries۰modelｰdelete entries k :
    entries۰model entries ⊢
    entries۰model (delete k entries).
  Proof.
    rewrite /entries۰model.
    iInduction entries as [| entry entries] "IH" forall (k); first iSteps.
    iIntros "(Hentry & Hentries)".
    destruct k as [| k]; first iFrame.
    rewrite /=. iFrame.
    iApply ("IH" with "Hentries").
  Qed.

  #[local] Lemma htbl٠remove_auxｰremoveｰspec γ ι key 𝑘𝑒𝑦 :
    ⊢ (
      ∀ backoff,
      <<<
        htbl۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦 ∗
        backoff۰model backoff
      | ∀∀ m,
        htbl۰model γ m
      >>>
        htbl٠remove_aux γ key backoff
        @ ↑ι
      <<<
        htbl۰model γ (delete 𝑘𝑒𝑦 m)
      | RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
        True
      >>>
    ) ∧ (
      <<<
        htbl۰inv γ ι ∗
        key۰model key 𝑘𝑒𝑦
      | ∀∀ m,
        htbl۰model γ m
      >>>
        htbl٠remove γ key
        @ ↑ι
      <<<
        htbl۰model γ (delete 𝑘𝑒𝑦 m)
      | RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHremove_aux & IHremove)".
    iSplit.

    { iIntros "%backoff %Φ (#Hhtbl & #Hkey & Hbackoff) HΦ".
      iPoseProof "Hhtbl" as "(:inv)".

      wp۰rec. wp۰pures.

      wp۰bind (_.{state})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (state۰witnessｰget with "Hgens_auth Hcurrent_auth Harrays") as "(Hgens_auth & Hcurrent_auth & Harrays & %buckets & %cap & %o & #Hwitness & _)"; first done.
      iSplitR "Hbackoff HΦ". { iFrameSteps. }
      iIntros "!> {Hfrozen_elems Hentries_models}".

      iPoseProof "Hwitness" as "(:state۰witness)".
      pose proof (is_pow2ｰpos _ Hpow2).
      wp۰apply+ (htbl٠indexｰspec with "[$Hself_hash $Hvalid_hash $Hkey]") as "_"; first done.
      pose proof (entries۰indexｰlt 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦 ltac:(lia)) as Hi.
      set i := entries۰index 𝘩𝑎𝑠𝘩 cap 𝑘𝑒𝑦.
      rewrite /state۰to_val.

      awp۰apply+ (array٠unsafe_getｰspecｰatomicｰinv with "Harray_inv") without "Hbackoff"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells & Hgens2_lookup & <-).
      iDestruct (big_sepL_lookup_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens2_lookup.
      iAaccIntro with "Hmodel".
      { iIntros "Hmodel !>".
        iDestruct ("Harrays" with "Hmodel") as "Harrays".
        iSplitL "Hgens_auth Hcurrent_auth Hmodel₂ Hself_state Hfrozen_auth Hinited_auth Hwaiters_auth Harrays Hwaiters"; last iSteps.
        iFrameSteps.
      }
      iIntros "%𝑣 (%Hlookup & Hmodel)".
      iDestruct ("Harrays" with "Hmodel") as "Harrays".
      rewrite Nat2Z.id in Hlookup.
      apply list_lookup_fmap_Some in Hlookup as (cell & -> & Hcells_lookup).
      simpl in Hcells_lookup.
      iDestruct (current۰lbｰvalid with "Hcurrent_auth Hcurrent_lb") as %Hg.
      destruct cell as [| entries | entries].

      - exfalso. by eapply (inv۰pureｰnot_init Hinv2 Hgens2_lookup Hg Hcells_lookup).

      - assert (cur1 = cur2) as <-.
        { destruct (decide (cur1 = cur2)); first done.
          opose proof* (inv۰pure۰old Hinv2 cur1) as (? & ?); [lia | done | done | done].
        }
        pose proof (inv۰pure۰model Hinv2 _ 𝑘𝑒𝑦 Hgens2_lookup) as Hm.
        rewrite /cells۰lookup /= (list_lookup_total_correct _ _ _ Hcells_lookup) /= in Hm.
        pose proof (inv۰pure۰wf Hinv2 _ _ Hgens2_lookup _ _ Hcells_lookup) as Hwf.
        simpl in Hwf.
        iAssert (▷ entries۰model entries)%I as "#Hentries".
        { iNext. iApply (entries۰modelｰlookup Hgens2_lookup Hcells_lookup with "Hentries_models"). }
        destruct (entries۰lookup 𝑘𝑒𝑦 entries) as [v'' |] eqn:Hlookup.

        + iSplitR "HΦ". { iFrameSteps. }
          iIntros "!> H£ Hbackoff {Hfrozen_elems Hentries_models}".
          iMod (lc_fupd_elim_later with "H£ Hentries") as "#Hentries'".

          wp۰load.
          wp۰apply (htbl٠bucket٠dissocｰspec equal key 𝑘𝑒𝑦 (entries۰bucket entries) (entries۰𝑘𝑒𝑦𝑠 entries) with "Hvalid_equal Hkey [] [Hbackoff HΦ]").
          { rewrite !length_fmap //. }
          { iModIntro. iApply (entries۰modelｰsep2 with "Hentries'"). }
          destruct (list_find (λ 𝑘𝑒𝑦', 𝑘𝑒𝑦 = 𝑘𝑒𝑦') (entries۰𝑘𝑒𝑦𝑠 entries)) as [(k, 𝑘𝑒𝑦'') |] eqn:Hfind; last first.
          { apply entries۰lookupｰlist_find in Hfind. congruence. }
          apply list_find_Some in Hfind as (Hk & <- & _).
          iNext. simpl.
          rewrite -list_fmap_delete.
          wp۰pure credit:"H£".

          awp۰apply+ (array٠unsafe_casｰspecｰatomicｰinv with "Harray_inv") without "Hbackoff"; first lia.
          iInv "Hinv" as "(:inv۰inner =3)".
          iDestruct (generations۰atｰvalid with "Hgens_auth Hgens_at") as %(cells3 & Hgens3_lookup & Hcells3).
          iDestruct (big_sepL_insert_acc with "Harrays") as "(Hmodel & Harrays)"; first exact Hgens3_lookup.
          iAaccIntro with "Hmodel".
          { iIntros "Hmodel !>".
            iDestruct ("Harrays" $! (buckets, cells3) with "Hmodel") as "Harrays".
            rewrite list_insert_id //.
            iFrame "HΦ". iFrameSteps.
          }
          iIntros "%b %𝑣 (%Hlookup3 & %Hcas & Hmodel)".
          rewrite Nat2Z.id in Hlookup3.
          apply list_lookup_fmap_Some in Hlookup3 as (cell & -> & Hcells3_lookup).
          simpl in Hcells3_lookup.
          destruct b.

          * apply cell۰to_valｰsimilarｰbucket in Hcas as (entries3 & -> & Hentries3).
            iDestruct (current۰lbｰvalid with "Hcurrent_auth Hcurrent_lb") as %Hg3.
            assert (cur1 = cur3) as <-.
            { destruct (decide (cur1 = cur3)); first done.
              opose proof* (inv۰pure۰old Hinv3 cur1) as (? & ?); [lia | done | done | done].
            }
            iAssert (▷ entries۰model entries3)%I as "#Hentries3".
            { iNext. iApply (entries۰modelｰlookup Hgens3_lookup Hcells3_lookup with "Hentries_models"). }
            iMod (lc_fupd_elim_later with "H£ Hentries3") as "#Hentries3'".
            iDestruct (entries۰modelｰagree with "Hvalid_functional Hentries3' Hentries'") as %->; first done.
            pose proof (λ 𝑘𝑒𝑦, inv۰pure۰model Hinv3 _ 𝑘𝑒𝑦 Hgens3_lookup) as Hm3.
            assert (m3 !! 𝑘𝑒𝑦 = Some v'') as Hm3k.
            { rewrite Hm3 /cells۰lookup /= Hcells3 (list_lookup_total_correct _ _ _ Hcells3_lookup) //. }
            iMod "HΦ" as "(%m & Hmodel₁ & _ & HΦ)".
            iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
            iMod (modelｰupdate (delete 𝑘𝑒𝑦 m3) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
            iMod ("HΦ" with "Hmodel₁") as "HΦ".
            iDestruct ("Harrays" $! (buckets, <[i := CellActive (delete k entries)]> cells3) with "[Hmodel]") as "Harrays".
            { iEval (rewrite Nat2Z.id) in "Hmodel". rewrite /= list_fmap_insert //. }
            iSplitR "HΦ".
            { iIntros "!> !>".
              iExists (<[cur1 := (buckets, <[i := CellActive (delete k entries)]> cells3)]> gens3), cur1, resizing3, (delete 𝑘𝑒𝑦 m3), frozen3, inited3, waiters3.
              rewrite (generations۰stateｰinsert Hgens3_lookup); first rewrite length_insert //.
              rewrite /generations۰auth /generations۰auth' (generations۰physｰinsert Hgens3_lookup); first rewrite length_insert //.
              iFrame "∗#".
              iSplitR.
              { iApply (entries۰modelsｰinsert (CellActive (delete k entries)) Hgens3_lookup Hcells3_lookup with "Hentries_models").
                iApply (entries۰modelｰdelete with "Hentries'").
              }
              iSplitR.
              { iPureIntro. eapply inv۰pureｰupdate; [done | done | done | |].
                - rewrite Hcells3. apply (entries۰wfｰsublist _ _ _ _ entries); last done.
                  apply sublist_delete.
                - intros 𝑘𝑒𝑦'. rewrite Hcells3.
                  rewrite (entries۰lookupｰdelete 𝑘𝑒𝑦 entries k); [apply Hwf | done |].
                  destruct (decide (𝑘𝑒𝑦' = 𝑘𝑒𝑦)) as [-> | Hne].
                  + rewrite lookup_delete_eq decide_True //.
                  + rewrite lookup_delete_ne //.
                    case_decide as Hidx; last done.
                    rewrite Hm3 /cells۰lookup Hcells3 Hidx (list_lookup_total_correct _ _ _ Hcells3_lookup) //.
              }
              iApply (waiter۰modelsｰmono with "Hwaiters").
              - intros g' Hg'. rewrite list_lookup_total_insert_ne //. lia.
              - apply (inv۰pure۰waiters Hinv3).
            }
            iIntros "!> _ Hbackoff".

            wp۰apply+ (htbl٠resizeｰspec with "[$Hhtbl $Hwitness]") as "_".
            wp۰pures.
            rewrite bool_decide_eq_true_2; first (apply elem_of_dom; naive).
            iApply "HΦ". done.

          * iDestruct ("Harrays" $! (buckets, cells3) with "Hmodel") as "Harrays".
            rewrite list_insert_id //.
            iSplitR "HΦ". { iFrameSteps. }
            iIntros "!> _ Hbackoff".

            wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as (backoff') "Hbackoff".
            wp۰apply ("IHremove_aux" with "[$Hhtbl $Hkey $Hbackoff] HΦ").

        + iMod "HΦ" as "(%m & Hmodel₁ & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          assert (𝑘𝑒𝑦 ∉ dom m2) as Hdom.
          { apply not_elem_of_dom. rewrite Hm //. }
          rewrite delete_id; first (apply not_elem_of_dom; done).
          iMod ("HΦ" with "Hmodel₁") as "HΦ".
          iSplitR "HΦ". { iFrameSteps. }
          iIntros "!> H£ Hbackoff {Hfrozen_elems Hentries_models}".
          iMod (lc_fupd_elim_later with "H£ Hentries") as "#Hentries'".

          wp۰load.
          wp۰apply (htbl٠bucket٠dissocｰspec equal key 𝑘𝑒𝑦 (entries۰bucket entries) (entries۰𝑘𝑒𝑦𝑠 entries) with "Hvalid_equal Hkey [] [HΦ]").
          { rewrite !length_fmap //. }
          { iModIntro. iApply (entries۰modelｰsep2 with "Hentries'"). }
          apply entries۰lookupｰlist_find in Hlookup as ->.
          iNext. simpl.
          wp۰pures.
          rewrite bool_decide_eq_false_2 //.
          iApply "HΦ". done.

      - iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> _ Hbackoff".

        wp۰apply+ (htbl٠finishｰspec with "Hhtbl") as "_".
        wp۰apply+ ("IHremove" with "[$Hhtbl $Hkey] HΦ").
    }

    { iIntros "%Φ (#Hhtbl & #Hkey) HΦ".

      wp۰rec.
      wp۰apply+ ("IHremove_aux" with "[$Hhtbl $Hkey] HΦ").
      iApply backoff٠defaultｰspec.
    }
  Qed.

  Lemma htbl٠removeｰspec γ ι key 𝑘𝑒𝑦 :
    <<<
      htbl۰inv γ ι ∗
      key۰model key 𝑘𝑒𝑦
    | ∀∀ m,
      htbl۰model γ m
    >>>
      htbl٠remove γ key
      @ ↑ι
    <<<
      htbl۰model γ (delete 𝑘𝑒𝑦 m)
    | RET #(bool_decide (𝑘𝑒𝑦 ∈ dom m));
      True
    >>>.
  Proof.
    iDestruct (htbl٠remove_auxｰremoveｰspec γ ι key 𝑘𝑒𝑦) as "(_ & H)".
    iApply "H".
  Qed.

End htbl۰G.

Require zoo_saturn.htbl__opaque.

Please opacify.
