From iris Require Import
  ghost_map
  gmap.
From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.mono_set
  lib.mono_list
.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  assert
  lst.
From zebre.persistent Require Export
  base
  pstore_1.
From zebre Require Import
  options.

Section Go.

Notation timestamp := nat.

Context `{pstore_G : PstoreG Σ}.
Context {IG1: ghost_mapG Σ (location*timestamp) val}.
Context {IG2: MonoListG Σ (gmap location val)%type}.

Record gnames := {γ1 : gname; γ2 : gname}.

Definition auth_snap_auth γ xs :=
  mono_list_auth γ.(γ2) (DfracOwn 1%Qp) xs.

Definition auth_snap_frag γ ρ σ :=
  mono_list_elem γ ρ σ.

Definition coherent
  (ρ:timestamp) (σ:gmap location val) (M:gmap (location*timestamp) val) :=
  forall l v , M !! (l,ρ) = Some v -> σ !! l = Some v.

Definition dom_le (ρ:timestamp) (M:gmap (location*timestamp) val) :=
  forall l ρ', (l,ρ') ∈ dom M -> ρ' <= ρ.

Record pureinv (ρ:timestamp) (σ:gmap location val) (M:gmap (location*timestamp) val) (xs:list (gmap location val)) :=
  { pu1: ρ = length xs;
    pu2: coherent ρ σ M;
    pu3: forall ρ' σ', xs !! ρ' = Some σ' -> coherent ρ' σ' M;
    pu4: dom_le ρ M
  }.

Definition isnow γ (s:val) (ρ:timestamp) : iProp Σ :=
  ∃ (σ:gmap location val) (* the current model of the store *)
    (M:gmap (location*timestamp) val) (* The points-tos, timestamped *)
    (xs:list (gmap location val)), (* The list of "generations"? To each timestamp < ρ, associates its model. *)
   ⌜pureinv ρ σ M xs⌝ ∗ pstore s σ ∗ ghost_map_auth γ.(γ1) 1%Qp M ∗
   mono_list_auth γ.(γ2) (DfracOwn 1%Qp) xs.

Definition pat_now := "[%σ [%M [%xs (%Hpure&Hstore&Hpointsto&Hsnap)]]]".

Definition snapshot γ t s ρ : iProp Σ :=
  ∃ σ, pstore_snapshot t s σ ∗ auth_snap_frag γ.(γ2) ρ σ .

Global Instance snapshot_persistent γ t s ρ : Persistent (snapshot γ t s ρ).
Proof. apply _. Qed.

Definition mapsto γ ρ l v :=
  ghost_map_elem γ.(γ1) (l,ρ) (DfracOwn 1) v.

Lemma lookup_insert_case `{Countable K} {V} (X:gmap K V) x y i :
  <[y:=i]> X !! x = if (decide (y=x)) then Some i else X !! x.
Proof. case_decide; subst. rewrite lookup_insert //. rewrite lookup_insert_ne //. Qed.

Lemma coherent_insert_bump M l ρ v σ :
  dom_le ρ M ->
  coherent ρ σ M ->
  M !! (l, ρ) = Some v ->
  coherent (S ρ) σ (<[(l, S ρ):=v]> M).
Proof.
  intros Hdom Hco ? l' ? E.
  rewrite lookup_insert_case in E.
  case_decide. naive_solver. exfalso.
  apply elem_of_dom_2,Hdom in E. lia.
Qed.

Lemma dom_le_bump l ρ v M :
  dom_le ρ M ->
  dom_le (S ρ) (<[(l, S ρ):=v]> M).
Proof.
  intros Hd.
  intros ??. rewrite dom_insert_L elem_of_union elem_of_singleton.
  intros [X|X]; first naive_solver by lia.
  apply Hd in X. lia.
Qed.

Lemma dom_le_update l ρ v M :
  dom_le ρ M ->
  dom_le ρ (<[(l, ρ):=v]> M).
Proof.
  intros Hd.
  intros ??. rewrite dom_insert_L elem_of_union elem_of_singleton.
  intros [X|X]; first naive_solver by lia.
  apply Hd in X. lia.
Qed.

Lemma coherent_insert_unrel ρ' ρ σ M l v :
  ρ ≠ ρ' ->
  coherent ρ' σ M ->
  coherent ρ' σ (<[(l, ρ):=v]> M).
Proof.
  intros Hcoh. intros ? l' v'.
  rewrite lookup_insert_case. intros E.
  case_decide; naive_solver.
Qed.

Lemma pstore_capture_spec γ s ρ l v :
    {{{
      isnow γ s ρ ∗ mapsto γ ρ l v
    }}}
      pstore_capture s
    {{{ t ρ',
      RET t;
      isnow γ s ρ' ∗ snapshot γ s t ρ ∗ mapsto γ ρ l v ∗ mapsto γ ρ' l v
    }}}.
Proof.
  iIntros (?) "(Hnow&Hmaps) Hpost".
  iDestruct "Hnow" as pat_now.
  iApply wp_fupd.
  wp_apply (pstore_capture_spec with "Hstore").
  iIntros (t) "(Hstore&#X)".
  iMod (mono_list_update_app [σ] with "Hsnap") as "Hsnap".
  iDestruct (mono_list_lb_get with "Hsnap") as "#HX".
  iDestruct (mono_list_elem_get (length xs) with "HX") as "#Hgo".
  { rewrite lookup_app_r // Nat.sub_diag //. }
  iClear "HX".

  iDestruct (ghost_map_lookup with "[$][$]") as "%".
  iMod (ghost_map_insert (l,(S ρ)) v with "Hpointsto") as "(?&?)".
  { destruct Hpure as [X1 X2 X3 X4]. apply not_elem_of_dom.
    intros F. apply X4 in F. lia. }

  iModIntro. iApply ("Hpost" $! t (S ρ)).
  iFrame.
  iSplitL.
  2:{ destruct Hpure. subst. iExists _. iFrame "#". }
  iExists _,_,_. iFrame. iPureIntro.
  { destruct Hpure as [X1 X2 X3 X4].
    constructor; eauto using coherent_insert_bump,dom_le_bump.
    { rewrite app_length //. simpl. lia. }
    { intros ??. rewrite lookup_app_Some. intros [?|(?&?)].
      { eapply coherent_insert_unrel.
        { apply lookup_lt_Some in H0. lia. }
        { eauto. } }
      { apply list_lookup_singleton_Some in H1. destruct H1 as (?&<-).
        assert (ρ' = ρ) as -> by lia.
        eauto using coherent_insert_unrel. } } }
Qed.

Lemma pstore_restore_spec γ s t ρ0 ρ l v :
    {{{
      isnow γ s ρ0 ∗ snapshot γ s t ρ ∗ mapsto γ ρ l v
    }}}
      pstore_restore s t
    {{{ ρ',
      RET ();
      isnow γ s ρ' ∗ mapsto γ ρ l v ∗ mapsto γ ρ' l v
    }}}.
Proof.
  iIntros (?) "(Hnow&Ht&E) Hpost".
  iDestruct "Hnow" as pat_now.
  iApply wp_fupd. rename σ into σ0.

  iDestruct "Ht" as "[%σ (Ht&?)]".
  wp_apply (pstore_restore_spec with "[$]").
  iIntros "Hstore".
  iApply ("Hpost" $! (S ρ0)).

  iDestruct (mono_list_lookup with "Hsnap [$]") as "%".
  iMod (mono_list_update_app [σ0] with "Hsnap") as "Hsnap".

  iDestruct (ghost_map_lookup with "[$][$]") as "%".
  iMod (ghost_map_insert (l,(S ρ0)) v with "Hpointsto") as "(?&?)".
  (* XXX lemma *)
  { destruct Hpure as [X1 X2 X3 X4]. apply not_elem_of_dom.
    intros F. apply X4 in F. lia. }
  iFrame.

  iExists _,_,_. iFrame.
  iPureIntro.
  destruct Hpure as [X1 X2 X3 X4].
  constructor; eauto using dom_le_bump.
  { rewrite app_length. simpl. lia. }
  { intros l' v' E.
    rewrite lookup_insert_case in E. case_decide.
    { inversion E. subst v. clear E.
      assert (l'=l) by naive_solver. subst l'.
      eapply X3; eauto. }
    { exfalso. apply elem_of_dom_2,X4 in E. lia. } }
  { intros ρ' σ'. rewrite lookup_app_Some. intros [X|(?&X)].
    { eapply coherent_insert_unrel; eauto.
      apply lookup_lt_Some in X. lia. }
    { apply list_lookup_singleton_Some in X. destruct X as (?&<-).
      assert (ρ' = ρ0) as -> by lia.
      eauto using coherent_insert_unrel. } }
Qed.

Lemma pstore_get_spec γ s ρ l v :
  {{{
     isnow γ s ρ ∗ mapsto γ ρ l v
  }}}
    pstore_get s #l
  {{{
     RET v;
     isnow γ s ρ ∗ mapsto γ ρ l v
  }}}.
Proof.
  iIntros (?) "(Hnow&Hl) Hpost".
  iDestruct "Hnow" as pat_now.
  iDestruct (ghost_map_lookup with "[$][$]") as "%".
  wp_apply (pstore_get_spec v with "[$]").
  { destruct Hpure as [X1 X2 X3 X4]. eauto. }
  iIntros "?".
  iApply "Hpost". iFrame. iExists _,_,_. by iFrame.
Qed.

Lemma coherent_update ρ σ M l v :
  coherent ρ σ M ->
  coherent ρ (<[l:=v]> σ) (<[(l, ρ):=v]> M).
Proof.
  intros Hcoh. intros l' v'. rewrite lookup_insert_case.
  case_decide as Eq.
  { inversion Eq. subst. rewrite lookup_insert. naive_solver. }
  { rewrite lookup_insert_ne; naive_solver. }
Qed.

Lemma pstore_set_spec γ s ρ l v v' :
  {{{
     isnow γ s ρ ∗ mapsto γ ρ l v
  }}}
    pstore_set s #l v'
  {{{
     RET ();
     isnow γ s ρ ∗ mapsto γ ρ l v'
  }}}.
Proof.
  iIntros (?) "(Hnow&Hl) Hpost".
  iDestruct "Hnow" as pat_now.
  iApply wp_fupd.

  iDestruct (ghost_map_lookup with "[$][$]") as "%".
  wp_apply (pstore_set_spec with "[$]").
  { destruct Hpure as [X1 X2 X3 X4]. apply elem_of_dom. eauto. }
  iIntros "?".

  iMod (ghost_map_update with "[$][$]") as "(?&?)".
  iApply "Hpost". iFrame. iExists _,_,_. iFrame.
  iPureIntro.
  inversion Hpure.
  constructor; eauto using coherent_update,dom_le_update.
  { intros. eapply coherent_insert_unrel; eauto.
    apply lookup_lt_Some in H0. lia. }
Qed.

Lemma pstore_ref_spec γ s ρ v :
  {{{
     isnow γ s ρ
  }}}
    pstore_ref v
  {{{ l,
     RET #l;
     isnow γ s ρ ∗ mapsto γ ρ l v
  }}}.
Proof.
  iIntros (?) "Hnow Hpost".
  iDestruct "Hnow" as pat_now.
  iApply wp_fupd.

  wp_apply (pstore_ref_spec with "[$]").
  iIntros (l) "(%Hl&?)".
  iMod (ghost_map_insert (l,ρ) with "[$]") as "(?&?)".
  { destruct Hpure as [X1 X2 X3 X4].
    destruct (M !! (l, ρ)) eqn:Go; last done. exfalso.
    apply X2, elem_of_dom_2 in Go. done. }

  iApply "Hpost". iFrame. iModIntro.
  iExists _,_,_. iFrame.
  iPureIntro.
  inversion Hpure as [X1 X2 X3 X4].
  constructor; eauto using coherent_update,dom_le_update.
  { intros. eapply coherent_insert_unrel; eauto.
    apply lookup_lt_Some in H. lia. }
Qed.

End Go.
