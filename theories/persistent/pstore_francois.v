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

Record gnames := mkg  {γ1 : gname; γ2 : gname}.

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

Lemma dom_le_update l ρ v M :
  dom_le ρ M ->
  dom_le ρ (<[(l, ρ):=v]> M).
Proof.
  intros Hd.
  intros ??. rewrite dom_insert_L elem_of_union elem_of_singleton.
  intros [X|X]; first naive_solver by lia.
  apply Hd in X. lia.
Qed.

Definition interp_store (γ:gnames) ρ (σ:gmap location val) : iProp Σ :=
  [∗ map] l ↦ v ∈ σ, mapsto γ ρ l v.

Lemma interp_store_disj γ ρ σ1 σ2 :
   interp_store γ ρ σ1 -∗ interp_store γ ρ σ2 -∗ ⌜σ1 ##ₘ σ2⌝.
Proof.
  rewrite /interp_store.
  iIntros "E1 E2". iIntros (l).
  destruct (σ1 !! l) eqn:X1, (σ2 !! l) eqn:X2; try done.
  iDestruct (big_sepM_lookup with "[$]") as "?". done.
  iDestruct (big_sepM_lookup with "[$]") as "?". done.
  iDestruct (ghost_map_elem_frac_ne with "[$][$]") as "%".
  { intros F. apply frac_valid in F. by compute in F. }
  { exfalso. naive_solver. }
Qed.

(* For now, using the frac one of all points-tos, for the union to distribute.
   We can do better. *)
Lemma interp_store_union1 γ ρ σ1 σ2 :
  interp_store γ ρ σ1 -∗ interp_store γ ρ σ2 -∗
  interp_store γ ρ (σ1 ∪ σ2).
Proof.
  iIntros "? ?".
  iDestruct (interp_store_disj with "[$][$]") as "%".
  iApply big_sepM_union. done. by iFrame.
Qed.

Lemma interp_store_union2 γ ρ σ1 σ2 :
  σ1 ##ₘ σ2 ->
  interp_store γ ρ (σ1 ∪ σ2) -∗
  interp_store γ ρ σ1 ∗ interp_store γ ρ σ2.
Proof.
  iIntros (?) "?". iApply big_sepM_union. done. by iFrame.
Qed.

Lemma interp_store_empty γ ρ :
  interp_store γ ρ ∅ ≡ True%I.
Proof.
  rewrite /interp_store big_sepM_empty //.
Qed.

Lemma interp_store_singleton γ ρ l v :
  interp_store γ ρ {[l:=v]} ≡ mapsto γ ρ l v.
Proof.
  rewrite /interp_store big_sepM_singleton //.
Qed.

Definition transportable γ (Φ:timestamp -> iProp Σ) : iProp Σ :=
  ∀ (ρ:timestamp),
    (Φ ρ -∗ ∃ (σ:gmap location val),
        (interp_store γ ρ σ ∗
         (interp_store γ ρ σ -∗ Φ ρ) ∗
         (∀ ρ', interp_store γ ρ' σ -∗ Φ ρ'))).

Lemma transportable_one γ l v :
  ⊢ transportable γ (fun ρ => mapsto γ ρ l v).
Proof.
  iIntros (ρ). iIntros "?". iExists {[l:=v]}.
  rewrite !interp_store_singleton. iIntros. iFrame.
  iSplitR. iSteps. iIntros (?). rewrite interp_store_singleton. iSteps.
Qed.

Lemma transportable_persistent γ Φ :
  ⊢ transportable γ (fun _ => □ Φ)%I.
Proof.
  iIntros (ρ). iIntros "#?". iExists ∅.
  rewrite !interp_store_empty left_id.
  iSplit. by iFrame "#". iIntros (?) "_". by iFrame "#".
Qed.

Lemma transportable_star γ Φ1 Φ2 :
  transportable γ Φ1 -∗
  transportable γ Φ2 -∗
  transportable γ (fun ρ => Φ1 ρ ∗ Φ2 ρ)%I.
Proof.
  iIntros "F1 F2". iIntros (ρ) "(E1&E2)".
  iDestruct ("F1" with "E1") as "[%σ1 (X11&X12&X13)]".
  iDestruct ("F2" with "E2") as "[%σ2 (X21&X22&X23)]".
  iDestruct (interp_store_disj with "X11 X21") as "%".
  iDestruct (interp_store_union1 with "X11 X21") as "?".
  iExists _. iFrame. iSplitL "X12 X22".
  { iIntros "?".
    iDestruct (interp_store_union2 with "[$]") as "(?&?)". done.
    iSteps. }
  { iIntros (?) "?".
    iDestruct (interp_store_union2 with "[$]") as "(?&?)". done.
    iSteps. }
Qed.

Lemma transportable_exists {A} γ Φ :
  (∀ (x:A), transportable γ (Φ x) )-∗
  transportable γ (fun ρ => ∃ x, Φ x ρ)%I.
Proof.
  iIntros "F". iIntros (?) "[%x H]".
  iDestruct ("F" with "[$]") as "[% (?&X1&X2)]".
  iExists _. iFrame. iSplitL "X1"; iSteps.
Qed.

(* XXX I don't know how to prove this. *)
Lemma transportable_forall {A} γ Φ :
  (∀ (x:A), transportable γ (Φ x) )-∗
  transportable γ (fun ρ => ∀ x, Φ x ρ)%I.
Abort.


Definition submap (ρ:timestamp) (σ:gmap location val) (M:gmap (location*timestamp) val) :=
  forall (l:location) (v:val), σ !! l = Some v -> M !! (l,ρ) = Some v.

Lemma use_interp_store γ ρ σ M :
  ghost_map_auth γ.(γ1) 1%Qp M -∗
  interp_store γ ρ σ -∗
  ⌜submap ρ σ M⌝.
Proof.
  iIntros "Ha Hf".
  iIntros (l v Hlv).
  iDestruct (big_sepM_lookup with "Hf") as "?". done.
  iDestruct (ghost_map_lookup with "[$][$]") as "%". done.
Qed.


Definition news (ρ:timestamp) (σ:gmap location val)  : gmap (location*timestamp) val :=
  kmap (fun l => (l,ρ)) σ.

Lemma pureinv_disj_news ρ σ M xs μ :
  pureinv ρ σ M xs ->
  news (S ρ) μ ##ₘ M.
Proof.
  intros [X1 X2 X3 X4]. apply map_disjoint_spec.
  intros (l,ρ') ? ? Hμ HM.
  rewrite /news in Hμ.
  apply lookup_kmap_Some in Hμ.
  2:apply _. destruct Hμ as (l'&X&Hμ). inversion X. subst.
  apply elem_of_dom_2,X4 in HM. lia.
Qed.

Lemma news_interp γ ρ μ :
  ([∗ map] k↦v ∈ news ρ μ, k ↪[γ1 γ] v) -∗
  interp_store γ ρ μ.
Proof.
  iIntros "Hm".
  iInduction (μ) as [|] "IH" using map_ind.
  { by iApply big_sepM_empty. }
  { rewrite /interp_store.
    rewrite /news kmap_insert !big_sepM_insert //.
    { apply lookup_kmap_None. apply _. naive_solver. }
    iDestruct "Hm" as "(?&?)". iFrame. iSteps. }
Qed.

Lemma dom_le_bump ρ μ M :
  dom_le ρ M ->
  dom_le (S ρ) (news (S ρ) μ ∪ M).
Proof.
  intros Hd.
  intros ??. rewrite dom_union_L elem_of_union.
  intros [X|X].
  { rewrite /news dom_kmap in X. apply elem_of_map_1 in X.
    naive_solver by lia. }
  { apply Hd in X. lia. }
Qed.

Lemma lookup_news_Some ρ μ l ρ' v :
  news ρ μ !! (l, ρ') = Some v ->
  ρ' = ρ /\ μ !! l = Some v .
Proof.
  rewrite /news lookup_kmap_Some. naive_solver.
Qed.

Lemma coherent_insert_bump M ρ σ :
  news (S ρ) σ ##ₘ M ->
  dom_le ρ M ->
  coherent ρ σ M ->
  coherent (S ρ) σ (news (S ρ) σ ∪ M).
Proof.
  intros ? Hdom Hco l' ? E.
  rewrite lookup_union_Some in E. done.
  destruct E as [E|E].
  { apply lookup_news_Some in E. naive_solver. }
  { apply elem_of_dom_2,Hdom in E. lia. }
Qed.

Lemma coherent_insert_unrel ρ' ρ σ M μ :
  news ρ μ ##ₘ M ->
  ρ ≠ ρ' ->
  coherent ρ' σ M ->
  coherent ρ' σ (news ρ μ ∪ M).
Proof.
  intros ? Hcoh. intros ? l' v' E.
  rewrite lookup_union_Some in E. done.
  destruct E as [E|E].
  { apply lookup_news_Some in E. naive_solver. }
  { naive_solver. }
Qed.


Definition populate γ s ρ ρ' : iProp Σ :=
  ∀ ρ0 Φ, isnow γ s ρ0 ∗ transportable γ Φ ∗ Φ ρ -∗ isnow γ s ρ0 ∗ Φ ρ ∗ Φ ρ'.

Lemma interp_store_subseteq γ ρ σ σ' :
  σ' ⊆ σ ->
  interp_store γ ρ σ -∗
  interp_store γ ρ σ'.
Proof.
  iIntros (?) "?".
  by iApply (big_sepM_subseteq with "[$]").
Qed.

Lemma pstore_capture_spec γ s ρ :
    {{{
      isnow γ s ρ
    }}}
      pstore_capture s
    {{{ t ρ',
      RET t;
      isnow γ s ρ' ∗ snapshot γ s t ρ ∗ populate γ s ρ ρ'
    }}}.
Proof.
  iIntros (?) "Hnow Hpost".
  iDestruct "Hnow" as pat_now.
  iApply wp_fupd.
  wp_apply (pstore_capture_spec with "Hstore").
  iIntros (t) "(Hstore&#X)".
  iMod (mono_list_update_app [σ] with "Hsnap") as "Hsnap".
  iDestruct (mono_list_lb_get with "Hsnap") as "#HX".
  iDestruct (mono_list_elem_get (length xs) with "HX") as "#Hgo".
  { rewrite lookup_app_r // Nat.sub_diag //. }
  iClear "HX".

  assert (news (S ρ) σ ##ₘ M) by (eauto using pureinv_disj_news).
  iMod (ghost_map_insert_big (news (S ρ) σ) with "[$]") as "(?&Hμ')".
  { done. }

  iModIntro. iApply ("Hpost" $! t (S ρ)).
  iSplitR "Hμ'".
  { iExists _,_,_. iFrame. iPureIntro.
  { generalize Hpure. intros [X1 X2 X3 X4].
    constructor; eauto using coherent_insert_bump,dom_le_bump.
    { rewrite app_length //. simpl. lia. }
    { intros ??. rewrite lookup_app_Some. intros [?|(?&?)].
      { eapply coherent_insert_unrel; eauto.
        { apply lookup_lt_Some in H0. lia. } }
      { apply list_lookup_singleton_Some in H1. destruct H1 as (?&<-).
        assert (ρ' = ρ) as -> by lia.
        eauto using coherent_insert_unrel. } } } }
  iSplitR.
  { destruct Hpure. subst. iExists _. iFrame "#". }
  { erewrite <- pu1. 2:done. iIntros (ρ0 ϕ) "(Hnow&HT&?)".
    iDestruct ("HT" with "[$]") as "[%σ' (X1&X2&X3)]".
    clear dependent M. rename σ into σ_old. rename xs into xs_old.
    iDestruct "Hnow" as pat_now.
    iDestruct (use_interp_store with "Hpointsto [$]") as "%".
    iSpecialize ("X2" with "[$]"). iFrame.
    iAssert (⌜σ' ⊆ σ_old⌝)%I as "%Hsub".
    { iDestruct (mono_list_lookup with "Hsnap [$]") as "%".
      iPureIntro.
      rewrite map_subseteq_spec. iIntros (l v Hl).
      apply H in Hl. destruct Hpure as [X1 X2 X3 X4]. naive_solver. }
    iDestruct (news_interp with "[$]") as "?".
    iDestruct (interp_store_subseteq with "[$]") as "?". done.
    iSpecialize ("X3" with "[$]"). iFrame. iExists _,_,_. by iFrame. }
Qed.

Lemma pstore_restore_spec γ s t ρ0 ρ :
    {{{
      isnow γ s ρ0 ∗ snapshot γ s t ρ
    }}}
      pstore_restore s t
    {{{ ρ',
      RET ();
      isnow γ s ρ' ∗ populate γ s ρ ρ'
    }}}.
Proof.
  iIntros (?) "(Hnow&Ht) Hpost".
  iDestruct "Hnow" as pat_now.
  iApply wp_fupd. rename σ into σ0.

  iDestruct "Ht" as "[%σ (Ht&?)]".
  wp_apply (pstore_restore_spec with "[$]").
  iIntros "Hstore".
  iApply ("Hpost" $! (S ρ0)).

  iDestruct (mono_list_lookup with "Hsnap [$]") as "%".
  iMod (mono_list_update_app [σ0] with "Hsnap") as "Hsnap".
  iDestruct (mono_list_lb_get with "Hsnap") as "#HX".
  iDestruct (mono_list_elem_get (length xs) with "HX") as "#Hgo".
  { rewrite lookup_app_r // Nat.sub_diag //. }

  assert (news (S ρ0) σ ##ₘ M) by (eauto using pureinv_disj_news).
  iMod (ghost_map_insert_big (news (S ρ0) σ) with "[$]") as "(?&Hμ')".
  { done. }

  iModIntro. iSplitR "Hμ'".
  { iExists _,_,_. iFrame.
    iPureIntro.
    destruct Hpure as [X1 X2 X3 X4].
    constructor; eauto using dom_le_bump.
    { rewrite app_length. simpl. lia. }
    { intros l' v' E.
      rewrite lookup_union_Some in E. done.
      destruct E as [E|E].
      { apply lookup_news_Some in E. naive_solver. }
      { exfalso. apply elem_of_dom_2,X4 in E. lia. } }
    { intros ρ' σ'. rewrite lookup_app_Some. intros [X|(?&X)].
      { eapply coherent_insert_unrel; eauto.
        apply lookup_lt_Some in X. lia. }
      { apply list_lookup_singleton_Some in X. destruct X as (?&<-).
        assert (ρ' = ρ0) as -> by lia.
        eauto using coherent_insert_unrel. } } }
  { erewrite <- pu1. 2:done. iIntros (? ϕ) "(Hnow&HT&?)".
    iDestruct ("HT" with "[$]") as "[%σ' (X1&X2&X3)]".
    clear dependent M. rename σ into σ_old. rename xs into xs_old.
    iDestruct "Hnow" as pat_now.
    iDestruct (use_interp_store with "Hpointsto [$]") as "%".
    iSpecialize ("X2" with "[$]"). iFrame.
    iAssert (⌜σ' ⊆ σ_old⌝)%I as "%Hsub".
    { iDestruct (mono_list_lookup with "Hsnap [$]") as "%".
      iDestruct (mono_list_lb_valid with "[$][$]") as "%Hprefix".
      iPureIntro.
      rewrite map_subseteq_spec. iIntros (l v Hl).
      apply H0 in Hl. destruct Hpure as [X1 X2 X3 X4].
      assert (xs_old !! ρ = xs !! ρ).
      { apply prefix_lookup_lt. apply lookup_lt_Some in H. done. eauto using prefix_app_l. }
      rewrite H2 in H. apply X3 in H. naive_solver. }
    iDestruct (news_interp with "[$]") as "?".
    iDestruct (interp_store_subseteq with "[$]") as "?". done.
    iSpecialize ("X3" with "[$]"). iFrame. iExists _,_,_. by iFrame. }
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

Lemma coherent_insert_unrel_one ρ' ρ σ M l v :
  ρ ≠ ρ' ->
  coherent ρ' σ M ->
  coherent ρ' σ (<[(l, ρ):=v]> M).
Proof.
  intros Hcoh. intros ? l' v'.
  rewrite lookup_insert_case. intros E.
  case_decide; naive_solver.
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
  { intros. eapply coherent_insert_unrel_one; eauto.
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
  { intros. eapply coherent_insert_unrel_one; eauto.
    apply lookup_lt_Some in H. lia. }
Qed.

Lemma pstore_create_spec :
  {{{ True }}}
    pstore_create ()
  {{{ s,
      RET s;
      ∃ γ ρ, isnow γ s ρ
  }}}.
Proof.
  iIntros (?) "_ Hpost".
  iApply wp_fupd.
  wp_apply pstore_create_spec. done.
  iIntros (s) "Hs".
  iApply "Hpost".
  iMod (ghost_map_alloc ∅) as "[%γ1 (?&_)]".
  iMod (mono_list_alloc nil) as "[%γ2 ?]".
  iModIntro. iExists (mkg γ1 γ2), 0.
  iExists ∅,∅,nil. simpl. iFrame.
  iPureIntro. constructor; eauto.
  { intros ??. set_solver. }
  { intros ??. set_solver. }
  { intros ??. set_solver. }
Qed.

End Go.
