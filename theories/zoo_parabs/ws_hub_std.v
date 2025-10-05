From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  gmultiset
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  int
  option
  optional
  array
  random_round
  domain.
From zoo_parabs Require Export
  base
  ws_hub_std__code.
From zoo_parabs Require Import
  ws_hub_std__types
  ws_queues_public
  waiters.
From zoo Require Import
  options.

Implicit Types b yield killed : bool.
Implicit Types l : location.
Implicit Types v t until pred : val.
Implicit Types vs : gmultiset val.
Implicit Types ws us : list val.
Implicit Types vss : list $ list val.
Implicit Types status : status.
Implicit Types empty : emptiness.

Class WsHubStdG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_hub_std_G_queues_G :: WsQueuesPublicG Σ ;
  #[local] ws_hub_std_G_waiters_G :: WaitersG Σ ;
}.

Definition ws_hub_std_Σ := #[
  ws_queues_public_Σ ;
  waiters_Σ
].
#[global] Instance subG_ws_hub_std_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_hub_std_Σ Σ →
  WsHubStdG Σ.
Proof.
  solve_inG.
Qed.

#[local] Definition consistent vs vss :=
  vs = ⋃+ (list_to_set_disj <$> vss).

#[local] Lemma consistent_alloc sz :
  consistent ∅ (replicate sz []).
Proof.
  symmetry.
  rewrite gmultiset_disj_union_list_empty => vs.
  rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_replicate.
  naive_solver.
Qed.
#[local] Lemma consistent_empty vs vss :
  consistent vs vss →
  vs = ∅ ↔
    ∀ i us,
    vss !! i = Some us →
    us = [].
Proof.
  intros ->.
  rewrite gmultiset_disj_union_list_empty.
  setoid_rewrite elem_of_list_fmap.
  split.
  - intros H i us Hus%elem_of_list_lookup_2.
    rewrite -list_to_set_disj_empty.
    eauto.
  - intros H ? (us & -> & Hus%elem_of_list_lookup).
    rewrite list_to_set_disj_empty.
    naive_solver.
Qed.
#[local] Lemma consistent_push {vs vss i us} v :
  vss !! i = Some us →
  consistent vs vss →
  consistent ({[+v+]} ⊎ vs) (<[i := us ++ [v]]> vss).
Proof.
  intros Hlookup ->.
  rewrite /consistent.
  rewrite list_fmap_insert list_to_set_disj_snoc gmultiset_disj_union_list_insert_disj_union_l //.
  rewrite list_lookup_fmap Hlookup //.
Qed.
#[local] Lemma consistent_remove {vs vss i us} us1 v us2 :
  vss !! i = Some us →
  us = us1 ++ v :: us2 →
  consistent vs vss →
    v ∈ vs ∧
    consistent (vs ∖ {[+v+]}) (<[i := us1 ++ us2]> vss).
Proof.
  intros Hlookup -> ->.
  assert ((list_to_set_disj <$> vss : list $ gmultiset _) !! i = Some $ (list_to_set_disj $ us1 ++ v :: us2)).
  { rewrite list_lookup_fmap Hlookup //. }
  split.
  - apply elem_of_gmultiset_disj_union_list.
    eexists. split.
    + rewrite elem_of_list_lookup. eauto.
    + rewrite list_to_set_disj_app. set_solver.
  - rewrite (gmultiset_disj_union_list_delete' _ i (list_to_set_disj $ us1 ++ v :: us2)) //.
    rewrite /consistent list_fmap_insert gmultiset_disj_union_list_insert //.
    rewrite !list_to_set_disj_app.
    multiset_solver.
Qed.
#[local] Lemma consistent_pop vs vss i us v :
  vss !! i = Some (us ++ [v]) →
  consistent vs vss →
    v ∈ vs ∧
    consistent (vs ∖ {[+v+]}) (<[i := us]> vss).
Proof.
  intros Hlookup Hconsistent.
  eapply (consistent_remove us v []) in Hconsistent; [| done..].
  rewrite app_nil_r // in Hconsistent.
Qed.
#[local] Lemma consistent_steal vs vss i v us :
  vss !! i = Some (v :: us) →
  consistent vs vss →
    v ∈ vs ∧
    consistent (vs ∖ {[+v+]}) (<[i := us]> vss).
Proof.
  intros Hlookup.
  eapply (consistent_remove [] v us); done.
Qed.

Opaque consistent.

Section ws_hub_std_G.
  Context `{ws_hub_std_G : WsHubStdG Σ}.

  Record metadata := {
    metadata_size : nat ;
    metadata_queues : val ;
    metadata_rounds : val ;
    metadata_waiters : val ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec :
    EqDecision metadata.
  Proof.
    solve_decision.
  Qed.
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition inv_inner l : iProp Σ :=
    ∃ killed,
    l.[killed] ↦ #killed.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %killed &
      Hl_killed
    )".
  Definition ws_hub_std_inv t ι sz : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜sz = γ.(metadata_size)⌝ ∗
    l.[queues] ↦□ γ.(metadata_queues) ∗
    l.[rounds] ↦□ γ.(metadata_rounds) ∗
    l.[waiters] ↦□ γ.(metadata_waiters) ∗
    ws_queues_public_inv γ.(metadata_queues) ι γ.(metadata_size) ∗
    array_inv γ.(metadata_rounds) γ.(metadata_size) ∗
    waiters_inv γ.(metadata_waiters) ∗
    inv nroot (inv_inner l).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l{} &
      %γ{} &
      {%Heq{};->} &
      #Hmeta{} &
      -> &
      #Hl{}_queues &
      #Hl{}_rounds &
      #Hl{}_waiters &
      #Hqueues{}_inv &
      #Hrounds{}_inv &
      #Hwaiters{}_inv &
      #Hinv{}
    )".

  Definition ws_hub_std_model t vs : iProp Σ :=
    ∃ l γ vss,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ws_queues_public_model γ.(metadata_queues) vss ∗
    ⌜consistent vs vss⌝.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %vss &
      %Heq &
      Hmeta_ &
      Hqueues_model &
      %Hconsistent
    )".

  Definition ws_hub_std_owner t i status empty : iProp Σ :=
    ∃ l γ ws round n,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ws_queues_public_owner γ.(metadata_queues) i status ws ∗
    ⌜empty = Empty → ws = []⌝ ∗
    array_slice γ.(metadata_rounds) i DfracDiscarded [round] ∗
    random_round_model' round (γ.(metadata_size) - 1) n.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %l{;_} &
      %γ{;_} &
      %ws{} &
      %round{} &
      %n{} &
      %Heq{} &
      Hmeta{;_} &
      Hqueues_owner{} &
      %Hempty{} &
      #Hrounds{} &
      Hround{}
    )".

  #[global] Instance ws_hub_std_model_timeless t vs :
    Timeless (ws_hub_std_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_hub_std_inv_persistent t ι sz :
    Persistent (ws_hub_std_inv t ι sz).
  Proof.
    apply _.
  Qed.

  Lemma ws_hub_std_inv_agree t ι sz1 sz2 :
    ws_hub_std_inv t ι sz1 -∗
    ws_hub_std_inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iSteps.
  Qed.

  Lemma ws_hub_std_owner_exclusive t i status1 empty1 status2 empty2 :
    ws_hub_std_owner t i status1 empty1 -∗
    ws_hub_std_owner t i status2 empty2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-. iClear "Hmeta2".
    iApply (ws_queues_public_owner_exclusive with "Hqueues_owner1 Hqueues_owner2").
  Qed.

  Lemma ws_hub_std_model_empty t ι sz vs :
    ws_hub_std_inv t ι sz -∗
    ws_hub_std_model t vs -∗
    ( [∗ list] i ∈ seq 0 sz,
      ∃ status,
      ws_hub_std_owner t i status Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:inv) (:model) Howners". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iEval (rewrite consistent_empty //). iIntros "%i %us %Hlookup".
    iDestruct (ws_queues_public_inv_model with "Hqueues_inv Hqueues_model") as %Hvss.
    opose proof* (lookup_lt_Some vss i us) as Hi; first done.
    iDestruct (big_sepL_lookup _ _ i with "Howners") as "(%status & Howner)".
    { rewrite lookup_seq. auto with lia. }
    iDestruct "Howner" as "(:owner)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (ws_queues_public_model_owner with "Hqueues_model Hqueues_owner") as "(%us_ & %Hlookup_ & %Hws)". simplify.
    iPureIntro. apply suffix_nil_inv. naive_solver.
  Qed.

  Lemma ws_hub_std_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_std_create #sz
    {{{ t,
      RET t;
      ws_hub_std_inv t ι ₊sz ∗
      ws_hub_std_model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_std_owner t i Nonblocked Empty
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    wp_apply (waiters_create_spec with "[//]") as (waiters) "#Hwaiters_inv".

    wp_smart_apply (array_unsafe_init_spec_disentangled (λ _ round, random_round_model' round (₊sz - 1) (₊sz - 1))) as (v_rounds rounds) "(%Hrounds & Hrounds_model & Hrounds)"; first done.
    { iIntros "!> %i %Hi".
      wp_smart_apply int_positive_part_spec.
      wp_apply (random_round_create_spec' with "[//]"); first lia.
      rewrite Nat2Z.id. assert (₊(sz - 1) = ₊sz - 1) as -> by lia.
      iSteps.
    }
    iDestruct (array_model_to_inv with "Hrounds_model") as "#Hrounds_inv".
    rewrite Hrounds.

    wp_smart_apply (ws_queues_public_create_spec with "[//]") as (queues) "(#Hqueues_inv & Hqueues_model & Hqueues_owner)"; first done.

    wp_block l as "Hmeta" "(Hl_queues & Hl_rounds & Hl_waiters & Hl_killed & _)".
    iMod (pointsto_persist with "Hl_queues") as "#Hl_queues".
    iMod (pointsto_persist with "Hl_rounds") as "#Hl_rounds".
    iMod (pointsto_persist with "Hl_waiters") as "#Hl_waiters".

    pose γ := {|
      metadata_size := ₊sz ;
      metadata_queues := queues ;
      metadata_rounds := v_rounds ;
      metadata_waiters := waiters ;
    |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitL "Hl_killed"; iSteps.
    - iPureIntro. apply consistent_alloc.
    - iMod (array_model_persist with "Hrounds_model") as "Hrounds_model".
      iDestruct (array_model_atomize with "Hrounds_model") as "(_ & Hrounds_model)".
      iDestruct (big_sepL_sep_2 with "Hrounds_model Hrounds") as "Hrounds".
      iDestruct (big_sepL_seq_index_1 with "Hqueues_owner") as "Hqueues_owner"; first done.
      iDestruct (big_sepL_sep_2 with "Hqueues_owner Hrounds") as "H".
      iApply big_sepL_seq_index; first done.
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_hub_std_size_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (array_size_spec_inv with "Hrounds_inv HΦ").
  Qed.

  Lemma ws_hub_std_block_spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty
    }}}
      ws_hub_std_block t #i
    {{{
      RET ();
      ws_hub_std_owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (ws_queues_public_block_spec with "[$Hqueues_inv $Hqueues_owner]"); first done.
    iSteps.
  Qed.

  Lemma ws_hub_std_unblock_spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty
    }}}
      ws_hub_std_unblock t #i
    {{{
      RET ();
      ws_hub_std_owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (ws_queues_public_unblock_spec with "[$Hqueues_inv $Hqueues_owner]"); first done.
    iSteps.
  Qed.

  Lemma ws_hub_std_killed_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_killed t
    {{{ killed,
      RET #killed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_std_notify_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (waiters_notify_spec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_std_notify_all_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_apply (ws_hub_std_size_spec) as "_"; first iSteps.
    wp_load.
    wp_apply (waiters_notify_many_spec with "Hwaiters_inv HΦ"); first lia.
  Qed.

  Lemma ws_hub_std_push_spec t ι sz i i_ empty v :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_push t #i v @ ↑ι
    <<<
      ws_hub_std_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_std_owner t i_ Nonblocked Nonempty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    awp_apply (ws_queues_public_push_spec with "[$Hqueues_inv $Hqueues_owner]") without "Hround"; first done.
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueues_model"; first iSteps. iIntros "%us (%Hlookup & Hqueues_model)".
    iSplitL.
    { iFrameSteps. iPureIntro. apply consistent_push; done. }
    iIntros "!> HΦ !> Hqueues_owner Hround {%}".

    wp_smart_apply ws_hub_std_notify_spec; iSteps.
  Qed.

  Lemma ws_hub_std_pop_spec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    awp_smart_apply (ws_queues_public_pop_spec with "[$Hqueues_inv $Hqueues_owner]") without "Hround"; first done.
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueues_model"; first iSteps. iIntros ([v |] us) "Ho".

    - iDestruct "Ho" as "(% & %Hlookup & %Hws & <- & Hqueues_model)".
      iExists (Some v).
      iSplitL.
      { eapply consistent_pop in Hconsistent; last done.
        iExists (vs ∖ {[+v+]}). iFrameSteps; iPureIntro.
        - multiset_solver.
        - naive_solver.
      }
      iSteps. iPureIntro.
      intros ->. exfalso.
      opose proof* Hempty as ->; first done.
      eapply suffix_cons_nil_inv, suffix_app_l. done.

    - iDestruct "Ho" as "(%Hlookup & -> & Hqueues_model)".
      iExists None. iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_std_try_steal_once_spec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_try_steal_once t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked empty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec_cell with "Hrounds") as "_"; first lia.
    wp_smart_apply (random_round_reset_spec' with "Hround") as "Hround".
    wp_load.

    iDestruct (ws_queues_public_inv_owner with "Hqueues_inv Hqueues_owner") as %?.
    awp_apply (ws_queues_public_steal_as_spec with "[$Hqueues_inv $Hqueues_owner $Hround]"); [lia.. |].
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueues_model"; first iSteps. iIntros ([v |]) "Ho".

    - iDestruct "Ho" as "(%j & %ws' & %Hj & %Hlookup & Hqueues_model)".
      iExists (Some v).
      iSplitL.
      { eapply consistent_steal in Hconsistent; last done.
        iExists (vs ∖ {[+v+]}). iFrameSteps; iPureIntro.
        - multiset_solver.
        - naive_solver.
      }
      iSteps.

    - iExists None. iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_std_try_steal_spec P t ι sz i i_ empty yield max_round until :
    i = ⁺i_ →
    (0 ≤ max_round)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty ∗
      □ WP until () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_try_steal t #i #yield #max_round until @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_std_model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked empty ∗
      if o is Anything then P else True
    >>>.
  Proof.
    intros ->.
    iLöb as "HLöb" forall (max_round).

    iIntros "%Hmax_round %Φ ((:inv) & (:owner) & #Huntil) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! Nothing with "Hmodel").
      iSteps.

    - awp_smart_apply (ws_hub_std_try_steal_once_spec with "[Hqueues_owner Hround]"); [done | iSteps |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Something v). iFrameSteps.

      + iLeft. iFrame.
        iIntros "HΦ !> Howner". clear- Hmax_round Hcase.

        wp_smart_apply (wp_wand with "Huntil") as (res) "(%b & -> & HP)".
        destruct b; wp_pures.

        * iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
          iApply ("HΦ" $! Anything with "Hmodel [$Howner $HP]").

        * wp_bind (if: _ then _ else _)%E.
          wp_apply (wp_wand itype_unit) as (res) "->".
          { destruct yield; iSteps. }
          wp_smart_apply ("HLöb" with "[] [$Howner] HΦ"); iSteps.
  Qed.

  #[local] Lemma ws_hub_std_steal_until_0_spec P t ι sz i i_ empty pred :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_until_0 t #i pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked empty ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & #Hpred) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_smart_apply (ws_hub_std_try_steal_once_spec with "[$Hinv $Howner]"); first done.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrameSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner {%}".

      wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
      destruct b; wp_pures.

      + iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
        iApply ("HΦ" $! None with "Hmodel [$Howner $HP]").

      + wp_apply domain_yield_spec.
        wp_smart_apply ("HLöb" with "Howner HΦ").
  Qed.
  #[local] Lemma ws_hub_std_steal_until_1_spec P t ι sz i i_ empty max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_until_1 t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked empty ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_try_steal_spec with "[$Hinv $Howner $Hpred]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame.
      iIntros "HΦ !> (Howner & _) {%}".

      wp_smart_apply (ws_hub_std_steal_until_0_spec with "[$Hinv $Howner $Hpred] HΦ"); first done.

    - iRight. iExists None. iFrameSteps.

    - iRight. iExists (Some v). iFrameSteps.
  Qed.
  Lemma ws_hub_std_steal_until_spec P t ι sz i i_ empty max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_until t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked empty ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_block_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_smart_apply (ws_hub_std_steal_until_1_spec with "[$Hinv $Howner $Hpred]"); [done.. |].
    iApply (atomic_update_wand with "HΦ"). iIntros "_ %o HΦ (Howner & HP)".
    wp_smart_apply (ws_hub_std_unblock_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_pures.
    iApply ("HΦ" with "[$Howner $HP]").
  Qed.

  #[local] Lemma ws_hub_std_steal_aux_spec P t ι sz i i_ empty max_round_noyield max_round_yield until :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty ∗
      □ WP until () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_aux t #i #max_round_noyield #max_round_yield until @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_std_model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked empty ∗
      if o is Anything then P else True
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner & #Huntil) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_try_steal_spec with "[$Hinv $Howner $Huntil]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame.
      iIntros "HΦ !> (Howner & _)". clear- Hmax_round_yield.

      wp_smart_apply (ws_hub_std_try_steal_spec with "[$Hinv $Howner $Huntil] HΦ"); done.

    - iRight. iExists Anything. iFrameSteps.

    - iRight. iExists (Something v). iFrameSteps.
  Qed.
  #[local] Lemma ws_hub_std_steal_0_spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked empty
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_0 t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked empty
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_smart_apply (ws_hub_std_steal_aux_spec True with "[$Hinv $Howner]"); [done.. | |].
    { iModIntro.
      wp_smart_apply (ws_hub_std_killed_spec with "Hinv") as (killed) "_".
      iSteps. destruct killed; iSteps.
    }
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame.
      iIntros "HΦ !> (Howner & _) {%}".

      iDestruct "Hinv" as "(:inv)".

      wp_load.
      wp_smart_apply (waiters_prepare_wait_spec with "Hwaiters_inv") as (waiter) "Hwaiter".

      awp_smart_apply (ws_hub_std_try_steal_once_spec with "[$Howner]") without "Hwaiter"; [done.. | iSteps |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

      + iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
        iRight. iExists (Some v).
        iSplitL "Hmodel". { iFrameSteps. }
        iIntros "HΦ !> Howner Hwaiter {%}".

        wp_smart_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
        wp_pures.
        iApply ("HΦ" with "Howner").

      + iLeft. iFrame.
        iIntros "HΦ !> Howner Hwaiter {%}".

        wp_smart_apply ws_hub_std_killed_spec as ([]) "_"; first iSteps.

        * wp_smart_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
          wp_pures.
          iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
          iApply ("HΦ" $! None with "Hmodel Howner").

        * wp_smart_apply (waiters_commit_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
          wp_smart_apply ("HLöb" with "Howner HΦ").

    - iRight. iExists None. iFrameSteps.

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v).
      iSplitL "Hmodel". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma ws_hub_std_steal_spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked empty
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_block_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_smart_apply (ws_hub_std_steal_0_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (atomic_update_wand with "HΦ"). iIntros "_ %o HΦ Howner".
    wp_smart_apply (ws_hub_std_unblock_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_pures.
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_std_kill_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_kill t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_pures.

    wp_bind (_ <-{killed} _)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_store.
    iSplitR "HΦ". { iSteps. }
    iIntros "!> {%}".

    wp_smart_apply ws_hub_std_notify_all_spec as "_"; first iSteps.
    iSteps.
  Qed.
End ws_hub_std_G.

#[global] Opaque ws_hub_std_inv.
#[global] Opaque ws_hub_std_model.
#[global] Opaque ws_hub_std_owner.

Section ws_hub_std_G.
  Context `{ws_hub_std_G : WsHubStdG Σ}.

  Lemma ws_hub_std_pop_steal_until_spec P t ι sz i i_ empty max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_pop_steal_until t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | empty,
      RET o;
      ws_hub_std_owner t i_ Nonblocked empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝ ∗
        P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrameSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield.

      wp_smart_apply (ws_hub_std_steal_until_spec with "[$Hinv $Howner $Hpred]"); [done.. |].
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ (Howner & HP)".
      iApply ("HΦ" with "[- $Howner]").
      destruct o; iFrameSteps.
  Qed.

  Lemma ws_hub_std_pop_steal_spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_pop_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | empty,
      RET o;
      ws_hub_std_owner t i_ Nonblocked empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_std_steal_spec with "[$Hinv $Howner]"); [done.. |].
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ Howner".
      iApply ("HΦ" with "[$Howner]").
      destruct o; iFrameSteps.
  Qed.
End ws_hub_std_G.

From zoo_parabs Require
  ws_hub_std__opaque.
