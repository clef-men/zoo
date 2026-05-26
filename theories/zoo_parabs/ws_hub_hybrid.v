From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  gmultiset
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.ghost_list.
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
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Export
  base
  ws_hub_hybrid__code.
From zoo_parabs Require Import
  ws_hub_hybrid__types
  ws_bdeques_public
  waiters.
From zoo Require Import
  options.

Implicit Types b yield closed : bool.
Implicit Types num_active : Z.
Implicit Types 𝑡 : location.
Implicit Types v t notification notify pred : val.
Implicit Types vs : gmultiset val.
Implicit Types ws us vs_queue : list val.
Implicit Types vss : list $ list val.
Implicit Types status : status.
Implicit Types empty : emptiness.

Class WsHubHybridG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] ws_hub_hybrid_G_deques_G :: WsBdequesPublicG Σ
  ; #[local] ws_hub_hybrid_G_queue_G :: MpmcQueue1G Σ
  ; #[local] ws_hub_hybrid_G_waiters_G :: WaitersG Σ
  ; #[local] ws_hub_hybrid_G_emptiness_G :: GhostListG Σ emptiness
  }.

Definition ws_hub_hybrid_Σ :=
  #[ws_bdeques_public_Σ
  ; mpmc_queue_1_Σ
  ; waiters_Σ
  ; ghost_list_Σ emptiness
  ].
#[global] Instance subG_ws_hub_hybrid_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_hub_hybrid_Σ Σ →
  WsHubHybridG Σ.
Proof.
  solve_inG.
Qed.

Section consistent.
  #[local] Definition consistent vs vss vs_queue :=
    vs =
      ⋃+ (list_to_set_disj <$> vss) ⊎
      list_to_set_disj vs_queue.

  #[local] Lemma consistent_alloc sz :
    consistent ∅ (replicate sz []) [].
  Proof.
    rewrite /consistent fmap_replicate gmultiset_disj_union_list_replicate_empty //.
  Qed.

  #[local] Lemma consistent_empty vs vss vs_queue :
    consistent vs vss vs_queue →
    vs = ∅ ↔
      ( ∀ i us,
        vss !! i = Some us →
        us = []
      ) ∧
      vs_queue = [].
  Proof.
    intros ->.
    rewrite gmultiset_disj_union_empty.
    rewrite gmultiset_disj_union_list_empty.
    setoid_rewrite list_elem_of_fmap.
    rewrite list_to_set_disj_empty.
    split.
    all: intros (H & ->); split; last done.
    - intros i us Hus%list_elem_of_lookup_2.
      rewrite -list_to_set_disj_empty.
      eauto.
    - intros ? (us & -> & Hus%list_elem_of_lookup).
      rewrite list_to_set_disj_empty.
      naive_solver.
  Qed.

  #[local] Lemma consistent_deque_push {vs vss vs_queue i us} v :
    vss !! i = Some us →
    consistent vs vss vs_queue →
    consistent ({[+v+]} ⊎ vs) (<[i := us ++ [v]]> vss) vs_queue.
  Proof.
    intros Hlookup ->.
    rewrite /consistent.
    rewrite assoc. f_equal.
    rewrite list_fmap_insert list_to_set_disj_snoc gmultiset_disj_union_list_insert_disj_union_l //.
    rewrite list_lookup_fmap Hlookup //.
  Qed.
  #[local] Lemma consistent_deque_remove {vs vss vs_queue i us} us1 v us2 :
    vss !! i = Some us →
    us = us1 ++ v :: us2 →
    consistent vs vss vs_queue →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us1 ++ us2]> vss) vs_queue.
  Proof.
    intros Hlookup -> Hconsistent.
    exists (vs ∖ {[+v+]}).
    rewrite {}Hconsistent.
    assert ((list_to_set_disj <$> vss : list $ gmultiset _) !! i = Some $ (list_to_set_disj $ us1 ++ v :: us2)).
    { rewrite list_lookup_fmap Hlookup //. }
    split.
    - apply gmultiset_disj_union_difference'.
      { apply elem_of_gmultiset_disj_union_l.
        apply elem_of_gmultiset_disj_union_list.
        eexists. split.
        - rewrite list_elem_of_lookup. eauto.
        - rewrite list_to_set_disj_app. set_solver.
      }
    - rewrite (gmultiset_disj_union_list_delete' _ i (list_to_set_disj $ us1 ++ v :: us2)) //.
      rewrite /consistent list_fmap_insert gmultiset_disj_union_list_insert //.
      rewrite !list_to_set_disj_app.
      multiset_solver.
  Qed.
  #[local] Lemma consistent_deque_pop vs vss vs_queue i us v :
    vss !! i = Some (us ++ [v]) →
    consistent vs vss vs_queue →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us]> vss) vs_queue.
  Proof.
    intros Hlookup Hconsistent.
    eapply (consistent_deque_remove us v []) in Hconsistent as (vs' & -> & Hconsistent). 2-3: done.
    rewrite app_nil_r in Hconsistent.
    eauto.
  Qed.
  #[local] Lemma consistent_deque_steal vs vss vs_queue i v us :
    vss !! i = Some (v :: us) →
    consistent vs vss vs_queue →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us]> vss) vs_queue.
  Proof.
    intros Hlookup.
    eapply (consistent_deque_remove [] v us) => //.
  Qed.

  #[local] Lemma consistent_queue_push {vs vss vs_queue} v :
    consistent vs vss vs_queue →
    consistent ({[+v+]} ⊎ vs) vss (vs_queue ++ [v]).
  Proof.
    intros ->.
    rewrite /consistent.
    rewrite (comm (⊎)) -assoc. f_equal.
    rewrite list_to_set_disj_app list_to_set_disj_cons right_id (comm (⊎)) //.
  Qed.
  #[local] Lemma consistent_queue_pop vs vss v vs_queue :
    consistent vs vss (v :: vs_queue) →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' vss vs_queue.
  Proof.
    intros ->.
    eexists. split.
    - rewrite assoc (comm (⊎) _ {[+_+]}) -assoc //.
    - done.
  Qed.
End consistent.

Opaque consistent.

Section ws_hub_hybrid_G.
  Context `{ws_hub_hybrid_G : WsHubHybridG Σ}.

  Implicit Types P P_notification P_pred Q Q_pred : iProp Σ.

  Record metadata :=
    { metadata_size : nat
    ; metadata_deques : val
    ; metadata_rounds : val
    ; metadata_queue : val
    ; metadata_waiters : val
    ; metadata_emptiness : gname
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

  #[local] Definition emptiness_auth' γ_emptiness sz vs_queue : iProp Σ :=
    ∃ emptys,
    ghost_list_auth γ_emptiness emptys ∗
    ⌜length emptys = sz⌝ ∗
    ⌜ vs_queue = []
    ∨ ∃ i,
      emptys !! i = Some Nonempty
    ⌝.
  #[local] Definition emptiness_auth γ :=
    emptiness_auth' γ.(metadata_emptiness) γ.(metadata_size).
  #[local] Instance : CustomIpat "emptiness_auth" :=
    " ( %emptys
      & Hauth
      & %Hemptys
      & %Hemptiness
      )
    ".
  #[local] Definition emptiness_at' γ_emptiness i :=
    ghost_list_at γ_emptiness i (DfracOwn 1).
  #[local] Definition emptiness_at γ :=
    emptiness_at' γ.(metadata_emptiness).

  #[local] Definition inv_inner 𝑡 : iProp Σ :=
    ∃ num_active,
    𝑡.[num_active] ↦ #num_active.
  #[local] Instance : CustomIpat "inv_inner" :=
    " ( %num_active
      & H𝑡_num_active
      )
    ".
  Definition ws_hub_hybrid_inv t ι sz : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ⌜sz = γ.(metadata_size)⌝ ∗
    𝑡.[deques] ↦□ γ.(metadata_deques) ∗
    𝑡.[rounds] ↦□ γ.(metadata_rounds) ∗
    𝑡.[queue] ↦□ γ.(metadata_queue) ∗
    𝑡.[waiters] ↦□ γ.(metadata_waiters) ∗
    ws_bdeques_public_inv γ.(metadata_deques) ι γ.(metadata_size) ∗
    array_inv γ.(metadata_rounds) γ.(metadata_size) ∗
    mpmc_queue_1_inv γ.(metadata_queue) ι ∗
    waiters_inv γ.(metadata_waiters) sz ∗
    inv nroot (inv_inner 𝑡).
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{}
      & ->
      & #H𝑡{}_deques
      & #H𝑡{}_queue
      & #H𝑡{}_rounds
      & #H𝑡{}_waiters
      & #Hdeques{}_inv
      & #Hrounds{}_inv
      & #Hqueue{}_inv
      & #Hwaiters{}_inv
      & #Hinv{}
      )
    ".

  Definition ws_hub_hybrid_model t vs : iProp Σ :=
    ∃ 𝑡 γ vss vs_queue,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ws_bdeques_public_model γ.(metadata_deques) vss ∗
    mpmc_queue_1_model γ.(metadata_queue) vs_queue ∗
    ⌜consistent vs vss vs_queue⌝ ∗
    emptiness_auth γ vs_queue.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡_
      & %γ_
      & %vss
      & %vs_queue
      & %Heq
      & Hmeta_
      & Hdeques_model
      & Hqueue_model
      & %Hconsistent
      & Hemptiness_auth
      )
    ".

  Definition ws_hub_hybrid_owner t i status empty : iProp Σ :=
    ∃ 𝑡 γ ws round n,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ws_bdeques_public_owner γ.(metadata_deques) i status ws ∗
    ⌜empty = Empty → ws = []⌝ ∗
    array_slice γ.(metadata_rounds) i DfracDiscarded [round] ∗
    random_round_model' round (γ.(metadata_size) - 1) n ∗
    emptiness_at γ i empty.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{;_}
      & %γ{;_}
      & %ws{}
      & %round{}
      & %n{}
      & %Heq{}
      & Hmeta{;_}
      & Hdeques_owner{}
      & %Hempty{}
      & #Hrounds{}
      & Hround{}
      & Hemptiness_at{_{}}
      )
    ".

  #[global] Instance ws_hub_hybrid_model_timeless t vs :
    Timeless (ws_hub_hybrid_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_hub_hybrid_inv_persistent t ι sz :
    Persistent (ws_hub_hybrid_inv t ι sz).
  Proof.
    apply _.
  Qed.

  #[local] Lemma emptiness_alloc sz :
    ⊢ |==>
      ∃ γ_emptiness,
      emptiness_auth' γ_emptiness sz [] ∗
      [∗ list] i ∈ seq 0 sz,
        emptiness_at' γ_emptiness i Empty.
  Proof.
    iMod ghost_list_alloc as "(%γ_emptiness & $ & Hats)".
    iDestruct (big_sepL_replicate_1 with "Hats") as "$".
    iSteps. iPureIntro. simpl_length.
  Qed.
  #[local] Lemma emptiness_at_valid γ vs_queue i empty :
    emptiness_auth γ vs_queue -∗
    emptiness_at γ i empty -∗
    ⌜i < γ.(metadata_size)⌝.
  Proof.
    iIntros "(:emptiness_auth) Hat".
    iDestruct (ghost_list_lookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iSteps.
  Qed.
  #[local] Lemma emptiness_empty γ vs_queue :
    emptiness_auth γ vs_queue -∗
    ( [∗ list] i ∈ seq 0 γ.(metadata_size),
      emptiness_at γ i Empty
    ) -∗
    ⌜vs_queue = []⌝.
  Proof.
    iIntros "(:emptiness_auth) Hats".
    destruct Hemptiness as [-> | (i & Hlookup)]. 1: iSteps.
    iDestruct (big_sepL_lookup with "Hats") as "Hat".
    { apply lookup_lt_Some in Hlookup.
      rewrite lookup_seq -Hemptys /=. eauto.
    }
    iDestruct (ghost_list_lookup with "Hauth Hat") as %?. congruence.
  Qed.
  #[local] Lemma emptiness_update_auth γ v vs_queue :
    emptiness_auth γ (v :: vs_queue) ⊢
    emptiness_auth γ vs_queue.
  Proof.
    iIntros "(:emptiness_auth)".
    destruct Hemptiness as [? | (i & Hlookup)]. 2: iSteps.
    exfalso. multiset_solver.
  Qed.
  #[local] Lemma emptiness_update_Nonempty {γ vs_queue i empty} vs_queue' :
    emptiness_auth γ vs_queue -∗
    emptiness_at γ i empty ==∗
      emptiness_auth γ vs_queue' ∗
      emptiness_at γ i Nonempty.
  Proof.
    iIntros "(:emptiness_auth) Hat".
    iDestruct (ghost_list_lookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iMod (ghost_list_update_at Nonempty with "Hauth Hat") as "($ & $)".
    iPureIntro. split.
    - simpl_length.
    - right. exists i. apply list_lookup_insert_eq => //.
  Qed.
  #[local] Lemma emptiness_update_Empty γ i empty :
    emptiness_auth γ [] -∗
    emptiness_at γ i empty ==∗
      emptiness_auth γ [] ∗
      emptiness_at γ i Empty.
  Proof.
    iIntros "(:emptiness_auth) Hat".
    iMod (ghost_list_update_at Empty with "Hauth Hat") as "($ & $)".
    iSteps. simpl_length.
  Qed.

  Opaque emptiness_auth'.

  Lemma ws_hub_hybrid_inv_agree t ι sz1 sz2 :
    ws_hub_hybrid_inv t ι sz1 -∗
    ws_hub_hybrid_inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iSteps.
  Qed.

  Lemma ws_hub_hybrid_owner_exclusive t i status1 empty1 status2 empty2 :
    ws_hub_hybrid_owner t i status1 empty1 -∗
    ws_hub_hybrid_owner t i status2 empty2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-. iClear "Hmeta2".
    iApply (ws_bdeques_public_owner_exclusive with "Hdeques_owner1 Hdeques_owner2").
  Qed.

  Lemma ws_hub_hybrid_inv_owner t ι sz i status empty :
    ws_hub_hybrid_inv t ι sz -∗
    ws_hub_hybrid_owner t i status empty -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". simplify.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iApply (ws_bdeques_public_inv_owner with "Hdeques_inv Hdeques_owner").
  Qed.

  Lemma ws_hub_hybrid_model_empty t ι sz vs :
    ws_hub_hybrid_inv t ι sz -∗
    ws_hub_hybrid_model t vs -∗
    ( [∗ list] i ∈ seq 0 sz,
      ∃ status,
      ws_hub_hybrid_owner t i status Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:inv) (:model) Howners". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    iEval (rewrite consistent_empty //).
    iSplit.

    - iIntros "%i %us %Hlookup".

      iDestruct (ws_bdeques_public_inv_model with "Hdeques_inv Hdeques_model") as %Hvss.
      opose proof* (lookup_lt_Some vss i us) as Hi. 1: done.
      iDestruct (big_sepL_lookup _ _ i with "Howners") as "(%status & Howner)".
      { rewrite lookup_seq. auto with lia. }
      iDestruct "Howner" as "(:owner)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (ws_bdeques_public_model_owner with "Hdeques_model Hdeques_owner") as "(%us_ & %Hlookup_ & %Hws)". simplify.
      iPureIntro. apply suffix_nil_inv. naive_solver.

    - iApply (emptiness_empty with "Hemptiness_auth").
      iApply (big_sepL_seq_impl with "Howners"). iIntros "!> %i %Hi (%status & (:owner)) /=". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iSteps.
  Qed.

  Lemma ws_hub_hybrid٠create𑁒spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_hybrid٠create #sz
    {{{
      t
    , RET t;
      ws_hub_hybrid_inv t ι ₊sz ∗
      ws_hub_hybrid_model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_hybrid_owner t i Nonblocked Empty
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    wp_apply+ (waiters٠create𑁒spec with "[//]") as (waiters) "#Hwaiters_inv". 1: done.

    wp_apply (mpmc_queue_1٠create𑁒spec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)".

    wp_apply+ (array٠unsafe_init𑁒spec_disentangled (λ _ round, random_round_model' round (₊sz - 1) (₊sz - 1))) as (v_rounds rounds) "(%Hrounds & Hrounds_model & Hrounds)". 1: done.
    { iIntros "!> %i %Hi".
      wp_apply+ int٠positive_part𑁒spec.
      wp_apply (random_round٠create𑁒spec' with "[//]"). 1: lia.
      rewrite Nat2Z.id. assert (₊(sz - 1) = ₊sz - 1) as -> by lia.
      iSteps.
    }
    iDestruct (array_model_to_inv with "Hrounds_model") as "#Hrounds_inv".
    rewrite Hrounds.

    wp_apply+ (ws_bdeques_public٠create𑁒spec with "[//]") as (deques) "(#Hdeques_inv & Hdeques_model & Hdeques_owner)". 1: done.

    wp_block 𝑡 as "Hmeta" "(H𝑡_deques & H𝑡_rounds & H𝑡_queue & H𝑡_waiters & H𝑡_num_active & _)".
    iMod (pointsto_persist with "H𝑡_deques") as "#H𝑡_deques".
    iMod (pointsto_persist with "H𝑡_rounds") as "#H𝑡_rounds".
    iMod (pointsto_persist with "H𝑡_queue") as "#H𝑡_queue".
    iMod (pointsto_persist with "H𝑡_waiters") as "#H𝑡_waiters".

    iMod (emptiness_alloc ₊sz) as "(%γ_emptiness & Hemptiness_auth & Hemptiness_ats)".

    pose γ :=
      {|metadata_size := ₊sz
      ; metadata_deques := deques
      ; metadata_rounds := v_rounds
      ; metadata_queue := queue
      ; metadata_waiters := waiters
      ; metadata_emptiness := γ_emptiness
      |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta". 1: done.

    iApply "HΦ".
    iSplitL "H𝑡_num_active"; iSteps.
    - iPureIntro. apply consistent_alloc.
    - iMod (array_model_persist with "Hrounds_model") as "Hrounds_model".
      iDestruct (array_model_atomize with "Hrounds_model") as "(_ & Hrounds_model)".
      iDestruct (big_sepL_sep_2 with "Hrounds_model Hrounds") as "H".
      iDestruct (big_sepL_sep_2 with "Hdeques_owner Hemptiness_ats") as "Howners".
      iDestruct (big_sepL_seq_index_1 with "Howners") as "Howners". 1: done.
      iDestruct (big_sepL_sep_2 with "Howners H") as "H".
      iApply big_sepL_seq_index. 1: done.
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_hub_hybrid٠size𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (array٠size𑁒spec_inv with "Hrounds_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_hybrid٠begin_inactive𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠begin_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠end_inactive𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠end_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠block_active𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty
    }}}
      ws_hub_hybrid٠block_active t #i
    {{{
      RET ();
      ws_hub_hybrid_owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (ws_bdeques_public٠block𑁒spec with "[$Hdeques_inv $Hdeques_owner]"). 1: done.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠unblock_active𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Blocked empty
    }}}
      ws_hub_hybrid٠unblock_active t #i
    {{{
      RET ();
      ws_hub_hybrid_owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (ws_bdeques_public٠unblock𑁒spec with "[$Hdeques_inv $Hdeques_owner]"). 1: done.
    iSteps.
  Qed.

  Lemma ws_hub_hybrid٠block𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty
    }}}
      ws_hub_hybrid٠block t #i
    {{{
      RET ();
      ws_hub_hybrid_owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply+ (ws_hub_hybrid٠begin_inactive𑁒spec with "Hinv") as "_".
    wp_apply+ (ws_hub_hybrid٠block_active𑁒spec with "[$Hinv $Howner] HΦ"). 1: done.
  Qed.

  Lemma ws_hub_hybrid٠unblock𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Blocked empty
    }}}
      ws_hub_hybrid٠unblock t #i
    {{{
      RET ();
      ws_hub_hybrid_owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply+ (ws_hub_hybrid٠unblock_active𑁒spec with "[$Hinv $Howner]") as "Howner". 1: done.
    wp_apply+ (ws_hub_hybrid٠end_inactive𑁒spec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_hybrid٠closed𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠closed t
    {{{
      closed
    , RET #closed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠notify𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (waiters٠notify_one𑁒spec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_hybrid٠notify_all𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (waiters٠notify_all𑁒spec with "Hwaiters_inv HΦ").
  Qed.

  Lemma ws_hub_hybrid٠push𑁒spec t ι sz i i_ empty v :
    i = ⁺i_ →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠push t #i v @ ↑ι
    <<<
      ws_hub_hybrid_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_hybrid_owner t i_ Nonblocked Nonempty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    awp_apply (ws_bdeques_public٠push𑁒spec with "[$Hdeques_inv $Hdeques_owner]") without "Hround". 1: done.
    iApply (aacc_aupd with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros "%b %us (%Hlookup & %Hus & Hdeques_model)".
    destruct b.

    - iRight.
      iMod (emptiness_update_Nonempty vs_queue with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
      iSplitR "Hemptiness_at".
      { iFrameSteps. iPureIntro. apply consistent_deque_push => //. }
      iIntros "!> HΦ !> Hdeques_owner Hround {%}".

      wp_apply+ ws_hub_hybrid٠notify𑁒spec. 1: iSteps.
      iSteps.

    - iLeft.
      iSplitR "Hemptiness_at". 1: iFrameSteps.
      iIntros "!> HΦ !> Hdeques_owner Hround {%}".

      wp_load.

      awp_apply (mpmc_queue_1٠push𑁒spec with "Hqueue_inv") without "Hdeques_owner Hround".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model".
      iMod (emptiness_update_Nonempty (vs_queue ++ [v]) with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
      iSplitR "Hemptiness_at".
      { iFrameSteps. iPureIntro. apply consistent_queue_push => //. }
      iIntros "!> HΦ !> _ (Hdeques_owner & Hround) {%}".

      wp_apply+ ws_hub_hybrid٠notify𑁒spec as "_". 1: iSteps.
      iSteps.
  Qed.

  Lemma ws_hub_hybrid٠pop𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    awp_apply+ (ws_bdeques_public٠pop𑁒spec with "[$Hdeques_inv $Hdeques_owner]") without "Hround". 1: done.
    iApply (aacc_aupd with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros ([v |] us) "Ho".

    - iRight.
      iDestruct "Ho" as "(% & %Hlookup & %Hws & <- & Hdeques_model)".
      iExists (Some v).
      iSplitR "Hemptiness_at".
      { eapply consistent_deque_pop in Hconsistent as (vs' & -> & Hconsistent). 2: done.
        iFrameSteps.
      }
      iSteps. iPureIntro.
      intros ->. exfalso.
      opose proof* Hempty as ->. 1: done.
      eapply suffix_cons_nil_inv, suffix_app_l => //.

    - iLeft.
      iDestruct "Ho" as "(%Hlookup & -> & Hdeques_model)".
      iSplitR "Hemptiness_at". 1: iFrameSteps.
      iIntros "!> HΦ !> Hdeques_owner Hround {%}".

      wp_load.

      awp_apply (mpmc_queue_1٠pop𑁒spec with "Hqueue_inv") without "Hdeques_owner Hround".
      iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model".
      iExists (head vs_queue).
      destruct vs_queue as [| v vs_queue] => /=.

      + iMod (emptiness_update_Empty with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
        iSplitR "Hemptiness_at". 1: iFrameSteps.
        iIntros "!> HΦ !> _ (Hdeques_owner & Hround) {%}".
        iSteps.

      + iSplitR "Hemptiness_at".
        { eapply consistent_queue_pop in Hconsistent as (vs' & -> & Hconsistent).
          iDestruct (emptiness_update_auth with "Hemptiness_auth") as "Hemptiness_auth".
          iFrameSteps.
        }
        iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠try_steal_once𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Blocked empty
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠try_steal_once t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ Blocked empty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (array٠unsafe_get𑁒spec_cell with "Hrounds") as "_". 1: lia.
    wp_apply+ (random_round٠reset𑁒spec' with "Hround") as "Hround".
    wp_load.

    iDestruct (ws_bdeques_public_inv_owner with "Hdeques_inv Hdeques_owner") as %?.
    awp_apply (ws_bdeques_public٠steal_as𑁒spec with "[$Hdeques_inv $Hdeques_owner $Hround]") without "Hemptiness_at". 1-2: lia.
    iApply (aacc_aupd_commit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros ([v |]) "Ho".

    - iDestruct "Ho" as "(%j & %ws' & %Hj & %Hlookup & Hdeques_model)".
      iExists (Some v).
      iSplitL.
      { eapply consistent_deque_steal in Hconsistent as (vs' & -> & Hconsistent). 2: done.
        iFrameSteps.
      }
      iSteps.

    - iExists None. iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid_try_steal₀𑁒spec P Q t ι sz i i_ empty yield max_round pred :
    i = ⁺i_ →
    (0 ≤ max_round)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Blocked empty ∗
      P ∗
      □ (
        P -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q else P
        }}
      )
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠try_steal₀ t #i #yield #max_round pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_hybrid_model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ Blocked empty ∗
      if o is Anything then Q else P
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round %Φ (#Hinv & Howner & HP & #Hpred) HΦ".

    iLöb as "HLöb" forall (max_round Hmax_round).

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! Nothing with "Hmodel").
      iFrame.

    - awp_apply+ (ws_hub_hybrid٠try_steal_once𑁒spec with "[$Hinv $Howner]"). 1: done.
      iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Something v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round Hcase}".

        wp_apply+ (wp_wand with "(Hpred HP)") as (res) "(%b & -> & Hb)".
        destruct b; wp_pures.

        * iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
          iApply ("HΦ" $! Anything with "Hmodel [$Howner $Hb]").

        * wp_bind (if: _ then _ else _)%E.
          wp_apply (wp_wand itype_unit) as (res) "->".
          { destruct yield; iSteps. }

          wp_apply+ ("HLöb" with "[%] Howner Hb HΦ"). 1: lia.
  Qed.

  #[local] Lemma ws_hub_hybrid٠try_steal𑁒spec P Q t ι sz i i_ empty max_round_noyield max_round_yield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Blocked empty ∗
      P ∗
      □ (
        P -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q else P
        }}
      )
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠try_steal t #i #max_round_noyield #max_round_yield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_hybrid_model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ Blocked empty ∗
      if o is Anything then Q else P
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP & #Hpred) HΦ".

    wp_rec.

    awp_apply+ (ws_hub_hybrid_try_steal₀𑁒spec P Q with "[$Hinv $Howner $HP $Hpred]"). 1-2: done.
    iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame. iIntros "HΦ !> (Howner & HP) {%- Hmax_round_yield}".

      wp_apply+ (ws_hub_hybrid_try_steal₀𑁒spec P Q with "[$Hinv $Howner $HP $Hpred] HΦ"). 1-2: done.

    - iRight. iExists Anything. iFrameSteps.

    - iRight. iExists (Something v). iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠steal_aux𑁒spec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Blocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype_unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠steal_aux t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ (if o then Nonblocked else Blocked) empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_hybrid_inv_owner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (notification).

    wp_rec.

    awp_apply+ (ws_hub_hybrid٠try_steal𑁒spec P_pred Q_pred with "[$Hinv $Howner $HP_pred $Hpred]"). 1-3: done.
    iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame. iIntros "HΦ !> (Howner & HP_pred) {%- Hi}".

      iDestruct "Hinv" as "(:inv)".

      wp_load.
      wp_apply (waiters٠prepare_wait𑁒spec with "Hwaiters_inv") as "_". 1: lia.

      awp_apply+ (ws_hub_hybrid٠try_steal_once𑁒spec with "[$Howner]"). 1: done. 1: iSteps.
      iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
        iRight. iExists (Some v).
        iSplitL "Hmodel". { iFrameSteps. }
        iIntros "HΦ !> Howner {%- Hi}".

        wp_load.
        wp_apply (waiters٠cancel_wait𑁒spec with "Hwaiters_inv") as (b) "_". 1: lia.
        wp_pures.

        iApply ("HΦ" with "[$]").

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hi}".

        wp_apply+ (wp_wand with "(Hnotification HP_notification [])") as (res) "(-> & HP_notification)".
        { wp_load.
          wp_apply (waiters٠notify𑁒spec with "Hwaiters_inv") => //. 1: lia.
        }
        wp_apply+ (wp_wand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
        destruct b; wp_pures.

        * wp_load.
          wp_apply (waiters٠cancel_wait𑁒spec with "Hwaiters_inv") as (b) "_". 1: lia.

          wp_bind (if: _ then _ else _)%E.
          wp_apply (wp_wand itype_unit) as (res) "->".
          { destruct b; wp_pures. 1: iSteps.
            wp_load.
            wp_apply (waiters٠notify_one𑁒spec with "Hwaiters_inv") => //.
          }

          wp_pures.

          iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
          iMod ("HΦ" $! None with "Hmodel") as "HΦ".
          iApply ("HΦ" with "[$]").

        * wp_load.
          wp_apply (waiters٠commit_wait𑁒spec with "Hwaiters_inv") as "_". 1: lia.
          wp_apply+ ("HLöb" with "Howner HP_notification [] Hb HΦ"). 1: iSteps.

    - iRight. iExists None.
      iSplitL "Hmodel". { iFrameSteps. }
      iIntros "HΦ !> (Howner & HQ_pred)".

      wp_pures.

      iApply ("HΦ" with "[$]").

    - iRight. iExists (Some v).
      iSplitL "Hmodel". { iFrameSteps. }
      iIntros "HΦ !> (Howner & HP_pred)".

      wp_pures.

      iApply ("HΦ" with "[$]").
  Qed.

  Lemma ws_hub_hybrid٠steal_until𑁒spec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype_unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_hybrid_inv_owner with "Hinv Howner") as %Hi.

    wp_rec.
    wp_apply+ (ws_hub_hybrid٠block_active𑁒spec with "[$Hinv $Howner]") as "Howner". 1: done.

    wp_apply+ (ws_hub_hybrid٠steal_aux𑁒spec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $HP_pred $Hpred]"). 1-3: done.
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ (Howner & HP_notification & H)".

    wp_apply+ (ws_hub_hybrid٠unblock_active𑁒spec with "[$Hinv $Howner]"). 1: done.
    iSteps.
  Qed.

  Lemma ws_hub_hybrid٠steal𑁒spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | RET o;
      ws_hub_hybrid_owner t i_ (if o then Nonblocked else Blocked) empty
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner) HΦ".
    iDestruct (ws_hub_hybrid_inv_owner with "Hinv Howner") as %Hi.

    wp_rec.
    wp_apply+ (ws_hub_hybrid٠block𑁒spec with "[$Hinv $Howner]") as "Howner". 1: done.

    wp_apply+ (ws_hub_hybrid٠steal_aux𑁒spec True True True with "[$Hinv $Howner]"). 1-3: done.
    { iStep. iSplit. 1: iSteps. iStep 3.
      wp_apply+ (ws_hub_hybrid٠closed𑁒spec with "Hinv") as ([]) "_".
      all: iSteps.
    }
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ (Howner & _)".

    wp_pures.

    wp_bind (Match _ _ _ _).
    wp_apply (wp_wand (λ res,
      ⌜res = ()%V⌝ ∗
      ws_hub_hybrid_owner t i_ (if o then Nonblocked else Blocked) empty
    )%I with "[Howner]") as (res) "(-> & Howner)".
    { destruct o as [v |]; wp_pures.
      - wp_apply (ws_hub_hybrid٠unblock𑁒spec with "[$Hinv $Howner]") as "$" => //.
      - wp_apply (ws_hub_hybrid٠notify_all𑁒spec with "Hinv").
        iFrameSteps.
    }

    wp_pures.

    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_hybrid٠close𑁒spec t ι sz :
    {{{
      ws_hub_hybrid_inv t ι sz
    }}}
      ws_hub_hybrid٠close t
    {{{
      RET ();
      True
    }}}.
  Proof.
    apply ws_hub_hybrid٠begin_inactive𑁒spec.
  Qed.
End ws_hub_hybrid_G.

#[global] Opaque ws_hub_hybrid_inv.
#[global] Opaque ws_hub_hybrid_model.
#[global] Opaque ws_hub_hybrid_owner.

Section ws_hub_hybrid_G.
  Context `{ws_hub_hybrid_G : WsHubHybridG Σ}.

  Implicit Types P P_notification P_pred Q Q_pred : iProp Σ.

  Lemma ws_hub_hybrid٠pop_steal_until𑁒spec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype_unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠pop_steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | empty,
      RET o;
      ws_hub_hybrid_owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

    wp_rec.
    wp_apply+ (wp_wand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
    destruct b; wp_pures.

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - awp_apply+ (ws_hub_hybrid٠pop𑁒spec with "[$Hinv $Howner]"). 1: done.
      iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

        wp_apply+ (ws_hub_hybrid٠steal_until𑁒spec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $Hb $Hpred]"). 1-3: done.
        iApply (atomic_update_wand with "HΦ").
        iSteps.
  Qed.

  Lemma ws_hub_hybrid٠pop_steal𑁒spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid_inv t ι sz ∗
      ws_hub_hybrid_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid_model t vs
    >>>
      ws_hub_hybrid٠pop_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid_model t vs'
      end
    | empty,
      RET o;
      ws_hub_hybrid_owner t i_ (if o then Nonblocked else Blocked) empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_apply+ (ws_hub_hybrid٠pop𑁒spec with "[$Hinv $Howner]"). 1: done.
    iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iSteps.

    - iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

      wp_apply+ (ws_hub_hybrid٠steal𑁒spec with "[$Hinv $Howner]"). 1-3: done.
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ Howner".
      iApply ("HΦ" with "[$Howner]").
      destruct o; iFrameSteps.
  Qed.
End ws_hub_hybrid_G.

From zoo_parabs Require
  ws_hub_hybrid__opaque.
