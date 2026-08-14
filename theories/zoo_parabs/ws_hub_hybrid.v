Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gmultiset.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.ghost_list.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_parabs.base.
Require Export zoo_parabs.ws_hub_hybrid__code.
Require Import zoo_parabs.ws_hub_hybrid__types.
Require Import zoo.options.

Implicit Type b yield closed : bool.
Implicit Type num_active : Z.
Implicit Type 𝑡 : location.
Implicit Type v t notification notify pred : val.
Implicit Type vs : gmultiset val.
Implicit Type ws us vs_queue : list val.
Implicit Type vss : list $ list val.
Implicit Type status : status.
Implicit Type empty : emptiness.

Class WsHubHybridG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_hub_hybrid۰G۰deques۰G :: WsBdequesPublicG Σ
  ; #[local] ws_hub_hybrid۰G۰queue۰G :: QueueMpmc1G Σ
  ; #[local] ws_hub_hybrid۰G۰waiters۰G :: WaitersG Σ
  ; #[local] ws_hub_hybrid۰G۰emptiness۰G :: GhostListG Σ emptiness
  }.

Definition ws_hub_hybrid۰Σ :=
  #[ws_bdeques_public۰Σ
  ; queue_mpmc_1۰Σ
  ; waiters۰Σ
  ; ghost_list۰Σ emptiness
  ].
#[global] Instance subGｰws_hub_hybrid۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_hub_hybrid۰Σ Σ →
  WsHubHybridG Σ.
Proof.
  solve_inG.
Qed.

Section consistent.
  #[local] Definition consistent vs vss vs_queue :=
    vs =
      ⋃+ (list_to_set_disj <$> vss) ⊎
      list_to_set_disj vs_queue.

  #[local] Lemma consistentｰalloc sz :
    consistent ∅ (replicate sz []) [].
  Proof.
    rewrite /consistent fmap_replicate gmultisetｰdisj_union_listｰreplicateｰempty //.
  Qed.

  #[local] Lemma consistentｰempty vs vss vs_queue :
    consistent vs vss vs_queue →
    vs = ∅ ↔
      ( ∀ i us,
        vss !! i = Some us →
        us = []
      ) ∧
      vs_queue = [].
  Proof.
    intros ->.
    rewrite gmultisetｰdisj_unionｰempty.
    rewrite gmultisetｰdisj_union_listｰempty.
    setoid_rewrite list_elem_of_fmap.
    rewrite list_to_set_disjｰempty.
    split.
    all: intros (H & ->); split; last done.
    - intros i us Hus%list_elem_of_lookup_2.
      rewrite -list_to_set_disjｰempty.
      eauto.
    - intros ? (us & -> & Hus%list_elem_of_lookup).
      rewrite list_to_set_disjｰempty.
      naive_solver.
  Qed.

  #[local] Lemma consistentｰdequeｰpush {vs vss vs_queue i us} v :
    vss !! i = Some us →
    consistent vs vss vs_queue →
    consistent ({[+v+]} ⊎ vs) (<[i := us ++ [v]]> vss) vs_queue.
  Proof.
    intros Hlookup ->.
    rewrite /consistent.
    rewrite assoc. f_equal.
    rewrite list_fmap_insert list_to_set_disjｰsnoc gmultisetｰdisj_union_listｰinsertｰdisj_unionｰl //.
    rewrite list_lookup_fmap Hlookup //.
  Qed.
  #[local] Lemma consistentｰdequeｰremove {vs vss vs_queue i us} us1 v us2 :
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
      { apply elem_ofｰgmultisetｰdisj_unionｰl.
        apply elem_of_gmultiset_disj_union_list.
        eexists. split.
        - rewrite list_elem_of_lookup. eauto.
        - rewrite list_to_set_disj_app. set_solver.
      }
    - rewrite (gmultisetｰdisj_union_listｰdelete' _ i (list_to_set_disj $ us1 ++ v :: us2)) //.
      rewrite /consistent list_fmap_insert gmultisetｰdisj_union_listｰinsert //.
      rewrite !list_to_set_disj_app.
      multiset_solver.
  Qed.
  #[local] Lemma consistentｰdequeｰpop vs vss vs_queue i us v :
    vss !! i = Some (us ++ [v]) →
    consistent vs vss vs_queue →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us]> vss) vs_queue.
  Proof.
    intros Hlookup Hconsistent.
    eapply (consistentｰdequeｰremove us v []) in Hconsistent as (vs' & -> & Hconsistent). 2-3: done.
    rewrite app_nil_r in Hconsistent.
    eauto.
  Qed.
  #[local] Lemma consistentｰdequeｰsteal vs vss vs_queue i v us :
    vss !! i = Some (v :: us) →
    consistent vs vss vs_queue →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us]> vss) vs_queue.
  Proof.
    intros Hlookup.
    eapply (consistentｰdequeｰremove [] v us) => //.
  Qed.

  #[local] Lemma consistentｰqueueｰpush {vs vss vs_queue} v :
    consistent vs vss vs_queue →
    consistent ({[+v+]} ⊎ vs) vss (vs_queue ++ [v]).
  Proof.
    intros ->.
    rewrite /consistent.
    rewrite (comm (⊎)) -assoc. f_equal.
    rewrite list_to_set_disj_app list_to_set_disj_cons right_id (comm (⊎)) //.
  Qed.
  #[local] Lemma consistentｰqueueｰpop vs vss v vs_queue :
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

Section ws_hub_hybrid۰G.
  Context `{ws_hub_hybrid۰G : WsHubHybridG Σ}.

  Implicit Type P P_notification P_pred Q Q_pred : iProp Σ.

  Record metadata :=
    { metadata۰size : nat
    ; metadata۰deques : val
    ; metadata۰rounds : val
    ; metadata۰queue : val
    ; metadata۰waiters : val
    ; metadata۰emptiness : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec :
    EqDecision metadata.
  Proof.
    solve_decision.
  Qed.
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition emptiness۰auth' γ_emptiness sz vs_queue : iProp Σ :=
    ∃ emptys,
    ghost_list۰auth γ_emptiness emptys ∗
    ⌜length emptys = sz⌝ ∗
    ⌜ vs_queue = []
    ∨ ∃ i,
      emptys !! i = Some Nonempty
    ⌝.
  #[local] Definition emptiness۰auth γ :=
    emptiness۰auth' γ.(metadata۰emptiness) γ.(metadata۰size).
  #[local] Instance : CustomIpat "emptiness۰auth" :=
    " ( %emptys
      & Hauth
      & %Hemptys
      & %Hemptiness
      )
    ".
  #[local] Definition emptiness۰at' γ_emptiness i :=
    ghost_list۰at γ_emptiness i (DfracOwn 1).
  #[local] Definition emptiness۰at γ :=
    emptiness۰at' γ.(metadata۰emptiness).

  #[local] Definition inv۰inner 𝑡 : iProp Σ :=
    ∃ num_active,
    𝑡.[num_active] ↦ #num_active.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %num_active
      & H𝑡_num_active
      )
    ".
  Definition ws_hub_hybrid۰inv t ι sz : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ⌜sz = γ.(metadata۰size)⌝ ∗
    𝑡.[deques] ↦□ γ.(metadata۰deques) ∗
    𝑡.[rounds] ↦□ γ.(metadata۰rounds) ∗
    𝑡.[queue] ↦□ γ.(metadata۰queue) ∗
    𝑡.[waiters] ↦□ γ.(metadata۰waiters) ∗
    ws_bdeques_public۰inv γ.(metadata۰deques) ι γ.(metadata۰size) ∗
    array۰inv γ.(metadata۰rounds) γ.(metadata۰size) ∗
    queue_mpmc_1۰inv γ.(metadata۰queue) ι ∗
    waiters۰inv γ.(metadata۰waiters) sz ∗
    inv nroot (inv۰inner 𝑡).
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

  Definition ws_hub_hybrid۰model t vs : iProp Σ :=
    ∃ 𝑡 γ vss vs_queue,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ws_bdeques_public۰model γ.(metadata۰deques) vss ∗
    queue_mpmc_1۰model γ.(metadata۰queue) vs_queue ∗
    ⌜consistent vs vss vs_queue⌝ ∗
    emptiness۰auth γ vs_queue.
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

  Definition ws_hub_hybrid۰owner t i status empty : iProp Σ :=
    ∃ 𝑡 γ ws round n,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ws_bdeques_public۰owner γ.(metadata۰deques) i status ws ∗
    ⌜empty = Empty → ws = []⌝ ∗
    array۰slice γ.(metadata۰rounds) i DfracDiscarded [round] ∗
    random_round۰model' round (γ.(metadata۰size) - 1) n ∗
    emptiness۰at γ i empty.
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

  #[global] Instance ws_hub_hybrid۰modelｰtimeless t vs :
    Timeless (ws_hub_hybrid۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_hub_hybrid۰invｰpersistent t ι sz :
    Persistent (ws_hub_hybrid۰inv t ι sz).
  Proof.
    apply _.
  Qed.

  #[local] Lemma emptinessｰalloc sz :
    ⊢ |==>
      ∃ γ_emptiness,
      emptiness۰auth' γ_emptiness sz [] ∗
      [∗ list] i ∈ seq 0 sz,
        emptiness۰at' γ_emptiness i Empty.
  Proof.
    iMod ghost_listｰalloc as "(%γ_emptiness & $ & Hats)".
    iDestruct (big_sepLｰreplicate₁ with "Hats") as "$".
    iSteps. iPureIntro. simp_length.
  Qed.
  #[local] Lemma emptiness۰atｰvalid γ vs_queue i empty :
    emptiness۰auth γ vs_queue -∗
    emptiness۰at γ i empty -∗
    ⌜i < γ.(metadata۰size)⌝.
  Proof.
    iIntros "(:emptiness۰auth) Hat".
    iDestruct (ghost_listｰlookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iSteps.
  Qed.
  #[local] Lemma emptinessｰempty γ vs_queue :
    emptiness۰auth γ vs_queue -∗
    ( [∗ list] i ∈ seq 0 γ.(metadata۰size),
      emptiness۰at γ i Empty
    ) -∗
    ⌜vs_queue = []⌝.
  Proof.
    iIntros "(:emptiness۰auth) Hats".
    destruct Hemptiness as [-> | (i & Hlookup)]. 1: iSteps.
    iDestruct (big_sepL_lookup with "Hats") as "Hat".
    { apply lookup_lt_Some in Hlookup.
      rewrite lookup_seq -Hemptys /=. eauto.
    }
    iDestruct (ghost_listｰlookup with "Hauth Hat") as %?. congruence.
  Qed.
  #[local] Lemma emptinessｰupdateｰauth γ v vs_queue :
    emptiness۰auth γ (v :: vs_queue) ⊢
    emptiness۰auth γ vs_queue.
  Proof.
    iIntros "(:emptiness۰auth)".
    destruct Hemptiness as [? | (i & Hlookup)]. 2: iSteps.
    exfalso. multiset_solver.
  Qed.
  #[local] Lemma emptinessｰupdateｰNonempty {γ vs_queue i empty} vs_queue' :
    emptiness۰auth γ vs_queue -∗
    emptiness۰at γ i empty ==∗
      emptiness۰auth γ vs_queue' ∗
      emptiness۰at γ i Nonempty.
  Proof.
    iIntros "(:emptiness۰auth) Hat".
    iDestruct (ghost_listｰlookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iMod (ghost_listｰupdateｰat Nonempty with "Hauth Hat") as "($ & $)".
    iPureIntro. split.
    - simp_length.
    - right. exists i. apply list_lookup_insert_eq => //.
  Qed.
  #[local] Lemma emptinessｰupdateｰEmpty γ i empty :
    emptiness۰auth γ [] -∗
    emptiness۰at γ i empty ==∗
      emptiness۰auth γ [] ∗
      emptiness۰at γ i Empty.
  Proof.
    iIntros "(:emptiness۰auth) Hat".
    iMod (ghost_listｰupdateｰat Empty with "Hauth Hat") as "($ & $)".
    iSteps. simp_length.
  Qed.

  Opaque emptiness۰auth'.

  Lemma ws_hub_hybrid۰invｰagree t ι sz1 sz2 :
    ws_hub_hybrid۰inv t ι sz1 -∗
    ws_hub_hybrid۰inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simp.
    iDestruct (metaｰagree with "Hmeta1 Hmeta2") as %<-.
    iSteps.
  Qed.

  Lemma ws_hub_hybrid۰ownerｰexclusive t i status1 empty1 status2 empty2 :
    ws_hub_hybrid۰owner t i status1 empty1 -∗
    ws_hub_hybrid۰owner t i status2 empty2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simp.
    iDestruct (metaｰagree with "Hmeta1 Hmeta2") as %<-. iClear "Hmeta2".
    iApply (ws_bdeques_public۰ownerｰexclusive with "Hdeques_owner1 Hdeques_owner2").
  Qed.

  Lemma ws_hub_hybrid۰invｰowner t ι sz i status empty :
    ws_hub_hybrid۰inv t ι sz -∗
    ws_hub_hybrid۰owner t i status empty -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". simp.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-.
    iApply (ws_bdeques_publicｰinvｰowner with "Hdeques_inv Hdeques_owner").
  Qed.

  Lemma ws_hub_hybrid۰modelｰempty t ι sz vs :
    ws_hub_hybrid۰inv t ι sz -∗
    ws_hub_hybrid۰model t vs -∗
    ( [∗ list] i ∈ seq 0 sz,
      ∃ status,
      ws_hub_hybrid۰owner t i status Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:inv) (:model) Howners". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    iEval (rewrite consistentｰempty //).
    iSplit.

    - iIntros "%i %us %Hlookup".

      iDestruct (ws_bdeques_publicｰinvｰmodel with "Hdeques_inv Hdeques_model") as %Hvss.
      opose proof* (lookup_lt_Some vss i us) as Hi. 1: done.
      iDestruct (big_sepL_lookup _ _ i with "Howners") as "(%status & Howner)".
      { rewrite lookup_seq. auto with lia. }
      iDestruct "Howner" as "(:owner)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (ws_bdeques_publicｰmodelｰowner with "Hdeques_model Hdeques_owner") as "(%us_ & %Hlookup_ & %Hws)". simp.
      iPureIntro. apply suffix_nil_inv. naive_solver.

    - iApply (emptinessｰempty with "Hemptiness_auth").
      iApply (big_sepLｰseqｰimpl with "Howners"). iIntros "!> %i %Hi (%status & (:owner)) /=". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iSteps.
  Qed.

  Lemma ws_hub_hybrid٠createｰspec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_hybrid٠create #sz
    {{{
      t
    , RET t;
      ws_hub_hybrid۰inv t ι ₊sz ∗
      ws_hub_hybrid۰model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_hybrid۰owner t i Nonblocked Empty
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.

    wp۰apply+ (waiters٠createｰspec with "[//]") as (waiters) "#Hwaiters_inv". 1: done.

    wp۰apply (queue_mpmc_1٠createｰspec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)".

    wp۰apply+ (array٠unsafe_initｰspecｰdisentangled (λ _ round, random_round۰model' round (₊sz - 1) (₊sz - 1))) as (v_rounds rounds) "(%Hrounds & Hrounds_model & Hrounds)". 1: done.
    { iIntros "!> %i %Hi".
      wp۰apply+ int٠positive_partｰspec.
      wp۰apply (random_round٠createｰspec' with "[//]"). 1: lia.
      rewrite Nat2Z.id. assert (₊(sz - 1) = ₊sz - 1) as -> by lia.
      iSteps.
    }
    iDestruct (array۰modelｰtoｰinv with "Hrounds_model") as "#Hrounds_inv".
    rewrite Hrounds.

    wp۰apply+ (ws_bdeques_public٠createｰspec with "[//]") as (deques) "(#Hdeques_inv & Hdeques_model & Hdeques_owner)". 1: done.

    wp۰block 𝑡 as "Hmeta" "#H𝑡_deques #H𝑡_rounds #H𝑡_queue #H𝑡_waiters H𝑡_num_active".

    iMod (emptinessｰalloc ₊sz) as "(%γ_emptiness & Hemptiness_auth & Hemptiness_ats)".

    pose γ :=
      {|metadata۰size := ₊sz
      ; metadata۰deques := deques
      ; metadata۰rounds := v_rounds
      ; metadata۰queue := queue
      ; metadata۰waiters := waiters
      ; metadata۰emptiness := γ_emptiness
      |}.

    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.

    iApply "HΦ".
    iSplitL "H𝑡_num_active"; iSteps.
    - iPureIntro. apply consistentｰalloc.
    - iMod (array۰modelｰpersist with "Hrounds_model") as "Hrounds_model".
      iDestruct (array۰modelｰatomize with "Hrounds_model") as "(_ & Hrounds_model)".
      iDestruct (big_sepL_sep_2 with "Hrounds_model Hrounds") as "H".
      iDestruct (big_sepL_sep_2 with "Hdeques_owner Hemptiness_ats") as "Howners".
      iDestruct (big_sepLｰseqｰindex₁ with "Howners") as "Howners". 1: done.
      iDestruct (big_sepL_sep_2 with "Howners H") as "H".
      iApply big_sepLｰseqｰindex. 1: done.
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_hub_hybrid٠sizeｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
    }}}
      ws_hub_hybrid٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (array٠sizeｰspecｰinv with "Hrounds_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_hybrid٠begin_inactiveｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
    }}}
      ws_hub_hybrid٠begin_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠end_inactiveｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
    }}}
      ws_hub_hybrid٠end_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠block_activeｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    }}}
      ws_hub_hybrid٠block_active t #i
    {{{
      RET ();
      ws_hub_hybrid۰owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (ws_bdeques_public٠blockｰspec with "[$Hdeques_inv $Hdeques_owner]"). 1: done.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠unblock_activeｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Blocked empty
    }}}
      ws_hub_hybrid٠unblock_active t #i
    {{{
      RET ();
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (ws_bdeques_public٠unblockｰspec with "[$Hdeques_inv $Hdeques_owner]"). 1: done.
    iSteps.
  Qed.

  Lemma ws_hub_hybrid٠blockｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    }}}
      ws_hub_hybrid٠block t #i
    {{{
      RET ();
      ws_hub_hybrid۰owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_hybrid٠begin_inactiveｰspec with "Hinv") as "_".
    wp۰apply+ (ws_hub_hybrid٠block_activeｰspec with "[$Hinv $Howner] HΦ"). 1: done.
  Qed.

  Lemma ws_hub_hybrid٠unblockｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Blocked empty
    }}}
      ws_hub_hybrid٠unblock t #i
    {{{
      RET ();
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_hybrid٠unblock_activeｰspec with "[$Hinv $Howner]") as "Howner". 1: done.
    wp۰apply+ (ws_hub_hybrid٠end_inactiveｰspec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_hybrid٠closedｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
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

  #[local] Lemma ws_hub_hybrid٠notifyｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
    }}}
      ws_hub_hybrid٠notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (waiters٠notify_oneｰspec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_hybrid٠notify_allｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
    }}}
      ws_hub_hybrid٠notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (waiters٠notify_allｰspec with "Hwaiters_inv HΦ").
  Qed.

  Lemma ws_hub_hybrid٠pushｰspec t ι sz i i_ empty v :
    i = ⁺i_ →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠push t #i v @ ↑ι
    <<<
      ws_hub_hybrid۰model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_hybrid۰owner t i_ Nonblocked Nonempty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    awp۰apply (ws_bdeques_public٠pushｰspec with "[$Hdeques_inv $Hdeques_owner]") without "Hround". 1: done.
    iApply (aaccｰaupd with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros "%b %us (%Hlookup & %Hus & Hdeques_model)".
    destruct b.

    - iRight.
      iMod (emptinessｰupdateｰNonempty vs_queue with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
      iSplitR "Hemptiness_at".
      { iFrameSteps. iPureIntro. apply consistentｰdequeｰpush => //. }
      iIntros "!> HΦ !> Hdeques_owner Hround {%}".

      wp۰apply+ ws_hub_hybrid٠notifyｰspec. 1: iSteps.
      iSteps.

    - iLeft.
      iSplitR "Hemptiness_at". 1: iFrameSteps.
      iIntros "!> HΦ !> Hdeques_owner Hround {%}".

      wp۰load.

      awp۰apply (queue_mpmc_1٠pushｰspec with "Hqueue_inv") without "Hdeques_owner Hround".
      iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model".
      iMod (emptinessｰupdateｰNonempty (vs_queue ++ [v]) with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
      iSplitR "Hemptiness_at".
      { iFrameSteps. iPureIntro. apply consistentｰqueueｰpush => //. }
      iIntros "!> HΦ !> _ (Hdeques_owner & Hround) {%}".

      wp۰apply+ ws_hub_hybrid٠notifyｰspec as "_". 1: iSteps.
      iSteps.
  Qed.

  Lemma ws_hub_hybrid٠popｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    awp۰apply+ (ws_bdeques_public٠popｰspec with "[$Hdeques_inv $Hdeques_owner]") without "Hround". 1: done.
    iApply (aaccｰaupd with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros ([v |] us) "Ho".

    - iRight.
      iDestruct "Ho" as "(% & %Hlookup & %Hws & <- & Hdeques_model)".
      iExists (Some v).
      iSplitR "Hemptiness_at".
      { eapply consistentｰdequeｰpop in Hconsistent as (vs' & -> & Hconsistent). 2: done.
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

      wp۰load.

      awp۰apply (queue_mpmc_1٠popｰspec with "Hqueue_inv") without "Hdeques_owner Hround".
      iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model".
      iExists (head vs_queue).
      destruct vs_queue as [| v vs_queue] => /=.

      + iMod (emptinessｰupdateｰEmpty with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
        iSplitR "Hemptiness_at". 1: iFrameSteps.
        iIntros "!> HΦ !> _ (Hdeques_owner & Hround) {%}".
        iSteps.

      + iSplitR "Hemptiness_at".
        { eapply consistentｰqueueｰpop in Hconsistent as (vs' & -> & Hconsistent).
          iDestruct (emptinessｰupdateｰauth with "Hemptiness_auth") as "Hemptiness_auth".
          iFrameSteps.
        }
        iSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠try_steal_onceｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Blocked empty
    | ∀∀ vs,
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠try_steal_once t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ Blocked empty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_getｰspecｰcell with "Hrounds") as "_". 1: lia.
    wp۰apply+ (random_round٠resetｰspec' with "Hround") as "Hround".
    wp۰load.

    iDestruct (ws_bdeques_publicｰinvｰowner with "Hdeques_inv Hdeques_owner") as %?.
    awp۰apply (ws_bdeques_public٠steal_asｰspec with "[$Hdeques_inv $Hdeques_owner $Hround]") without "Hemptiness_at". 1-2: lia.
    iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros ([v |]) "Ho".

    - iDestruct "Ho" as "(%j & %ws' & %Hj & %Hlookup & Hdeques_model)".
      iExists (Some v).
      iSplitL.
      { eapply consistentｰdequeｰsteal in Hconsistent as (vs' & -> & Hconsistent). 2: done.
        iFrameSteps.
      }
      iSteps.

    - iExists None. iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠try_steal₁ｰspec P Q t ι sz i i_ empty yield max_round pred :
    i = ⁺i_ →
    (0 ≤ max_round)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Blocked empty ∗
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
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠try_steal₁ t #i #yield #max_round pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_hybrid۰model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ Blocked empty ∗
      if o is Anything then Q else P
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round %Φ (#Hinv & Howner & HP & #Hpred) HΦ".

    iLöb as "HLöb" forall (max_round Hmax_round).

    wp۰rec. wp۰pures.
    case_bool_decide as Hcase; wp۰pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! Nothing with "Hmodel").
      iFrame.

    - awp۰apply+ (ws_hub_hybrid٠try_steal_onceｰspec with "[$Hinv $Howner]"). 1: done.
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Something v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round Hcase}".

        wp۰apply+ (wpｰwand with "(Hpred HP)") as (res) "(%b & -> & Hb)".
        destruct b; wp۰pures.

        * iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
          iApply ("HΦ" $! Anything with "Hmodel [$Howner $Hb]").

        * wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
          wp۰apply (wpｰwand itype۰unit) as (res) "->".
          { destruct yield; iSteps. }

          wp۰apply+ ("HLöb" with "[%] Howner Hb HΦ"). 1: lia.
  Qed.

  #[local] Lemma ws_hub_hybrid٠try_stealｰspec P Q t ι sz i i_ empty max_round_noyield max_round_yield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Blocked empty ∗
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
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠try_steal t #i #max_round_noyield #max_round_yield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_hybrid۰model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ Blocked empty ∗
      if o is Anything then Q else P
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP & #Hpred) HΦ".

    wp۰rec.

    awp۰apply+ (ws_hub_hybrid٠try_steal₁ｰspec P Q with "[$Hinv $Howner $HP $Hpred]"). 1-2: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame. iIntros "HΦ !> (Howner & HP) {%- Hmax_round_yield}".

      wp۰apply+ (ws_hub_hybrid٠try_steal₁ｰspec P Q with "[$Hinv $Howner $HP $Hpred] HΦ"). 1-2: done.

    - iRight. iExists Anything. iFrameSteps.

    - iRight. iExists (Something v). iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_hybrid٠steal_auxｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Blocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
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
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠steal_aux t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ (if o then Nonblocked else Blocked) empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_hybrid۰invｰowner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (notification).

    wp۰rec.

    awp۰apply+ (ws_hub_hybrid٠try_stealｰspec P_pred Q_pred with "[$Hinv $Howner $HP_pred $Hpred]"). 1-3: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame. iIntros "HΦ !> (Howner & HP_pred) {%- Hi}".

      iDestruct "Hinv" as "(:inv)".

      wp۰load.
      wp۰apply (waiters٠prepare_waitｰspec with "Hwaiters_inv") as "_". 1: lia.

      awp۰apply+ (ws_hub_hybrid٠try_steal_onceｰspec with "[$Howner]"). 1: done. 1: iSteps.
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
        iRight. iExists (Some v).
        iSplitL "Hmodel". { iFrameSteps. }
        iIntros "HΦ !> Howner {%- Hi}".

        wp۰load.
        wp۰apply (waiters٠cancel_waitｰspec with "Hwaiters_inv") as (b) "_". 1: lia.
        wp۰pures.

        iApply ("HΦ" with "[$]").

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hi}".

        wp۰apply+ (wpｰwand with "(Hnotification HP_notification [])") as (res) "(-> & HP_notification)".
        { wp۰load.
          wp۰apply (waiters٠notifyｰspec with "Hwaiters_inv") => //. 1: lia.
        }
        wp۰apply+ (wpｰwand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
        destruct b; wp۰pures.

        * wp۰load.
          wp۰apply (waiters٠cancel_waitｰspec with "Hwaiters_inv") as (b) "_". 1: lia.

          wp۰bind (𝗶𝗳 _ 𝘁𝗵𝗲𝗻 _ 𝗲𝗹𝘀𝗲 _)%E.
          wp۰apply (wpｰwand itype۰unit) as (res) "->".
          { destruct b; wp۰pures. 1: iSteps.
            wp۰load.
            wp۰apply (waiters٠notify_oneｰspec with "Hwaiters_inv") => //.
          }

          wp۰pures.

          iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
          iMod ("HΦ" $! None with "Hmodel") as "HΦ".
          iApply ("HΦ" with "[$]").

        * wp۰load.
          wp۰apply (waiters٠commit_waitｰspec with "Hwaiters_inv") as "_". 1: lia.
          wp۰apply+ ("HLöb" with "Howner HP_notification [] Hb HΦ"). 1: iSteps.

    - iRight. iExists None.
      iSplitL "Hmodel". { iFrameSteps. }
      iIntros "HΦ !> (Howner & HQ_pred)".

      wp۰pures.

      iApply ("HΦ" with "[$]").

    - iRight. iExists (Some v).
      iSplitL "Hmodel". { iFrameSteps. }
      iIntros "HΦ !> (Howner & HP_pred)".

      wp۰pures.

      iApply ("HΦ" with "[$]").
  Qed.

  Lemma ws_hub_hybrid٠steal_untilｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
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
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_hybrid۰invｰowner with "Hinv Howner") as %Hi.

    wp۰rec.
    wp۰apply+ (ws_hub_hybrid٠block_activeｰspec with "[$Hinv $Howner]") as "Howner". 1: done.

    wp۰apply+ (ws_hub_hybrid٠steal_auxｰspec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $HP_pred $Hpred]"). 1-3: done.
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ (Howner & HP_notification & H)".

    wp۰apply+ (ws_hub_hybrid٠unblock_activeｰspec with "[$Hinv $Howner]"). 1: done.
    iSteps.
  Qed.

  Lemma ws_hub_hybrid٠stealｰspec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | RET o;
      ws_hub_hybrid۰owner t i_ (if o then Nonblocked else Blocked) empty
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner) HΦ".
    iDestruct (ws_hub_hybrid۰invｰowner with "Hinv Howner") as %Hi.

    wp۰rec.
    wp۰apply+ (ws_hub_hybrid٠blockｰspec with "[$Hinv $Howner]") as "Howner". 1: done.

    wp۰apply+ (ws_hub_hybrid٠steal_auxｰspec True True True with "[$Hinv $Howner]"). 1-3: done.
    { iStep. iSplit. 1: iSteps. iStep 3.
      wp۰apply+ (ws_hub_hybrid٠closedｰspec with "Hinv") as ([]) "_".
      all: iSteps.
    }
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ (Howner & _)".

    wp۰pures.

    wp۰bind (Match _ _ _ _).
    wp۰apply (wpｰwand (λ res,
      ⌜res = ()%V⌝ ∗
      ws_hub_hybrid۰owner t i_ (if o then Nonblocked else Blocked) empty
    )%I with "[Howner]") as (res) "(-> & Howner)".
    { destruct o as [v |]; wp۰pures.
      - wp۰apply (ws_hub_hybrid٠unblockｰspec with "[$Hinv $Howner]") as "$" => //.
      - wp۰apply (ws_hub_hybrid٠notify_allｰspec with "Hinv").
        iFrameSteps.
    }

    wp۰pures.

    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_hybrid٠closeｰspec t ι sz :
    {{{
      ws_hub_hybrid۰inv t ι sz
    }}}
      ws_hub_hybrid٠close t
    {{{
      RET ();
      True
    }}}.
  Proof.
    apply ws_hub_hybrid٠begin_inactiveｰspec.
  Qed.
End ws_hub_hybrid۰G.

#[global] Opaque ws_hub_hybrid۰inv.
#[global] Opaque ws_hub_hybrid۰model.
#[global] Opaque ws_hub_hybrid۰owner.

Section ws_hub_hybrid۰G.
  Context `{ws_hub_hybrid۰G : WsHubHybridG Σ}.

  Implicit Type P P_notification P_pred Q Q_pred : iProp Σ.

  Lemma ws_hub_hybrid٠pop_steal_untilｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
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
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠pop_steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | empty,
      RET o;
      ws_hub_hybrid۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

    wp۰rec.
    wp۰apply+ (wpｰwand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
    destruct b; wp۰pures.

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - awp۰apply+ (ws_hub_hybrid٠popｰspec with "[$Hinv $Howner]"). 1: done.
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

        wp۰apply+ (ws_hub_hybrid٠steal_untilｰspec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $Hb $Hpred]"). 1-3: done.
        iApply (atomic_updateｰwand with "HΦ").
        iSteps.
  Qed.

  Lemma ws_hub_hybrid٠pop_stealｰspec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_hybrid۰inv t ι sz ∗
      ws_hub_hybrid۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_hybrid۰model t vs
    >>>
      ws_hub_hybrid٠pop_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_hybrid۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_hybrid۰model t vs'
      end
    | empty,
      RET o;
      ws_hub_hybrid۰owner t i_ (if o then Nonblocked else Blocked) empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp۰rec.

    awp۰apply+ (ws_hub_hybrid٠popｰspec with "[$Hinv $Howner]"). 1: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iSteps.

    - iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

      wp۰apply+ (ws_hub_hybrid٠stealｰspec with "[$Hinv $Howner]"). 1-3: done.
      iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ Howner".
      iApply ("HΦ" with "[$Howner]").
      destruct o; iFrameSteps.
  Qed.
End ws_hub_hybrid۰G.

Require zoo_parabs.ws_hub_hybrid__opaque.
