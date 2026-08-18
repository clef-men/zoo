Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gmultiset.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_parabs.base.
Require Export zoo_parabs.ws_hub_std__code.
Require Import zoo_parabs.ws_hub_std__types.
Require Import zoo.options.

Implicit Type b yield closed : bool.
Implicit Type num_active : Z.
Implicit Type 𝑡 : location.
Implicit Type v t notification notify pred : val.
Implicit Type vs : gmultiset val.
Implicit Type ws us : list val.
Implicit Type vss : list $ list val.
Implicit Type status : status.
Implicit Type empty : emptiness.

Class WsHubStdG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_hub_std۰G۰deques۰G :: WsDequesPublicG Σ
  ; #[local] ws_hub_std۰G۰waiters۰G :: WaitersG Σ
  }.

Definition ws_hub_std۰Σ :=
  #[ws_deques_public۰Σ
  ; waiters۰Σ
  ].
#[global] Instance subGｰws_hub_std۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_hub_std۰Σ Σ →
  WsHubStdG Σ.
Proof.
  solve_inG.
Qed.

Section consistent.
  #[local] Definition consistent vs vss :=
    vs = ⋃+ (list_to_set_disj <$> vss).

  #[local] Lemma consistentｰalloc sz :
    consistent ∅ (replicate sz []).
  Proof.
    rewrite /consistent fmap_replicate gmultisetｰdisj_union_listｰreplicateｰempty //.
  Qed.

  #[local] Lemma consistentｰempty vs vss :
    consistent vs vss →
    vs = ∅ ↔
      ∀ i us,
      vss !! i = Some us →
      us = [].
  Proof.
    intros ->.
    rewrite gmultisetｰdisj_union_listｰempty.
    setoid_rewrite list_elem_of_fmap.
    split.
    - intros H i us Hus%list_elem_of_lookup_2.
      rewrite -list_to_set_disjｰempty.
      eauto.
    - intros H ? (us & -> & Hus%list_elem_of_lookup).
      rewrite list_to_set_disjｰempty.
      naive_solver.
  Qed.

  #[local] Lemma consistentｰpush {vs vss i us} v :
    vss !! i = Some us →
    consistent vs vss →
    consistent ({[+v+]} ⊎ vs) (<[i := us ++ [v]]> vss).
  Proof.
    intros Hlookup ->.
    rewrite /consistent.
    rewrite list_fmap_insert list_to_set_disjｰsnoc gmultisetｰdisj_union_listｰinsertｰdisj_unionｰl //.
    rewrite list_lookup_fmap Hlookup //.
  Qed.
  #[local] Lemma consistentｰremove {vs vss i us} us1 v us2 :
    vss !! i = Some us →
    us = us1 ++ v :: us2 →
    consistent vs vss →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us1 ++ us2]> vss).
  Proof.
    intros Hlookup -> Hconsistent.
    exists (vs ∖ {[+v+]}).
    rewrite {}Hconsistent.
    assert ((list_to_set_disj <$> vss : list $ gmultiset _) !! i = Some $ (list_to_set_disj $ us1 ++ v :: us2)).
    { rewrite list_lookup_fmap Hlookup //. }
    split.
    - apply gmultiset_disj_union_difference'.
      { apply elem_of_gmultiset_disj_union_list.
        eexists. split.
        - rewrite list_elem_of_lookup. eauto.
        - rewrite list_to_set_disj_app. set_solver.
      }
    - rewrite (gmultisetｰdisj_union_listｰdelete' _ i (list_to_set_disj $ us1 ++ v :: us2)) //.
      rewrite /consistent list_fmap_insert gmultisetｰdisj_union_listｰinsert //.
      rewrite !list_to_set_disj_app.
      multiset_solver.
  Qed.
  #[local] Lemma consistentｰpop vs vss i us v :
    vss !! i = Some (us ++ [v]) →
    consistent vs vss →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us]> vss).
  Proof.
    intros Hlookup Hconsistent.
    eapply (consistentｰremove us v []) in Hconsistent as (vs' & -> & Hconsistent). 2-3: done.
    rewrite app_nil_r in Hconsistent.
    eauto.
  Qed.
  #[local] Lemma consistentｰsteal vs vss i v us :
    vss !! i = Some (v :: us) →
    consistent vs vss →
      ∃ vs',
      vs = {[+v+]} ⊎ vs' ∧
      consistent vs' (<[i := us]> vss).
  Proof.
    intros Hlookup.
    eapply (consistentｰremove [] v us) => //.
  Qed.
End consistent.

Opaque consistent.

Section ws_hub_std۰G.
  Context `{ws_hub_std۰G : WsHubStdG Σ}.

  Implicit Type P P_notification P_pred Q Q_pred : iProp Σ.

  Record metadata :=
    { metadata۰size : nat
    ; metadata۰deques : val
    ; metadata۰rounds : val
    ; metadata۰waiters : val
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

  #[local] Definition inv۰inner 𝑡 : iProp Σ :=
    ∃ num_active,
    𝑡.[num_active] ↦ #num_active.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %num_active
      & H𝑡_num_active
      )
    ".
  Definition ws_hub_std۰inv t ι sz : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ⌜sz = γ.(metadata۰size)⌝ ∗
    𝑡.[deques] ↦□ γ.(metadata۰deques) ∗
    𝑡.[rounds] ↦□ γ.(metadata۰rounds) ∗
    𝑡.[waiters] ↦□ γ.(metadata۰waiters) ∗
    ws_deques_public۰inv γ.(metadata۰deques) ι γ.(metadata۰size) ∗
    array۰inv γ.(metadata۰rounds) γ.(metadata۰size) ∗
    waiters۰inv γ.(metadata۰waiters) sz ∗
    inv nroot (inv۰inner 𝑡).
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{}
      & ->
      & #H𝑡{}_deques
      & #H𝑡{}_rounds
      & #H𝑡{}_waiters
      & #Hdeques{}_inv
      & #Hrounds{}_inv
      & #Hwaiters{}_inv
      & #Hinv{}
      )
    ".

  Definition ws_hub_std۰model t vs : iProp Σ :=
    ∃ 𝑡 γ vss,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ws_deques_public۰model γ.(metadata۰deques) vss ∗
    ⌜consistent vs vss⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡_
      & %γ_
      & %vss
      & %Heq
      & Hmeta_
      & Hdeques_model
      & %Hconsistent
      )
    ".

  Definition ws_hub_std۰owner t i status empty : iProp Σ :=
    ∃ 𝑡 γ ws round n,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    ws_deques_public۰owner γ.(metadata۰deques) i status ws ∗
    ⌜empty = Empty → ws = []⌝ ∗
    array۰slice γ.(metadata۰rounds) i DfracDiscarded [round] ∗
    random_round۰model' round (γ.(metadata۰size) - 1) n.
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
      )
    ".

  #[global] Instance ws_hub_std۰modelｰtimeless t vs :
    Timeless (ws_hub_std۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_hub_std۰invｰpersistent t ι sz :
    Persistent (ws_hub_std۰inv t ι sz).
  Proof.
    apply _.
  Qed.

  Lemma ws_hub_std۰invｰagree t ι sz1 sz2 :
    ws_hub_std۰inv t ι sz1 -∗
    ws_hub_std۰inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simp.
    iDestruct (metaｰagree with "Hmeta1 Hmeta2") as %<-.
    iSteps.
  Qed.

  Lemma ws_hub_std۰ownerｰexclusive t i status1 empty1 status2 empty2 :
    ws_hub_std۰owner t i status1 empty1 -∗
    ws_hub_std۰owner t i status2 empty2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simp.
    iDestruct (metaｰagree with "Hmeta1 Hmeta2") as %<-. iClear "Hmeta2".
    iApply (ws_deques_public۰ownerｰexclusive with "Hdeques_owner1 Hdeques_owner2").
  Qed.

  Lemma ws_hub_stdｰinvｰowner t ι sz i status empty :
    ws_hub_std۰inv t ι sz -∗
    ws_hub_std۰owner t i status empty -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". simp.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-.
    iApply (ws_deques_publicｰinvｰowner with "Hdeques_inv Hdeques_owner").
  Qed.

  Lemma ws_hub_std۰modelｰempty t ι sz vs :
    ws_hub_std۰inv t ι sz -∗
    ws_hub_std۰model t vs -∗
    ( [∗ list] i ∈ seq 0 sz,
      ∃ status,
      ws_hub_std۰owner t i status Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:inv) (:model) Howners". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iEval (rewrite consistentｰempty //). iIntros "%i %us %Hlookup".
    iDestruct (ws_deques_publicｰinvｰmodel with "Hdeques_inv Hdeques_model") as %Hvss.
    opose proof* (lookup_lt_Some vss i us) as Hi. 1: done.
    iDestruct (big_sepL_lookup _ _ i with "Howners") as "(%status & Howner)".
    { rewrite lookup_seq. auto with lia. }
    iDestruct "Howner" as "(:owner)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (ws_deques_publicｰmodelｰowner with "Hdeques_model Hdeques_owner") as "(%us_ & %Hlookup_ & %Hws)". simp.
    iPureIntro. apply suffix_nil_inv. naive_solver.
  Qed.

  Lemma ws_hub_std٠createｰspec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_std٠create #sz
    {{{
      t
    , RET t;
      ws_hub_std۰inv t ι ₊sz ∗
      ws_hub_std۰model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_std۰owner t i Nonblocked Empty
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.

    wp۰apply+ (waiters٠createｰspec with "[//]") as (waiters) "#Hwaiters_inv". 1: done.

    wp۰apply+ (array٠unsafe_initｰspecｰdisentangled (λ _ round, random_round۰model' round (₊sz - 1) (₊sz - 1))) as (v_rounds rounds) "(%Hrounds & Hrounds_model & Hrounds)". 1: done.
    { iIntros "!> %i %Hi".
      wp۰apply+ int٠positive_partｰspec.
      wp۰apply (random_round٠createｰspec' with "[//]"). 1: lia.
      rewrite Nat2Z.id. assert (₊(sz - 1) = ₊sz - 1) as -> by lia.
      iSteps.
    }
    iDestruct (array۰modelｰtoｰinv with "Hrounds_model") as "#Hrounds_inv".
    rewrite Hrounds.

    wp۰apply+ (ws_deques_public٠createｰspec with "[//]") as (deques) "(#Hdeques_inv & Hdeques_model & Hdeques_owner)". 1: done.

    wp۰block 𝑡 as "Hmeta" "#H𝑡_deques #H𝑡_rounds #H𝑡_waiters H𝑡_num_active".

    pose γ :=
      {|metadata۰size := ₊sz
      ; metadata۰deques := deques
      ; metadata۰rounds := v_rounds
      ; metadata۰waiters := waiters
      |}.

    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.

    iApply "HΦ".
    iSplitL "H𝑡_num_active"; iSteps.
    - iPureIntro. apply consistentｰalloc.
    - iMod (array۰modelｰpersist with "Hrounds_model") as "Hrounds_model".
      iDestruct (array۰modelｰatomize with "Hrounds_model") as "(_ & Hrounds_model)".
      iDestruct (big_sepL_sep_2 with "Hrounds_model Hrounds") as "Hrounds".
      iDestruct (big_sepLｰseqｰindex₁ with "Hdeques_owner") as "Hdeques_owner". 1: done.
      iDestruct (big_sepL_sep_2 with "Hdeques_owner Hrounds") as "H".
      iApply big_sepLｰseqｰindex. 1: done.
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_hub_std٠sizeｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (array٠sizeｰspecｰinv with "Hrounds_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_std٠begin_inactiveｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠begin_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_std٠end_inactiveｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠end_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_std٠block_activeｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty
    }}}
      ws_hub_std٠block_active t #i
    {{{
      RET ();
      ws_hub_std۰owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (ws_deques_public٠blockｰspec with "[$Hdeques_inv $Hdeques_owner]"). 1: done.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_std٠unblock_activeｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Blocked empty
    }}}
      ws_hub_std٠unblock_active t #i
    {{{
      RET ();
      ws_hub_std۰owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (ws_deques_public٠unblockｰspec with "[$Hdeques_inv $Hdeques_owner]"). 1: done.
    iSteps.
  Qed.

  Lemma ws_hub_std٠blockｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty
    }}}
      ws_hub_std٠block t #i
    {{{
      RET ();
      ws_hub_std۰owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_std٠begin_inactiveｰspec with "Hinv") as "_".
    wp۰apply+ (ws_hub_std٠block_activeｰspec with "[$Hinv $Howner] HΦ"). 1: done.
  Qed.

  Lemma ws_hub_std٠unblockｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Blocked empty
    }}}
      ws_hub_std٠unblock t #i
    {{{
      RET ();
      ws_hub_std۰owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp۰rec.
    wp۰apply+ (ws_hub_std٠unblock_activeｰspec with "[$Hinv $Howner]") as "Howner". 1: done.
    wp۰apply+ (ws_hub_std٠end_inactiveｰspec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_std٠closedｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠closed t
    {{{
      closed
    , RET #closed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_std٠notifyｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (waiters٠notify_oneｰspec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_std٠notify_allｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (waiters٠notify_allｰspec with "Hwaiters_inv HΦ").
  Qed.

  Lemma ws_hub_std٠pushｰspec t ι sz i i_ empty v :
    i = ⁺i_ →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠push t #i v
      @ ↑ι
    <<<
      ws_hub_std۰model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_std۰owner t i_ Nonblocked Nonempty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    awp۰apply (ws_deques_public٠pushｰspec with "[$Hdeques_inv $Hdeques_owner]") without "Hround". 1: done.
    iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros "%us (%Hlookup & Hdeques_model) !>".
    iSplitL.
    { iFrameSteps. iPureIntro. apply consistentｰpush => //. }
    iIntros "HΦ !> Hdeques_owner Hround {%}".

    wp۰apply+ ws_hub_std٠notifyｰspec. 1: iSteps.
    iSteps.
  Qed.

  Lemma ws_hub_std٠popｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠pop t #i
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    awp۰apply+ (ws_deques_public٠popｰspec with "[$Hdeques_inv $Hdeques_owner]") without "Hround". 1: done.
    iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros ([v |] us) "Ho".

    - iDestruct "Ho" as "(% & %Hlookup & %Hws & <- & Hdeques_model)".
      iExists (Some v).
      iSplitL.
      { eapply consistentｰpop in Hconsistent as (vs' & -> & Hconsistent). 2: done.
        iFrameSteps.
      }
      iSteps. iPureIntro.
      intros ->. exfalso.
      opose proof* Hempty as ->. 1: done.
      eapply suffix_cons_nil_inv, suffix_app_l => //.

    - iDestruct "Ho" as "(%Hlookup & -> & Hdeques_model)".
      iExists None. iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_std٠try_steal_onceｰspec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Blocked empty
    | ∀∀ vs,
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠try_steal_once t #i
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ Blocked empty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_getｰspecｰcell with "Hrounds") as "_". 1: lia.
    wp۰apply+ (random_round٠resetｰspec' with "Hround") as "Hround".
    wp۰load.

    iDestruct (ws_deques_publicｰinvｰowner with "Hdeques_inv Hdeques_owner") as %?.
    awp۰apply (ws_deques_public٠steal_asｰspec with "[$Hdeques_inv $Hdeques_owner $Hround]"). 1-2: lia.
    iApply (aaccｰaupdｰcommit with "HΦ"). 1: solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hdeques_model". 1: iSteps. iIntros ([v |]) "Ho".

    - iDestruct "Ho" as "(%j & %ws' & %Hj & %Hlookup & Hdeques_model)".
      iExists (Some v).
      iSplitL.
      { eapply consistentｰsteal in Hconsistent as (vs' & -> & Hconsistent). 2: done.
        iFrameSteps.
      }
      iSteps.

    - iExists None. iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_std٠try_steal₁ｰspec P Q t ι sz i i_ empty yield max_round pred :
    i = ⁺i_ →
    (0 ≤ max_round)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Blocked empty ∗
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
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠try_steal₁ t #i #yield #max_round pred
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_std۰model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ Blocked empty ∗
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

    - awp۰apply+ (ws_hub_std٠try_steal_onceｰspec with "[$Hinv $Howner]"). 1: done.
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

  #[local] Lemma ws_hub_std٠try_stealｰspec P Q t ι sz i i_ empty max_round_noyield max_round_yield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Blocked empty ∗
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
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠try_steal t #i #max_round_noyield #max_round_yield pred
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_std۰model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ Blocked empty ∗
      if o is Anything then Q else P
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP & #Hpred) HΦ".

    wp۰rec.

    awp۰apply+ (ws_hub_std٠try_steal₁ｰspec P Q with "[$Hinv $Howner $HP $Hpred]"). 1-2: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame. iIntros "HΦ !> (Howner & HP) {%- Hmax_round_yield}".

      wp۰apply+ (ws_hub_std٠try_steal₁ｰspec P Q with "[$Hinv $Howner $HP $Hpred] HΦ"). 1-2: done.

    - iRight. iExists Anything. iFrameSteps.

    - iRight. iExists (Something v). iFrameSteps.
  Qed.

  #[local] Lemma ws_hub_std٠steal_auxｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Blocked empty ∗
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
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠steal_aux t #i #max_round_noyield #max_round_yield notification pred
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ (if o then Nonblocked else Blocked) empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_stdｰinvｰowner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (notification).

    wp۰rec.

    awp۰apply+ (ws_hub_std٠try_stealｰspec P_pred Q_pred with "[$Hinv $Howner $HP_pred $Hpred]"). 1-3: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame. iIntros "HΦ !> (Howner & HP_pred) {%- Hi}".

      iDestruct "Hinv" as "(:inv)".

      wp۰load.
      wp۰apply (waiters٠prepare_waitｰspec with "Hwaiters_inv") as "_". 1: lia.

      awp۰apply+ (ws_hub_std٠try_steal_onceｰspec with "[$Howner]"). 1: done. 1: iSteps.
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

  Lemma ws_hub_std٠steal_untilｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty ∗
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
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠steal_until t #i #max_round_noyield #max_round_yield notification pred
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_stdｰinvｰowner with "Hinv Howner") as %Hi.

    wp۰rec.
    wp۰apply+ (ws_hub_std٠block_activeｰspec with "[$Hinv $Howner]") as "Howner". 1: done.

    wp۰apply+ (ws_hub_std٠steal_auxｰspec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $HP_pred $Hpred]"). 1-3: done.
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ (Howner & HP_notification & H)".

    wp۰apply+ (ws_hub_std٠unblock_activeｰspec with "[$Hinv $Howner]"). 1: done.
    iSteps.
  Qed.

  Lemma ws_hub_std٠stealｰspec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠steal t #i #max_round_noyield #max_round_yield
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | RET o;
      ws_hub_std۰owner t i_ (if o then Nonblocked else Blocked) empty
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner) HΦ".
    iDestruct (ws_hub_stdｰinvｰowner with "Hinv Howner") as %Hi.

    wp۰rec.
    wp۰apply+ (ws_hub_std٠blockｰspec with "[$Hinv $Howner]") as "Howner". 1: done.

    wp۰apply+ (ws_hub_std٠steal_auxｰspec True True True with "[$Hinv $Howner]"). 1-3: done.
    { iStep. iSplit. 1: iSteps. iStep 3.
      wp۰apply+ (ws_hub_std٠closedｰspec with "Hinv") as ([]) "_".
      all: iSteps.
    }
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ (Howner & _)".

    wp۰pures.

    wp۰bind (Match _ _ _ _).
    wp۰apply (wpｰwand (λ res,
      ⌜res = ()%V⌝ ∗
      ws_hub_std۰owner t i_ (if o then Nonblocked else Blocked) empty
    )%I with "[Howner]") as (res) "(-> & Howner)".
    { destruct o as [v |]; wp۰pures.
      - wp۰apply (ws_hub_std٠unblockｰspec with "[$Hinv $Howner]") as "$" => //.
      - wp۰apply (ws_hub_std٠notify_allｰspec with "Hinv").
        iFrameSteps.
    }

    wp۰pures.

    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_std٠closeｰspec t ι sz :
    {{{
      ws_hub_std۰inv t ι sz
    }}}
      ws_hub_std٠close t
    {{{
      RET ();
      True
    }}}.
  Proof.
    apply ws_hub_std٠begin_inactiveｰspec.
  Qed.
End ws_hub_std۰G.

#[global] Opaque ws_hub_std۰inv.
#[global] Opaque ws_hub_std۰model.
#[global] Opaque ws_hub_std۰owner.

Section ws_hub_std۰G.
  Context `{ws_hub_std۰G : WsHubStdG Σ}.

  Implicit Type P P_notification P_pred Q Q_pred : iProp Σ.

  Lemma ws_hub_std٠pop_steal_untilｰspec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty ∗
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
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠pop_steal_until t #i #max_round_noyield #max_round_yield notification pred
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | empty,
      RET o;
      ws_hub_std۰owner t i_ Nonblocked empty ∗
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

    - awp۰apply+ (ws_hub_std٠popｰspec with "[$Hinv $Howner]"). 1: done.
      iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

        wp۰apply+ (ws_hub_std٠steal_untilｰspec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $Hb $Hpred]"). 1-3: done.
        iApply (atomic_updateｰwand with "HΦ").
        iSteps.
  Qed.

  Lemma ws_hub_std٠pop_stealｰspec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std۰inv t ι sz ∗
      ws_hub_std۰owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_std۰model t vs
    >>>
      ws_hub_std٠pop_steal t #i #max_round_noyield #max_round_yield
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std۰model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std۰model t vs'
      end
    | empty,
      RET o;
      ws_hub_std۰owner t i_ (if o then Nonblocked else Blocked) empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp۰rec.

    awp۰apply+ (ws_hub_std٠popｰspec with "[$Hinv $Howner]"). 1: done.
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iSteps.

    - iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

      wp۰apply+ (ws_hub_std٠stealｰspec with "[$Hinv $Howner]"). 1-3: done.
      iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs %o HΦ Howner".
      iApply ("HΦ" with "[$Howner]").
      destruct o; iFrameSteps.
  Qed.
End ws_hub_std۰G.

Require zoo_parabs.ws_hub_std__opaque.
