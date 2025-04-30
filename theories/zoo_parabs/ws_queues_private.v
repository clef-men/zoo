From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.ghost_pred
  lib.ghost_list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  array
  atomic_array
  deque
  random_round.
From zoo_parabs Require Export
  base
  ws_queues_private__code.
From zoo_parabs Require Import
  ws_queues_private__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t deque round : val.
Implicit Types o : option val.
Implicit Types vs ws : list val.
Implicit Types vss wss : list (list val).
Implicit Types status : status.
Implicit Types statuses : list status.

Class WsQueuesPrivateG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_queues_private_G_models_G :: GhostListG Σ (list val) ;
  #[local] ws_queues_private_G_channels_G :: GhostPredG Σ (option val) ;
}.

Definition ws_queues_private_Σ := #[
  ghost_list_Σ (list val) ;
  ghost_pred_Σ (option val)
].
#[global] Instance subG_ws_queues_private_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_queues_private_Σ Σ →
  WsQueuesPrivateG Σ.
Proof.
  solve_inG.
Qed.

#[local] Coercion status_to_val status : val :=
  match status with
  | Blocked =>
      §Blocked
  | Nonblocked =>
      §Nonblocked
  end.

Inductive request :=
  | RequestBlocked
  | RequestNone
  | RequestSome (i : nat).
Implicit Types request : request.
Implicit Types requests : list request.

#[local] Coercion request_to_val request : val :=
  match request with
  | RequestBlocked =>
      §RequestBlocked
  | RequestNone =>
      §RequestNone
  | RequestSome i =>
      ‘RequestSome( #i )
  end.

Inductive response :=
  | ResponseWaiting
  | ResponseNone
  | ResponseSome v.
Implicit Types response : response.
Implicit Types responses : list response.

#[local] Coercion response_to_val response : val :=
  match response with
  | ResponseWaiting =>
      §ResponseWaiting
  | ResponseNone =>
      §ResponseNone
  | ResponseSome v =>
      ‘ResponseSome( v )
  end.

Section ws_queues_private_G.
  Context `{ws_queues_private_G : WsQueuesPrivateG Σ}.

  Implicit Types Ψ : option val → iProp Σ.

  Record metadata := {
    metadata_deques_array : val ;
    metadata_deques : list val ;
    metadata_statuses_array : val ;
    metadata_requests_array : val ;
    metadata_responses_array : val ;
    metadata_inv : namespace ;
    metadata_size : nat ;
    metadata_models : gname ;
    metadata_channels : list gname ;
  }.
  Implicit Types γ : metadata.
  Implicit Types γ_channels : list gname.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition models_auth' :=
    ghost_list_auth.
  #[local] Definition models_auth γ :=
    models_auth' γ.(metadata_models).
  #[local] Definition models_at' γ_models i :=
    ghost_list_at γ_models i (DfracOwn 1).
  #[local] Definition models_at γ :=
    models_at' γ.(metadata_models).

  #[local] Definition channels_at' γ_channels i q Ψ : iProp Σ :=
    ∃ γ_channel,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_pred γ_channel (DfracOwn q) Ψ.
  #[local] Definition channels_at γ :=
    channels_at' γ.(metadata_channels).
  #[local] Instance : CustomIpatFormat "channels_at" :=
    "(
      %γ_channel &
      %Hlookup &
      Hγ_channel
    )".

  #[local] Definition request_au γ j Ψ : iProp Σ :=
    AU <{
      ∃∃ vss,
      models_auth γ vss
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      ∀∀ o,
      match o with
      | None =>
          models_auth γ vss
      | Some v =>
          ∃ vs,
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          models_auth γ (<[j := vs]> vss)
      end
    , COMM
      Ψ o
    }>.

  #[local] Definition inv_inner γ : iProp Σ :=
    ∃ statuses requests responses,
    array_model γ.(metadata_statuses_array) (DfracOwn 1) (status_to_val <$> statuses) ∗
    array_model γ.(metadata_requests_array) (DfracOwn 1) (request_to_val <$> requests) ∗
    array_model γ.(metadata_responses_array) (DfracOwn 1) (response_to_val <$> responses) ∗
    ( [∗ list] i ↦ request ∈ requests,
      if request is RequestSome j then
        ∃ Ψ,
        ⌜j < γ.(metadata_size)⌝ ∗
        channels_at γ j (1/2) Ψ ∗
        request_au γ j Ψ
      else
        True
    ) ∗
    ( [∗ list] i ↦ response ∈ responses,
      match response with
      | ResponseWaiting =>
          True
      | ResponseNone =>
          ∃ Ψ,
          channels_at γ i (1/2) Ψ ∗
          Ψ None
      | ResponseSome v =>
          ∃ Ψ,
          channels_at γ i (1/2) Ψ ∗
          Ψ (Some v)
      end
    ).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %statuses{} &
      %requests{} &
      %responses{} &
      >Hstatuses_model &
      >Hrequests_model &
      >Hresponses_model &
      Hrequests &
      Hresponses
    )".
  Definition ws_queues_private_inv t ι (sz : nat) : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    ⌜sz = γ.(metadata_size)⌝ ∗
    meta l nroot γ ∗
    l.[size] ↦□ #γ.(metadata_size) ∗
    l.[deques] ↦□ γ.(metadata_deques_array) ∗
    ⌜length γ.(metadata_deques) = γ.(metadata_size)⌝ ∗
    array_model γ.(metadata_deques_array) DfracDiscarded γ.(metadata_deques) ∗
    l.[statuses] ↦□ γ.(metadata_statuses_array) ∗
    array_inv γ.(metadata_statuses_array) γ.(metadata_size) ∗
    l.[requests] ↦□ γ.(metadata_requests_array) ∗
    array_inv γ.(metadata_requests_array) γ.(metadata_size) ∗
    l.[responses] ↦□ γ.(metadata_responses_array) ∗
    array_inv γ.(metadata_responses_array) γ.(metadata_size) ∗
    inv ι (inv_inner γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l{} &
      %γ{} &
      {%Ht_eq{}=->} &
      {%Hι_eq{}=->} &
      {%Hsz_eq{}=->} &
      #Hmeta{_{}} &
      #Hl{}_size &
      #Hl{}_deques &
      %Hdeques{}_length &
      #Hdeques{}_model &
      #Hl{}_statuses &
      #Hstatuses{}_inv &
      #Hl{}_requests &
      #Hrequests{}_inv &
      #Hl{}_responses &
      #Hresponses{}_inv &
      #Hinv{}
    )".

  Definition ws_queues_private_model t vss : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    models_auth γ vss.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l{=_} &
      %γ{=_} &
      %Heq{} &
      #Hmeta_{} &
      Hmodels_auth
    )".

  Definition ws_queues_private_owner t i status ws : iProp Σ :=
    ∃ l γ deque vs Ψ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜γ.(metadata_deques) !! i = Some deque⌝ ∗
    deque_model deque vs ∗
    models_at γ i vs ∗
    ⌜vs `suffix_of` ws⌝ ∗
    channels_at γ i 1 Ψ.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %l{=_} &
      %γ{=_} &
      %deque{} &
      %vs{} &
      %Ψ{} &
      %Heq{} &
      #Hmeta_{} &
      %Hdeques_lookup{_{}} &
      Hdeque_model{_{}} &
      Hmodels_at{_{}} &
      %Hws{} &
      Hchannels_at{_{}}
    )".

  #[global] Instance ws_queues_private_model_timeless t vss :
    Timeless (ws_queues_private_model t vss).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_queues_private_inv_persistent t ι sz :
    Persistent (ws_queues_private_inv t ι sz).
  Proof.
    apply _.
  Qed.

  #[local] Lemma models_alloc sz :
    ⊢ |==>
      ∃ γ_models,
      models_auth' γ_models (replicate sz []) ∗
      [∗ list] i ∈ seq 0 sz,
        models_at' γ_models i [].
  Proof.
    iMod ghost_list_alloc as "(%γ_models & $ & Hats)".
    iApply (big_sepL_replicate_1 with "Hats").
  Qed.
  #[local] Lemma models_lookup γ vss i vs :
    models_auth γ vss -∗
    models_at γ i vs -∗
    ⌜vss !! i = Some vs⌝.
  Proof.
    apply ghost_list_lookup.
  Qed.
  #[local] Lemma models_update {γ vss i vs} vs' :
    models_auth γ vss -∗
    models_at γ i vs ==∗
      models_auth γ (<[i := vs']> vss) ∗
      models_at γ i vs'.
  Proof.
    apply ghost_list_update_at.
  Qed.

  #[local] Lemma channels_alloc sz :
    ⊢ |==>
      ∃ γ_channels,
      [∗ list] i ∈ seq 0 sz,
        channels_at' γ_channels i 1 inhabitant.
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 sz,
        |==>
        ∃ γ_channel,
        ghost_pred γ_channel (DfracOwn 1) inhabitant
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iApply ghost_pred_alloc.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepL_exists with "H") as "(%γ_channels & _ & H)".
    iDestruct (big_sepL2_retract_r with "H") as "(_ & H)".
    iDestruct (big_sepL_seq_index_2 with "H") as "H".
    { simpl_length. }
    iSteps.
  Qed.

  Opaque channels_at'.

  Lemma ws_queues_private_inv_agree t ι1 sz1 ι2 sz2 :
    ws_queues_private_inv t ι1 sz1 -∗
    ws_queues_private_inv t ι2 sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (pointsto_agree with "Hl1_size Hl2_size") as %?. naive_solver.
  Qed.

  Lemma ws_queues_private_inv_owner t ι sz i status ws :
    ws_queues_private_inv t ι sz -∗
    ws_queues_private_owner t i status ws -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    apply lookup_lt_Some in Hdeques_lookup.
    iSteps.
  Qed.
  Lemma ws_queues_private_model_owner t vss i status ws :
    ws_queues_private_model t vss -∗
    ws_queues_private_owner t i status ws -∗
      ∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:model =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. simplify.
    iDestruct (models_lookup with "Hmodels_auth Hmodels_at_2") as %Hlookup.
    iSteps.
  Qed.
  Lemma ws_queues_private_owner_exclusive t i status1 ws1 status2 ws2 :
    ws_queues_private_owner t i status1 ws1 -∗
    ws_queues_private_owner t i status2 ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-. simplify.
    iApply (deque_model_exclusive with "Hdeque_model_1 Hdeque_model_2").
  Qed.

  Lemma ws_queues_private_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_queues_private_create #sz
    {{{ t,
      RET t;
      ws_queues_private_inv t ι ₊sz ∗
      ws_queues_private_model t (replicate ₊sz []) ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_queues_private_owner t i Nonblocked []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_apply (array_unsafe_make_spec with "[//]") as (responses_array) "Hresponses_model"; first done.
    iDestruct (array_model_to_inv with "Hresponses_model") as "#Hresponses_inv".
    wp_apply (array_make_spec with "[//]") as (requests_array) "(_ & Hrequests_model)".
    iDestruct (array_model_to_inv with "Hrequests_model") as "#Hrequests_inv".
    wp_apply (array_unsafe_make_spec with "[//]") as (statuses_array) "Hstatuses_model"; first done.
    iDestruct (array_model_to_inv with "Hstatuses_model") as "#Hstatuses_inv".
    wp_apply (array_unsafe_init_spec_disentangled (λ _ deque, deque_model deque [])) as (deques_array deques) "(%Hdeques_length & Hdeques_model & Hdeques)"; first done.
    { iIntros "!> %i %Hi".
      wp_apply (deque_create_spec with "[//]").
      iSteps.
    }
    iDestruct (array_model_to_inv with "Hdeques_model") as "#Hdeques_inv".
    iMod (array_model_persist with "Hdeques_model") as "#Hdeques_model".
    wp_block l as "Hmeta" "(Hl_size & Hl_deques & Hl_statuses & Hl_requests & Hl_responses & _)".
    iMod (pointsto_persist with "Hl_size") as "#Hl_size".
    iMod (pointsto_persist with "Hl_deques") as "#Hl_deques".
    iMod (pointsto_persist with "Hl_statuses") as "#Hl_statuses".
    iMod (pointsto_persist with "Hl_requests") as "#Hl_requests".
    iMod (pointsto_persist with "Hl_responses") as "#Hl_responses".

    iMod models_alloc as "(%γ_models & Hmodels_auth & Hmodels_ats)".
    iMod channels_alloc as "(%γ_channels & Hchannels_ats)".

    pose γ := {|
      metadata_deques_array := deques_array ;
      metadata_deques := deques ;
      metadata_statuses_array := statuses_array ;
      metadata_requests_array := requests_array ;
      metadata_responses_array := responses_array ;
      metadata_size := ₊sz ;
      metadata_inv := ι ;
      metadata_models := γ_models ;
      metadata_channels := γ_channels ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodels_auth Hdeques Hmodels_ats Hchannels_ats".

    - rewrite Hdeques_length. simpl_length.
      iEval (rewrite -(fmap_replicate status_to_val _ Nonblocked)) in "Hstatuses_model".
      iEval (rewrite -(fmap_replicate request_to_val _ RequestNone)) in "Hrequests_model".
      iEval (rewrite -(fmap_replicate response_to_val _ ResponseWaiting)) in "Hresponses_model".
      iExists l, γ. rewrite Z2Nat.id //. iStep 14.
      iApply inv_alloc.
      iSteps. iSplitL => /=.
      + iApply big_sepL_intro. iIntros "!>" (i request (-> & _)%lookup_replicate) "//".
      + iApply big_sepL_intro. iIntros "!>" (i request (-> & _)%lookup_replicate) "//".

    - iSteps.
      iDestruct (big_sepL_sep_2 with "Hmodels_ats Hchannels_ats") as "H".
      iDestruct (big_sepL_to_seq0 with "Hdeques") as "Hdeques". rewrite Hdeques_length.
      iDestruct (big_sepL_sep_2 with "Hdeques H") as "H".
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_queues_private_size_spec t ι sz :
    {{{
      ws_queues_private_inv t ι sz
    }}}
      ws_queues_private_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    iSteps.
  Qed.

 Lemma ws_queues_private_block_spec t ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Nonblocked ws
    }}}
      ws_queues_private_block t #i
    {{{
      RET ();
      ws_queues_private_owner t i_ Blocked ws
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp_rec.
    wp_apply (wp_wand itype_unit); last iSteps.
    wp_load.

    awp_apply (array_unsafe_set_spec_atomic_inv with "Hstatuses_inv"); first lia.
    iInv "Hinv" as "(:inv_inner =1)".
    iAaccIntro with "Hstatuses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ Blocked).
    iIntros "Hstatuses_model !>".
    iSplitL. { iFrameSteps. }
    iIntros "_".

    wp_load.

    awp_apply (array_unsafe_xchg_spec_atomic_inv with "Hrequests_inv"); first lia.
    iInv "Hinv" as "(:inv_inner =2)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ RequestBlocked).
    iIntros "% (%Hrequests2_lookup & Hrequests_model) !>".
    apply list_lookup_fmap_Some in Hrequests2_lookup as (request & Hrequests2_lookup & ->).
    iDestruct (big_sepL_insert_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
    iDestruct ("Hrequests" $! RequestBlocked with "[//]") as "Hrequests".
    iSplitR "Hrequest". { iFrameSteps. }
    iIntros "_".

    destruct request as [| | j]; [iSteps.. |].
    iDestruct "Hrequest" as "(%Χ & >% & Hchannels_at_j & HΧ)".

    wp_load.

    iApply fupd_wp.
    iMod "HΧ" as "(%vss & Hmodels_auth & _ & HΧ)".
    iMod ("HΧ" $! None with "Hmodels_auth") as "HΧ".
    iModIntro.

    awp_apply (array_unsafe_set_spec_atomic_inv with "Hresponses_inv"); first lia.
    iInv "Hinv" as "(:inv_inner =3)".
    iAaccIntro with "Hresponses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseNone).
    iIntros "Hresponses_model !>".
    iDestruct (array_inv_model_agree with "Hresponses_inv Hresponses_model") as %Hresponses3. simpl_length in Hresponses3.
    iDestruct (big_sepL_insert j ResponseNone with "Hresponses [Hchannels_at_j HΧ]") as "Hresponses"; [lia | iSteps |].
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.

  Lemma ws_queues_private_unblock_spec t ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Blocked ws
    }}}
      ws_queues_private_unblock t #i
    {{{
      RET ();
      ws_queues_private_owner t i_ Nonblocked ws
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp_rec.
    wp_apply (wp_wand itype_unit); last iSteps.
    wp_load.

    awp_apply (array_unsafe_set_spec_atomic_inv with "Hrequests_inv"); first lia.
    iInv "Hinv" as "(:inv_inner =1)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ RequestNone).
    iIntros "Hrequests_model !>".
    iDestruct (array_inv_model_agree with "Hrequests_inv Hrequests_model") as %Hrequests3. simpl_length in Hrequests3.
    iDestruct (big_sepL_insert i_ RequestNone with "Hrequests [//]") as "Hrequests"; first lia.
    iSplitL. { iFrameSteps. }
    iIntros "_".

    wp_load.

    awp_apply (array_unsafe_set_spec_atomic_inv with "Hstatuses_inv"); first lia.
    iInv "Hinv" as "(:inv_inner =2)".
    iAaccIntro with "Hstatuses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ Nonblocked).
    iIntros "Hstatuses_model !>".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma ws_queues_private_respond_spec {t ι sz i i_} ws :
    i = ⁺i_ →
    {{{
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Blocked ws
    }}}
      ws_queues_private_respond t #i
    {{{
      RET ();
      ws_queues_private_owner t i_ Nonblocked ws
    }}}.
  Proof.
  Admitted.

  Lemma ws_queues_private_push_spec t ι sz i i_ ws v :
    i = ⁺i_ →
    <<<
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Nonblocked ws
    | ∀∀ vss,
      ws_queues_private_model t vss
    >>>
      ws_queues_private_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ws_queues_private_model t (<[i_ := vs ++ [v]]> vss)
    | RET ();
      ws_queues_private_owner t i_ Nonblocked (vs ++ [v])
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec with "Hdeques_model") as "_"; [lia | done | lia |].
    wp_apply (deque_push_back_spec with "Hdeque_model") as "Hdeque_model".

    iApply fupd_wp.
    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (models_lookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
    iMod (models_update (vs ++ [v]) with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
    iMod ("HΦ" with "[Hmodels_auth]") as "HΦ"; first iSteps.
    iModIntro.

    wp_smart_apply (ws_queues_private_respond_spec with "[-HΦ] HΦ"); [done | iFrameSteps].
  Qed.

  Lemma ws_queues_private_pop_spec t ι sz i i_ ws :
    i = ⁺i_ →
    <<<
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Nonblocked ws
    | ∀∀ vss,
      ws_queues_private_model t vss
    >>>
      ws_queues_private_pop t #i @ ↑ι
    <<<
      ∃∃ o ws,
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ⌜ws = []⌝ ∗
          ws_queues_private_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ⌜ws = vs⌝ ∗
          ws_queues_private_model t (<[i_ := vs]> vss)
      end
    | RET o;
      ws_queues_private_owner t i_ Nonblocked ws
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec with "Hdeques_model") as "_"; [lia | done | lia |].
    wp_apply (deque_pop_back_spec with "Hdeque_model") as (o) "Hdeque_model".

    iApply fupd_wp.
    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (models_lookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
    destruct o as [v |].

    - iDestruct "Hdeque_model" as "(%vs' & -> & Hdeque_model)".
      iMod (models_update vs' with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
      iMod ("HΦ" $! (Some v) with "[Hmodels_auth]") as "HΦ"; first iSteps.
      iModIntro.

      wp_smart_apply (ws_queues_private_respond_spec with "[-HΦ]") as "Howner"; [done | iFrameSteps |].
      wp_pures.
      iApply ("HΦ" with "Howner").

    - iDestruct "Hdeque_model" as "(-> & Hdeque_model)".
      iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.
      iModIntro.

      wp_smart_apply (ws_queues_private_respond_spec [] with "[-HΦ]") as "Howner"; [done | iFrameSteps |].
      wp_pures.
      iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_queues_private_steal_to_spec t ι (sz : nat) i i_ ws j :
    i = ⁺i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Blocked ws
    | ∀∀ vss,
      ws_queues_private_model t vss
    >>>
      ws_queues_private_steal_to t #i #j @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_queues_private_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! ₊j = Some (v :: vs)⌝ ∗
          ws_queues_private_model t (<[₊j := vs]> vss)
      end
    | RET o;
      ws_queues_private_owner t i_ Blocked ws
    >>>.
  Proof.
  Admitted.
End ws_queues_private_G.

#[global] Opaque ws_queues_private_inv.
#[global] Opaque ws_queues_private_model.
#[global] Opaque ws_queues_private_owner.

Section ws_queues_private_G.
  Context `{ws_queues_private_G : WsQueuesPrivateG Σ}.

  #[local] Lemma ws_queues_private_steal_as_0_spec t ι (sz : nat) i i_ ws round (n : nat) :
    i = ⁺i_ →
    <<<
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) n
    | ∀∀ vss,
      ws_queues_private_model t vss
    >>>
      ws_queues_private_steal_as_0 t #sz #i round #n @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_queues_private_model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_queues_private_model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_queues_private_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & Hround) HΦ".
    iDestruct (ws_queues_private_inv_owner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (n).

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel [$Howner Hround]"); first iSteps.

    - wp_apply (random_round_next_spec' with "Hround") as (j) "(%Hj & Hround)"; first lia.
      wp_pures.
      rewrite Nat2Z.id.
      pose k := (i_ + 1 + j) `mod` sz.
      assert ((i_ + 1 + j) `rem` sz = k)%Z as ->.
      { rewrite Z.rem_mod_nonneg; lia. }
      awp_smart_apply (ws_queues_private_steal_to_spec with "[$Hinv $Howner]") without "Hround"; [done | lia |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([ v |]).

      + rewrite Nat2Z.id.
        iSteps as (vs Hlookup) "Hmodel". iExists (Some v). iSteps. iExists k. iSteps. iPureIntro.
        clear Hlookup. rewrite {}/k.
        destruct (decide (i_ + 1 + j < sz)).
        * rewrite Nat.mod_small //. lia.
        * assert (i_ + 1 + j < sz * 2) as ?%Nat.div_lt_upper_bound by lia; last lia.
          assert ((i_ + 1 + j) `div` sz = 1) by lia.
          lia.

      + iSteps as "HΦ Howner Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        iSteps.
  Qed.
  Lemma ws_queues_private_steal_as_spec t ι sz i i_ ws round :
    i = ⁺i_ →
    0 < sz →
    <<<
      ws_queues_private_inv t ι sz ∗
      ws_queues_private_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_queues_private_model t vss
    >>>
      ws_queues_private_steal_as t #i round @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_queues_private_model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_queues_private_model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_queues_private_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Hsz %Φ (#Hinv & Hround) HΦ".

    wp_rec.
    wp_smart_apply (ws_queues_private_size_spec with "Hinv") as "_".
    wp_pures.
    assert (sz - 1 = (sz - 1)%nat)%Z as -> by lia.
    wp_apply (ws_queues_private_steal_as_0_spec with "[$Hinv $Hround] HΦ"); first done.
  Qed.
End ws_queues_private_G.

#[global] Opaque ws_queues_private_create.
#[global] Opaque ws_queues_private_size.
#[global] Opaque ws_queues_private_block.
#[global] Opaque ws_queues_private_unblock.
#[global] Opaque ws_queues_private_push.
#[global] Opaque ws_queues_private_pop.
#[global] Opaque ws_queues_private_steal_to.
#[global] Opaque ws_queues_private_steal_as.
