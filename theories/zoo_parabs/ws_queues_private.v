From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.ghost_var
  lib.ghost_pred
  lib.ghost_list
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  array
  atomic_array
  queue_3
  domain
  random_round.
From zoo_parabs Require Export
  base
  ws_queues_private__code.
From zoo_parabs Require Import
  ws_queues_private__types.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t queue round : val.
Implicit Types o : option val.
Implicit Types vs ws : list val.
Implicit Types vss wss : list (list val).
Implicit Types status : status.
Implicit Types statuses : list status.

Class WsQueuesPrivateG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_queues_private_G_models_G :: GhostListG Σ (list val) ;
  #[local] ws_queues_private_G_channel_pred_G :: GhostPredG Σ (option val) ;
  #[local] ws_queues_private_G_channel_generation_G :: GhostVarG Σ (leibnizO gname) ;
  #[local] ws_queues_private_G_channel_state_G :: OneshotG Σ () (option val) ;
}.

Definition ws_queues_private_Σ := #[
  ghost_list_Σ (list val) ;
  ghost_pred_Σ (option val) ;
  ghost_var_Σ (leibnizO gname) ;
  oneshot_Σ () (option val)
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

#[local] Definition request_to_val request : val :=
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

#[local] Coercion option_to_response o :=
  match o with
  | None =>
      ResponseNone
  | Some v =>
      ResponseSome v
  end.
#[local] Definition response_to_val response : val :=
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
    metadata_queues_array : val ;
    metadata_queues : list val ;
    metadata_statuses_array : val ;
    metadata_requests_array : val ;
    metadata_responses_array : val ;
    metadata_inv : namespace ;
    metadata_size : nat ;
    metadata_models : gname ;
    metadata_channels : list (gname * gname) ;
  }.
  Implicit Types γ : metadata.
  Implicit Types γ_channels : list (gname * gname).

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition models_auth' γ_models sz vss : iProp Σ :=
    ghost_list_auth γ_models vss ∗
    ⌜length vss = sz⌝.
  #[local] Definition models_auth γ :=
    models_auth' γ.(metadata_models) γ.(metadata_size).
  #[local] Instance : CustomIpatFormat "models_auth" :=
    "(
      Hauth &
      %Hvss
    )".
  #[local] Definition models_at' γ_models i :=
    ghost_list_at γ_models i (DfracOwn 1).
  #[local] Definition models_at γ :=
    models_at' γ.(metadata_models).

  #[local] Definition channels_waiting' γ_channels i : iProp Σ :=
    ∃ γ_channel gen,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_var γ_channel.2 (DfracOwn (1/2)) gen ∗
    oneshot_pending gen (DfracOwn 1) ().
  #[local] Definition channels_waiting γ :=
    channels_waiting' γ.(metadata_channels).
  #[local] Instance : CustomIpatFormat "channels_waiting" :=
    "(
      %γ_channel_{} &
      %gen{} &
      %Hlookup_{} &
      Hgeneration_{} &
      Hpending_{}
    )".
  #[local] Definition channels_sender' γ_channels i Ψ state : iProp Σ :=
    ∃ γ_channel,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_pred γ_channel.1 (DfracOwn (3/4)) Ψ ∗
    match state with
    | None =>
        True
    | Some o =>
        ∃ gen,
        ghost_var γ_channel.2 (DfracOwn (1/2)) gen ∗
        oneshot_shot gen o
    end.
  #[local] Definition channels_sender γ :=
    channels_sender' γ.(metadata_channels).
  #[local] Instance : CustomIpatFormat "channels_sender" :=
    "(
      %γ_channel_{} &
      {>;}%Hlookup_{} &
      Hpred_{} &
      { {done}
        ( %gen{} &
          Hgeneration_{} &
          #Hshot_{}
        )
      ; _
      }
    )".
  #[local] Definition channels_receiver' γ_channels i Ψ state : iProp Σ :=
    ∃ γ_channel gen,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_pred γ_channel.1 (DfracOwn (1/4)) Ψ ∗
    ghost_var γ_channel.2 (DfracOwn (1/2)) gen ∗
    match state with
    | None =>
        True
    | Some o =>
        oneshot_shot gen o
    end.
  #[local] Definition channels_receiver γ :=
    channels_receiver' γ.(metadata_channels).
  #[local] Instance : CustomIpatFormat "channels_receiver" :=
    "(
      %γ_channel_{} &
      %gen{} &
      %Hlookup_{} &
      Hpred_{} &
      Hgeneration_{} &
      {{done}#Hshot_{};_}
    )".

  #[local] Definition request_au γ i Ψ : iProp Σ :=
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
          ⌜vss !! i = Some (v :: vs)⌝ ∗
          models_auth γ (<[i := vs]> vss)
      end
    , COMM
      Ψ o
    }>.

  #[local] Definition request_model γ i request : iProp Σ :=
    match request with
    | RequestSome j =>
        ∃ Ψ,
        ⌜j < γ.(metadata_size)⌝ ∗
        channels_sender γ j Ψ None ∗
        request_au γ i Ψ
    | _ =>
        True
    end.
  #[local] Instance : CustomIpatFormat "request_model" :=
    "(
      %Χ &
      >% &
      Hchannels_sender &
      HΧ
    )".

  #[local] Definition response_model γ i response : iProp Σ :=
    match response with
    | ResponseWaiting =>
        channels_waiting γ i
    | ResponseNone =>
        ∃ Ψ,
        channels_sender γ i Ψ (Some None) ∗
        Ψ None
    | ResponseSome v =>
        ∃ Ψ,
        channels_sender γ i Ψ (Some $ Some v) ∗
        Ψ (Some v)
    end.
  #[local] Instance : CustomIpatFormat "response_model" :=
    "(
      %Ψ{} &
      Hchannels_sender{_{}} &
      HΨ{}
    )".

  #[local] Definition inv_inner γ : iProp Σ :=
    ∃ statuses requests responses,
    array_model γ.(metadata_statuses_array) (DfracOwn 1) (status_to_val <$> statuses) ∗
    array_model γ.(metadata_requests_array) (DfracOwn 1) (request_to_val <$> requests) ∗
    array_model γ.(metadata_responses_array) (DfracOwn 1) (response_to_val <$> responses) ∗
    ([∗ list] i ↦ request ∈ requests, request_model γ i request) ∗
    ([∗ list] i ↦ response ∈ responses, response_model γ i response).

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
    l.[queues] ↦□ γ.(metadata_queues_array) ∗
    ⌜length γ.(metadata_queues) = γ.(metadata_size)⌝ ∗
    array_model γ.(metadata_queues_array) DfracDiscarded γ.(metadata_queues) ∗
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
      {%Ht_eq{};->} &
      {%Hι_eq{};->} &
      {%Hsz_eq{};->} &
      #Hmeta{_{}} &
      #Hl{}_size &
      #Hl{}_queues &
      %Hqueues{}_length &
      #Hqueues{}_model &
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
      %l{;_} &
      %γ{;_} &
      %Heq{} &
      #Hmeta_{} &
      Hmodels_auth
    )".

  Definition ws_queues_private_owner t i status ws : iProp Σ :=
    ∃ l γ queue vs Ψ_sender Ψ_receiver,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜γ.(metadata_queues) !! i = Some queue⌝ ∗
    queue_3_model queue vs ∗
    models_at γ i vs ∗
    ⌜vs `suffix_of` ws⌝ ∗
    channels_sender γ i Ψ_sender None ∗
    channels_receiver γ i Ψ_receiver None.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %l{;_} &
      %γ{;_} &
      %queue{} &
      %vs{} &
      %Ψ_sender{_{}} &
      %Ψ_receiver{_{}} &
      %Heq{} &
      #Hmeta_{} &
      %Hqueues_lookup{_{}} &
      Hqueue_model{_{}} &
      Hmodels_at{_{}} &
      %Hws{} &
      Hchannels_sender{_{}} &
      Hchannels_receiver{_{}}
    )".

  #[global] Instance channels_waiting_timeless γ i :
    Timeless (channels_waiting γ i).
  Proof.
    apply _.
  Qed.
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
      models_auth' γ_models sz (replicate sz []) ∗
      [∗ list] i ∈ seq 0 sz,
        models_at' γ_models i [].
  Proof.
    iMod ghost_list_alloc as "(%γ_models & $ & Hats)".
    iSplitR.
    - iPureIntro. apply length_replicate.
    - iApply (big_sepL_replicate_1 with "Hats").
  Qed.
  #[local] Lemma models_auth_length γ vss :
    models_auth γ vss ⊢
    ⌜length vss = γ.(metadata_size)⌝.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma models_lookup γ vss i vs :
    models_auth γ vss -∗
    models_at γ i vs -∗
    ⌜vss !! i = Some vs⌝.
  Proof.
    iIntros "(:models_auth) Hat".
    iApply (ghost_list_lookup with "Hauth Hat").
  Qed.
  #[local] Lemma models_update {γ vss i vs} vs' :
    models_auth γ vss -∗
    models_at γ i vs ==∗
      models_auth γ (<[i := vs']> vss) ∗
      models_at γ i vs'.
  Proof.
    iIntros "(:models_auth) Hat".
    iMod (ghost_list_update_at with "Hauth Hat") as "($ & $)".
    iPureIntro. simpl_length.
  Qed.

  Opaque models_auth'.

  #[local] Lemma channels_alloc sz :
    ⊢ |==>
      ∃ γ_channels,
      ( [∗ list] i ∈ seq 0 sz,
        channels_waiting' γ_channels i
      ) ∗
      ( [∗ list] i ∈ seq 0 sz,
        channels_sender' γ_channels i inhabitant None ∗
        channels_receiver' γ_channels i inhabitant None
      ).
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 sz,
        |==>
        ∃ γ_channel,
        ( ∃ gen,
          ghost_var (ghost_var_G := ws_queues_private_G_channel_generation_G) γ_channel.2 (DfracOwn (1/2)) gen ∗
          oneshot_pending gen (DfracOwn 1) ()
        ) ∗
        ( ∃ gen,
          ghost_pred γ_channel.1 (DfracOwn (3/4)) inhabitant ∗
          ghost_pred γ_channel.1 (DfracOwn (1/4)) inhabitant ∗
          ghost_var γ_channel.2 (DfracOwn (1/2)) gen
        )
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iMod (ghost_pred_alloc inhabitant) as "(%γ_pred & Hpred)".
      iEval (rewrite -Qp.three_quarter_quarter) in "Hpred". iDestruct "Hpred" as "(Hpred_1 & Hpred_2)".
      iMod (oneshot_alloc ()) as "(%gen & Hpending)".
      iMod (ghost_var_alloc (ghost_var_G := ws_queues_private_G_channel_generation_G) gen) as "(%γ_state & Hgeneration_1 & Hgeneration_2)".
      iExists (γ_pred, γ_state). iSteps.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepL_exists with "H") as "(%γ_channels & _ & H)".
    iDestruct (big_sepL2_sep with "H") as "(H1 & H2)".
    iDestruct (big_sepL2_retract_r with "H1") as "(_ & H1)".
    iDestruct (big_sepL2_retract_r with "H2") as "(_ & H2)".
    iDestruct (big_sepL_seq_index_2 with "H1") as "H1".
    { simpl_length. }
    iDestruct (big_sepL_seq_index_2 with "H2") as "H2".
    { simpl_length. }
    iExists γ_channels. iSplitL "H1".
    1: iApply (big_sepL_impl with "H1").
    2: iApply (big_sepL_impl with "H2").
    all: iSteps.
  Qed.
  #[local] Lemma channels_sender_exclusive γ i Ψ1 state1 Ψ2 state2 :
    channels_sender γ i Ψ1 state1 -∗
    channels_sender γ i Ψ2 state2 -∗
    False.
  Proof.
    iIntros "(:channels_sender =1) (:channels_sender =2)". simplify_eq.
    iDestruct (ghost_pred_dfrac_ne with "Hpred_1 Hpred_2") as %?; naive_solver.
  Qed.
  #[local] Lemma channels_prepare {γ i Ψ1 Ψ2} Ψ :
    channels_sender γ i Ψ1 None -∗
    channels_receiver γ i Ψ2 None ==∗
      channels_sender γ i Ψ None ∗
      channels_receiver γ i Ψ None.
  Proof.
    iIntros "(:channels_sender =1) (:channels_receiver =2)". simplify_eq.
    iDestruct (ghost_pred_combine inhabitant with "Hpred_1 Hpred_2") as "(_ & Hpred)". rewrite dfrac_op_own Qp.three_quarter_quarter.
    iMod (ghost_pred_update Ψ with "Hpred") as "Hpred".
    iEval (rewrite -Qp.three_quarter_quarter) in "Hpred". iDestruct "Hpred" as "(Hpred_1 & Hpred_2)".
    iSteps.
  Qed.
  #[local] Lemma channels_send {γ i Ψ} o :
    channels_waiting γ i -∗
    channels_sender γ i Ψ None ==∗
    channels_sender γ i Ψ (Some o).
  Proof.
    iIntros "(:channels_waiting =1) (:channels_sender =2)". simplify_eq.
    iMod (oneshot_update_shot o with "Hpending_1") as "#Hshot".
    iSteps.
  Qed.
  #[local] Lemma channels_receive γ i Ψ1 Ψ2 o :
    ▷ channels_sender γ i Ψ1 (Some o) -∗
    channels_receiver γ i Ψ2 None -∗
      ◇ (
        ▷ channels_sender γ i Ψ1 (Some o) ∗
        channels_receiver γ i Ψ2 (Some o)
      ).
  Proof.
    iIntros "(:channels_sender =1 > done=) (:channels_receiver =2)". simplify_eq.
    iDestruct "Hgeneration_1" as ">Hgeneration_1".
    iDestruct "Hshot_1" as ">Hshot_1".
    iDestruct (ghost_var_agree_L with "Hgeneration_1 Hgeneration_2") as %<-.
    iModIntro. iFrameSteps.
  Qed.
  #[local] Lemma channels_reset γ i Ψ1 o1 Ψ2 o2 E :
    ▷ channels_sender γ i Ψ1 (Some o1) -∗
    channels_receiver γ i Ψ2 (Some o2) ={E}=∗
      channels_waiting γ i ∗
      ▷ channels_sender γ i Ψ1 None ∗
      channels_receiver γ i Ψ2 None.
  Proof.
    iIntros "(:channels_sender =1 > done=) (:channels_receiver =2)". simplify_eq.
    iDestruct "Hgeneration_1" as ">Hgeneration_1".
    iMod (oneshot_alloc ()) as "(%gen & Hpending)".
    iDestruct (ghost_var_combine with "Hgeneration_1 Hgeneration_2") as "(_ & Hgeneration)". rewrite dfrac_op_own Qp.half_half.
    iMod (ghost_var_update (ghost_var_G := ws_queues_private_G_channel_generation_G) gen with "Hgeneration") as "Hgeneration".
    iDestruct "Hgeneration" as "(Hgeneration_1 & Hgeneration_2)".
    iSteps.
  Qed.
  #[local] Lemma channels_waiting_receiver γ i Ψ o :
    ▷ channels_waiting γ i -∗
    channels_receiver γ i Ψ (Some o) -∗
    ◇ False.
  Proof.
    iIntros ">(:channels_waiting =1) (:channels_receiver =2 done=)". simplify_eq.
    iDestruct (ghost_var_agree_L with "Hgeneration_1 Hgeneration_2") as %<-.
    iApply (oneshot_pending_shot with "Hpending_1 Hshot_2").
  Qed.
  #[local] Lemma channels_sender_receiver_agree γ i Ψ1 o1 Ψ2 o2 E :
    ▷ channels_sender γ i Ψ1 (Some o1) -∗
    channels_receiver γ i Ψ2 (Some o2) ={E}=∗
      ▷^2 (Ψ1 o1 ≡ Ψ2 o1) ∗
      ⌜o1 = o2⌝ ∗
      ▷ channels_sender γ i Ψ1 (Some o1) ∗
      channels_receiver γ i Ψ2 (Some o1).
  Proof.
    iIntros "(:channels_sender =1 > done=) (:channels_receiver =2 done=)". simplify_eq.
    iDestruct "Hgeneration_1" as ">Hgeneration_1".
    iDestruct "Hshot_1" as ">Hshot_1".
    iDestruct (ghost_pred_agree o1 with "Hpred_1 [$Hpred_2]") as "#Heq".
    iDestruct (ghost_var_agree_L with "Hgeneration_1 Hgeneration_2") as %<-.
    iDestruct (oneshot_shot_agree with "Hshot_1 Hshot_2") as %<-.
    iFrame "#∗". iSteps.
  Qed.

  Opaque channels_waiting'.
  Opaque channels_sender'.
  Opaque channels_receiver'.

  #[local] Lemma response_model_sender γ i response Ψ state :
    ▷ response_model γ i response -∗
    channels_sender γ i Ψ state -∗
      ◇ (
        ⌜response = ResponseWaiting⌝ ∗
        channels_waiting γ i ∗
        channels_sender γ i Ψ state
      ).
  Proof.
    iIntros "Hresponse Hchannels_sender".
    destruct response.
    1: iDestruct "Hresponse" as ">Hresponse".
    1: iModIntro; iSteps.
    all: iDestruct "Hresponse" as "(:response_model =1)".
    all: iDestruct (channels_sender_exclusive with "Hchannels_sender Hchannels_sender_1") as ">%".
    all: done.
  Qed.
  #[local] Lemma response_model_receiver γ i response Ψ o E :
    ▷ response_model γ i response -∗
    channels_receiver γ i Ψ (Some o) ={E}=∗
      ∃ Ψ_,
      ▷^2 (Ψ_ o ≡ Ψ o) ∗
      ⌜response = o⌝ ∗
      ▷ channels_sender γ i Ψ_ (Some o) ∗
      channels_receiver γ i Ψ (Some o) ∗
      ▷ Ψ_ o.
  Proof.
    iIntros "Hresponse Hchannels_receiver".
    destruct response.
    1: iMod (channels_waiting_receiver with "Hresponse Hchannels_receiver") as %[].
    all: iDestruct "Hresponse" as "(:response_model =1)".
    all: iMod (channels_sender_receiver_agree with "Hchannels_sender_1 Hchannels_receiver") as "(Heq & <- & $ & $)".
    all: iFrame "#∗"; iSteps.
  Qed.

  Lemma ws_queues_private_inv_agree t ι1 sz1 ι2 sz2 :
    ws_queues_private_inv t ι1 sz1 -∗
    ws_queues_private_inv t ι2 sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (pointsto_agree with "Hl1_size Hl2_size") as %?. naive_solver.
  Qed.

  Lemma ws_queues_private_inv_model t ι sz vss :
    ws_queues_private_inv t ι sz -∗
    ws_queues_private_model t vss -∗
    ⌜length vss = sz⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iApply (models_auth_length with "Hmodels_auth").
  Qed.

  Lemma ws_queues_private_inv_owner t ι sz i status ws :
    ws_queues_private_inv t ι sz -∗
    ws_queues_private_owner t i status ws -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    apply lookup_lt_Some in Hqueues_lookup.
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
    iApply (queue_3_model_exclusive with "Hqueue_model_1 Hqueue_model_2").
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
    wp_apply (array_unsafe_init_spec_disentangled (λ _ queue, queue_3_model queue [])) as (queues_array queues) "(%Hqueues_length & Hqueues_model & Hqueues)"; first done.
    { iIntros "!> %i %Hi".
      wp_apply (queue_3_create_spec with "[//]").
      iSteps.
    }
    iDestruct (array_model_to_inv with "Hqueues_model") as "#Hqueues_inv".
    iMod (array_model_persist with "Hqueues_model") as "#Hqueues_model".
    wp_block l as "Hmeta" "(Hl_size & Hl_queues & Hl_statuses & Hl_requests & Hl_responses & _)".
    iMod (pointsto_persist with "Hl_size") as "#Hl_size".
    iMod (pointsto_persist with "Hl_queues") as "#Hl_queues".
    iMod (pointsto_persist with "Hl_statuses") as "#Hl_statuses".
    iMod (pointsto_persist with "Hl_requests") as "#Hl_requests".
    iMod (pointsto_persist with "Hl_responses") as "#Hl_responses".

    iMod models_alloc as "(%γ_models & Hmodels_auth & Hmodels_ats)".
    iMod channels_alloc as "(%γ_channels & Hchannels_1 & Hchannels_2)".

    pose γ := {|
      metadata_queues_array := queues_array ;
      metadata_queues := queues ;
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
    iSplitR "Hmodels_auth Hqueues Hmodels_ats Hchannels_2".

    - rewrite Hqueues_length. simpl_length.
      iEval (rewrite -(fmap_replicate status_to_val _ Nonblocked)) in "Hstatuses_model".
      iEval (rewrite -(fmap_replicate request_to_val _ RequestNone)) in "Hrequests_model".
      iEval (rewrite -(fmap_replicate response_to_val _ ResponseWaiting)) in "Hresponses_model".
      iExists l, γ. rewrite Z2Nat.id //. iStep 14.
      iApply inv_alloc.
      iSteps. iSplitR => /=.
      + iApply big_sepL_intro. iIntros "!>" (i request (-> & _)%lookup_replicate) "//".
      + rewrite big_op.big_sepL_replicate.
        iApply (big_sepL_impl with "Hchannels_1").
        iSteps.

    - iSteps.
      iDestruct (big_sepL_sep_2 with "Hmodels_ats Hchannels_2") as "H".
      iDestruct (big_sepL_to_seq0 with "Hqueues") as "Hqueues". rewrite Hqueues_length.
      iDestruct (big_sepL_sep_2 with "Hqueues H") as "H".
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
    iDestruct "Hrequest" as "(:request_model)".

    wp_load.

    iApply fupd_wp.
    iMod "HΧ" as "(%vss & Hmodels_auth & _ & HΧ)".
    iMod ("HΧ" $! None with "Hmodels_auth") as "HΧ".
    iModIntro.

    awp_apply (array_unsafe_set_spec_atomic_inv with "Hresponses_inv"); first lia.
    iInv "Hinv" as "(:inv_inner =3)".
    iAaccIntro with "Hresponses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseNone).
    iIntros "Hresponses_model".
    iDestruct (array_inv_model_agree with "Hresponses_inv Hresponses_model") as %Hresponses3. simpl_length in Hresponses3.
    destruct (lookup_lt_is_Some_2 responses3 j) as (response & Hresponses3_lookup); first lia.
    iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
    iMod (response_model_sender with "Hresponse Hchannels_sender") as "(-> & Hchannels_waiting & Hchannels_sender)".
    iMod (channels_send with "Hchannels_waiting Hchannels_sender") as "Hchannels_sender".
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
      ws_queues_private_owner t i_ Nonblocked ws
    }}}
      ws_queues_private_respond t #i
    {{{
      RET ();
      ws_queues_private_owner t i_ Nonblocked ws
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp_rec.
    iApply (wp_frame_wand with "[Hchannels_sender Hchannels_receiver HΦ]"); first iAccu.
    wp_load.

    awp_apply (array_unsafe_xchg_spec_atomic_inv with "Hrequests_inv") without "Hqueue_model Hmodels_at"; first lia.
    iInv "Hinv" as "(:inv_inner =1)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ RequestNone).
    iIntros "% (%Hrequests1_lookup & Hrequests_model) !>".
    apply list_lookup_fmap_Some in Hrequests1_lookup as (request & Hrequests1_lookup & ->).
    iDestruct (big_sepL_insert_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
    iDestruct ("Hrequests" $! RequestNone with "[//]") as "Hrequests".
    iSplitR "Hrequest". { iFrameSteps. }
    iIntros "_ (Hqueue_model & Hmodels_at)".

    destruct request as [| | j]; [iSteps.. |].
    iDestruct "Hrequest" as "(:request_model)".

    wp_load.
    wp_apply (array_unsafe_get_spec with "Hqueues_model") as "_"; [lia | done | lia |].
    wp_apply (queue_3_pop_front_spec with "Hqueue_model") as "Hqueue_model".

    wp_bind (Match _ _ _ _)%E.
    wp_apply (wp_wand (λ res,
      ⌜res = response_to_val $ head vs⌝
    )%I) as "%res ->".
    { destruct vs; iSteps. }

    wp_load.

    awp_apply (array_unsafe_set_spec_atomic_inv with "Hresponses_inv") without "Hqueue_model"; first lia.
    iInv "Hinv" as "(:inv_inner =2)".
    iAaccIntro with "Hresponses_model"; first iSteps.
    rewrite Nat2Z.id -list_fmap_insert.
    iIntros "Hresponses_model".
    iDestruct (array_inv_model_agree with "Hresponses_inv Hresponses_model") as %Hresponses2. simpl_length in Hresponses2.
    destruct (lookup_lt_is_Some_2 responses2 j) as (response & Hresponses2_lookup); first lia.
    iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
    iMod (response_model_sender with "Hresponse Hchannels_sender") as "(-> & Hchannels_waiting & Hchannels_sender)".
    iMod (channels_send (head vs) with "Hchannels_waiting Hchannels_sender") as "Hchannels_sender".

    iAssert (
      |={_}=>
      models_at γ i_ (tail vs) ∗
      response_model γ j (head vs)
    )%I with "[Hmodels_at Hchannels_sender HΧ]" as ">(Hmodels_at & Hresponse)".
    { iMod "HΧ" as "(%vss & Hmodels_auth & _ & HΧ)".
      iDestruct (models_lookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
      destruct vs as [| v vs]; first iSteps.
      iMod (models_update vs with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
      iMod ("HΧ" $! (Some v) with "[$Hmodels_auth //]") as "HΧ".
      iSteps.
    }

    iSplitR "Hmodels_at". { iFrameSteps. }
    iSteps. iPureIntro. apply suffix_tail. done.
  Qed.

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
    wp_apply (array_unsafe_get_spec with "Hqueues_model") as "_"; [lia | done | lia |].
    wp_apply (queue_3_push_spec with "Hqueue_model") as "Hqueue_model".

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
    wp_apply (array_unsafe_get_spec with "Hqueues_model") as "_"; [lia | done | lia |].
    wp_apply (queue_3_pop_back_spec with "Hqueue_model") as (o) "Hqueue_model".

    iApply fupd_wp.
    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (models_lookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
    destruct o as [v |].

    - iDestruct "Hqueue_model" as "(%vs' & -> & Hqueue_model)".
      iMod (models_update vs' with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
      iMod ("HΦ" $! (Some v) with "[Hmodels_auth]") as "HΦ"; first iSteps.
      iModIntro.

      wp_smart_apply (ws_queues_private_respond_spec with "[-HΦ]") as "Howner"; [done | iFrameSteps |].
      wp_pures.
      iApply ("HΦ" with "Howner").

    - iDestruct "Hqueue_model" as "(-> & Hqueue_model)".
      iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.
      iModIntro.

      wp_smart_apply (ws_queues_private_respond_spec [] with "[-HΦ]") as "Howner"; [done | iFrameSteps |].
      wp_pures.
      iApply ("HΦ" with "Howner").
  Qed.

  #[local] Lemma ws_queues_private_steal_to_0_spec l γ i i_ Ψ :
    i = ⁺i_ →
    i_ < γ.(metadata_size) →
    {{{
      meta l nroot γ ∗
      l.[responses] ↦□ γ.(metadata_responses_array) ∗
      array_inv γ.(metadata_responses_array) γ.(metadata_size) ∗
      inv γ.(metadata_inv) (inv_inner γ) ∗
      channels_receiver γ i_ Ψ None
    }}}
      ws_queues_private_steal_to_0 #l #i
    {{{ o Ψ_sender Ψ_receiver,
      RET o : val;
      channels_sender γ i_ Ψ_sender None ∗
      channels_receiver γ i_ Ψ_receiver None ∗
      Ψ o
    }}}.
  Proof.
    iIntros (-> Hi) "%Φ (#Hmeta & #Hl_responses & #Hresponses_inv & #Hinv & Hchannels_receiver) HΦ".

    iLöb as "HLöb".

    wp_rec. wp_load.

    awp_apply (array_unsafe_get_spec_atomic with "[//]") without "HΦ"; first lia.
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (array_inv_model_agree with "Hresponses_inv Hresponses_model") as %Hresponses1. simpl_length in Hresponses1.
    destruct (lookup_lt_is_Some_2 responses1 i_) as (response & Hresponses1_lookup); first lia.
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    repeat iExists _. iSplitL "Hresponses_model".
    { iFrame. rewrite Nat2Z.id list_lookup_fmap_Some. iSteps. }
    iSplit; first iSteps. iIntros "Hresponses_model". iMod "Hclose" as "_".
    destruct response as [| | v].

    - iSplitR "Hchannels_receiver". { iFrameSteps. }
      iIntros "!> _ HΦ".

      wp_smart_apply domain_yield_spec.
      wp_smart_apply ("HLöb" with "Hchannels_receiver HΦ").

    - iDestruct (big_sepL_lookup_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iDestruct "Hresponse" as "(:response_model =1)".
      iMod (channels_receive with "Hchannels_sender_1 Hchannels_receiver") as "(Hchannels_sender & Hchannels_receiver)".
      iSplitR "Hchannels_receiver". { iFrameSteps. }
      iIntros "!> _ HΦ".

      wp_load.

      awp_apply (array_unsafe_set_spec_atomic_inv with "Hresponses_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv_inner =2)".
      iAaccIntro with "Hresponses_model"; first iSteps.
      rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseWaiting).
      iIntros "Hresponses_model".
      iDestruct (array_inv_model_agree with "Hresponses_inv Hresponses_model") as %Hresponses2. simpl_length in Hresponses2.
      destruct (lookup_lt_is_Some_2 responses2 i_) as (response & Hresponses2_lookup); first lia.
      iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iMod (response_model_receiver with "Hresponse Hchannels_receiver") as "(%Ψ_ & Heq & -> & Hchannels_sender & Hchannels_receiver & HΨ)".
      iMod (channels_reset with "Hchannels_sender Hchannels_receiver") as "(Hchannels_waiting & Hchannels_sender & Hchannels_receiver)".
      iDestruct ("Hresponses" $! ResponseWaiting with "[$Hchannels_waiting]") as "Hresponses".
      iSplitR "Hchannels_sender Hchannels_receiver Heq HΨ". { iFrameSteps. }
      iIntros "!> H£ HΦ".

      wp_pures.
      iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
      iRewrite "Heq" in "HΨ".
      iApply ("HΦ" $! None).
      iSteps.

    - iDestruct (big_sepL_lookup_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iDestruct "Hresponse" as "(:response_model =1)".
      iMod (channels_receive with "Hchannels_sender_1 Hchannels_receiver") as "(Hchannels_sender & Hchannels_receiver)".
      iSplitR "Hchannels_receiver". { iFrameSteps. }
      iIntros "!> _ HΦ".

      wp_load.

      awp_apply (array_unsafe_set_spec_atomic_inv with "Hresponses_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv_inner =2)".
      iAaccIntro with "Hresponses_model"; first iSteps.
      rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseWaiting).
      iIntros "Hresponses_model".
      iDestruct (array_inv_model_agree with "Hresponses_inv Hresponses_model") as %Hresponses2. simpl_length in Hresponses2.
      destruct (lookup_lt_is_Some_2 responses2 i_) as (response & Hresponses2_lookup); first lia.
      iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iMod (response_model_receiver with "Hresponse Hchannels_receiver") as "(%Ψ_ & Heq & -> & Hchannels_sender & Hchannels_receiver & HΨ)".
      iMod (channels_reset with "Hchannels_sender Hchannels_receiver") as "(Hchannels_waiting & Hchannels_sender & Hchannels_receiver)".
      iDestruct ("Hresponses" $! ResponseWaiting with "[$Hchannels_waiting]") as "Hresponses".
      iSplitR "Hchannels_sender Hchannels_receiver Heq HΨ". { iFrameSteps. }
      iIntros "!> H£ HΦ".

      wp_pures.
      iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
      iRewrite "Heq" in "HΨ".
      iApply ("HΦ" $! (Some v)).
      iSteps.
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
    iIntros (-> Hj) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp_rec.
    iApply (wp_frame_wand with "[Hqueue_model Hmodels_at]"); first iAccu.
    wp_load.

    awp_apply (array_unsafe_get_spec_atomic with "[//]") without "Hchannels_sender Hchannels_receiver HΦ"; first lia.
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (array_inv_model_agree with "Hstatuses_inv Hstatuses_model") as %Hstatuses1. simpl_length in Hstatuses1.
    destruct (lookup_lt_is_Some_2 statuses1 ₊j) as (status & Hstatuses1_lookup); first lia.
    rewrite /atomic_acc /=.
    iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
    repeat iExists _. iSplitL "Hstatuses_model".
    { iFrame. rewrite list_lookup_fmap_Some. iSteps. }
    iSplit; first iSteps. iIntros "Hstatuses_model". iMod "Hclose" as "_". iIntros "!>".
    iSplitL. { iFrameSteps. }
    iIntros "_ (Hchannels_sender & Hchannels_receiver & HΦ)".

    destruct status; wp_pures.

    - iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.

      iSteps.

    - wp_load.

      awp_apply (array_unsafe_cas_spec_atomic_inv with "Hrequests_inv"); first lia.
      iInv "Hinv" as "(:inv_inner =2)".
      iAaccIntro with "Hrequests_model"; first iSteps.
      rewrite -(list_fmap_insert _ _ _ (RequestSome _)).
      iIntros "%b % (%Hrequests2_lookup & %Hcas & Hrequests_model)".
      apply list_lookup_fmap_Some in Hrequests2_lookup as (request & Hrequests2_lookup & ->).
      destruct b.

      + iMod (channels_prepare (λ o, ws_queues_private_owner #l i_ Blocked ws -∗ Φ o)%I with "Hchannels_sender Hchannels_receiver") as "(Hchannels_sender & Hchannels_receiver)".
        iDestruct (big_sepL_insert ₊j (RequestSome i_) with "Hrequests [Hchannels_sender HΦ]") as "Hrequests".
        { eapply lookup_lt_Some. done. }
        { iSteps.
          rewrite /request_au. iAuIntro.
          iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (:model)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iAaccIntro with "Hmodels_auth"; first iSteps. iIntros (o) "Hmodels_auth".
          iExists o. iRevert "Hmodels_auth".
          destruct o; iSteps.
        }
        iSplitR "Hchannels_receiver". { iFrameSteps. }
        iIntros "!> _".

        wp_smart_apply (ws_queues_private_steal_to_0_spec with "[$Hmeta $Hl_responses $Hresponses_inv $Hinv $Hchannels_receiver]"); [lia.. |].
        iSteps.

      + iSplitR "Hchannels_sender Hchannels_receiver HΦ". { iFrameSteps. }
        iIntros "!> _".

        iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.

        iSteps.
  Qed.
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
        destruct_decide (i_ + 1 + j < sz).
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

From zoo_parabs Require
  ws_queues_private__opaque.
