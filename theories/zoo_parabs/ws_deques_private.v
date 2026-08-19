Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.iris.base_logic.lib.ghost_pred.
Require Import zoo.iris.base_logic.lib.ghost_list.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_parabs.base.
Require Export zoo_parabs.ws_deques_private__code.
Require Import zoo_parabs.ws_deques_private__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v t queue round backoff : val.
Implicit Type o : option val.
Implicit Type vs ws : list val.
Implicit Type vss wss : list (list val).
Implicit Type status : status.
Implicit Type statuses : list status.

Class WsDequesPrivateG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ws_deques_private۰G۰models۰G :: GhostListG Σ (list val)
  ; #[local] ws_deques_private۰G۰owner۰G :: TwinsG Σ (leibnizO status)
  ; #[local] ws_deques_private۰G۰channel۰pred۰G :: GhostPredG Σ (option val)
  ; #[local] ws_deques_private۰G۰channel۰generation۰G :: GhostVarG Σ (leibnizO gname)
  ; #[local] ws_deques_private۰G۰channel۰state۰G :: OneshotG Σ () (option val)
  }.

Definition ws_deques_private۰Σ :=
  #[ghost_list۰Σ (list val)
  ; twins۰Σ (leibnizO status)
  ; ghost_pred۰Σ (option val)
  ; ghost_var۰Σ (leibnizO gname)
  ; oneshot۰Σ () (option val)
  ].
#[global] Instance subGｰws_deques_private۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ws_deques_private۰Σ Σ →
  WsDequesPrivateG Σ.
Proof.
  solve_inG.
Qed.

#[local] Coercion status۰to_val status : val :=
  match status with
  | Blocked =>
      §Blocked
  | Nonblocked =>
      §Nonblocked
  end.

Variant request :=
  | RequestBlocked
  | RequestNone
  | RequestSome (i : nat).
Implicit Type request : request.
Implicit Type requests : list request.

#[local] Definition request۰to_val request : val :=
  match request with
  | RequestBlocked =>
      §RequestBlocked
  | RequestNone =>
      §RequestNone
  | RequestSome i =>
      ‘RequestSome( #i )
  end.

Variant response :=
  | ResponseWaiting
  | ResponseNone
  | ResponseSome v.
Implicit Type response : response.
Implicit Type responses : list response.

#[local] Coercion option۰to_response o :=
  match o with
  | None =>
      ResponseNone
  | Some v =>
      ResponseSome v
  end.
#[local] Definition response۰to_val response : val :=
  match response with
  | ResponseWaiting =>
      §ResponseWaiting
  | ResponseNone =>
      §ResponseNone
  | ResponseSome v =>
      ‘ResponseSome( v )
  end.

Section ws_deques_private۰G.
  Context `{ws_deques_private۰G : WsDequesPrivateG Σ}.

  Implicit Type Ψ : option val → iProp Σ.

  Record metadata :=
    { metadata۰queues۰array : val
    ; metadata۰queues : list val
    ; metadata۰statuses۰array : val
    ; metadata۰requests۰array : val
    ; metadata۰responses۰array : val
    ; metadata۰inv : namespace
    ; metadata۰size : nat
    ; metadata۰models : gname
    ; metadata۰owners : list gname
    ; metadata۰channels : list (gname * gname)
    }.
  Implicit Type γ : metadata.
  Implicit Type γ_owners : list gname.
  Implicit Type γ_channels : list (gname * gname).

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition models۰auth' γ_models sz vss : iProp Σ :=
    ghost_list۰auth γ_models vss ∗
    ⌜length vss = sz⌝.
  #[local] Definition models۰auth γ :=
    models۰auth' γ.(metadata۰models) γ.(metadata۰size).
  #[local] Instance : CustomIpat "models۰auth" :=
    " ( Hauth{_{}}
      & %Hvss{}
      )
    ".
  #[local] Definition models۰at' γ_models i :=
    ghost_list۰at γ_models i (DfracOwn 1).
  #[local] Definition models۰at γ :=
    models۰at' γ.(metadata۰models).

  #[local] Definition owner₁' γ_owners i status : iProp Σ :=
    ∃ γ_owner,
    ⌜γ_owners !! i = Some γ_owner⌝ ∗
    twins۰twin₁ γ_owner (DfracOwn 1) status.
  #[local] Definition owner₁ γ :=
    owner₁' γ.(metadata۰owners).
  #[local] Instance : CustomIpat "owner₁" :=
    " ( %γ_owner{_{}}
      & %Hlookup{_{}}
      & Htwin₁
      )
    ".
  #[local] Definition owner₂' γ_owners i status : iProp Σ :=
    ∃ γ_owner,
    ⌜γ_owners !! i = Some γ_owner⌝ ∗
    twins۰twin₂ γ_owner status.
  #[local] Definition owner₂ γ :=
    owner₂' γ.(metadata۰owners).
  #[local] Instance : CustomIpat "owner₂" :=
    " ( %γ_owner{_{}}
      & %Hlookup{_{}}
      & Htwin₂
      )
    ".

  #[local] Definition channels۰waiting' γ_channels i : iProp Σ :=
    ∃ γ_channel gen,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_var γ_channel.2 (DfracOwn (1/2)) gen ∗
    oneshot۰pending gen (DfracOwn 1) ().
  #[local] Definition channels۰waiting γ :=
    channels۰waiting' γ.(metadata۰channels).
  #[local] Instance : CustomIpat "channels۰waiting" :=
    " ( %γ_channel_{}
      & %gen{}
      & %Hlookup_{}
      & Hgeneration_{}
      & Hpending_{}
      )
    ".
  #[local] Definition channels۰sender' γ_channels i Ψ state : iProp Σ :=
    ∃ γ_channel,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_pred γ_channel.1 (DfracOwn (3/4)) Ψ ∗
    match state with
    | None =>
        True
    | Some o =>
        ∃ gen,
        ghost_var γ_channel.2 (DfracOwn (1/2)) gen ∗
        oneshot۰shot gen o
    end.
  #[local] Definition channels۰sender γ :=
    channels۰sender' γ.(metadata۰channels).
  #[local] Instance : CustomIpat "channels۰sender" :=
    " ( %γ_channel_{}
      & {>;}%Hlookup_{}
      & Hpred_{}
      & { {done}
          ( %gen{}
          & Hgeneration_{}
          & #Hshot_{}
          )
        ; _
        }
      )
    ".
  #[local] Definition channels۰receiver' γ_channels i Ψ state : iProp Σ :=
    ∃ γ_channel gen,
    ⌜γ_channels !! i = Some γ_channel⌝ ∗
    ghost_pred γ_channel.1 (DfracOwn (1/4)) Ψ ∗
    ghost_var γ_channel.2 (DfracOwn (1/2)) gen ∗
    match state with
    | None =>
        True
    | Some o =>
        oneshot۰shot gen o
    end.
  #[local] Definition channels۰receiver γ :=
    channels۰receiver' γ.(metadata۰channels).
  #[local] Instance : CustomIpat "channels۰receiver" :=
    " ( %γ_channel_{}
      & %gen{}
      & %Hlookup_{}
      & Hpred_{}
      & Hgeneration_{}
      & {{done}#Hshot_{};_}
      )
    ".

  #[local] Definition request۰au γ i Ψ : iProp Σ :=
    AU <{
      ∃∃ vss,
      models۰auth γ vss
    }> @ ⊤ ∖ ↑γ.(metadata۰inv), ∅ <{
      ∀∀ o,
      match o with
      | None =>
          models۰auth γ vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i = Some (v :: vs)⌝ ∗
          models۰auth γ (<[i := vs]> vss)
      end
    , COMM
      Ψ o
    }>.

  #[local] Definition request۰model۰blocked γ i : iProp Σ :=
    owner₂ γ i Blocked.
  #[local] Instance : CustomIpat "request۰model۰blocked" :=
    " {>;}Howner₂
    ".
  #[local] Definition request۰model۰nonblocked' γ i j : iProp Σ :=
    ∃ Ψ,
    ⌜j < γ.(metadata۰size)⌝ ∗
    channels۰sender γ j Ψ None ∗
    request۰au γ i Ψ.
  #[local] Instance : CustomIpat "request۰model۰nonblocked'" :=
    " ( %Χ
      & {>;}%
      & Hchannels_sender
      & HΧ
      )
    ".
  #[local] Definition request۰model۰nonblocked γ i j : iProp Σ :=
    owner₂ γ i Nonblocked ∗
    request۰model۰nonblocked' γ i j.
  #[local] Instance : CustomIpat "request۰model۰nonblocked" :=
    " ( {>;}Howner₂
      & (:request۰model۰nonblocked')
      )
    ".
  #[local] Definition request۰model γ i request : iProp Σ :=
    match request with
    | RequestSome j =>
          request۰model۰blocked γ i
        ∨ request۰model۰nonblocked γ i j
    | _ =>
        owner₂ γ i Nonblocked
    end.
  #[local] Instance : CustomIpat "request۰model" :=
    " [ (:request۰model۰blocked)
      | (:request۰model۰nonblocked)
      ]
    ".

  #[local] Definition response۰model γ i response : iProp Σ :=
    match response with
    | ResponseWaiting =>
        channels۰waiting γ i
    | ResponseNone =>
        ∃ Ψ,
        channels۰sender γ i Ψ (Some None) ∗
        Ψ None
    | ResponseSome v =>
        ∃ Ψ,
        channels۰sender γ i Ψ (Some $ Some v) ∗
        Ψ (Some v)
    end.
  #[local] Instance : CustomIpat "response۰model" :=
    " ( %Ψ{}
      & Hchannels_sender{_{}}
      & HΨ{}
      )
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ statuses requests responses,
    array۰model γ.(metadata۰statuses۰array) (DfracOwn 1) (status۰to_val <$> statuses) ∗
    array۰model γ.(metadata۰requests۰array) (DfracOwn 1) (request۰to_val <$> requests) ∗
    array۰model γ.(metadata۰responses۰array) (DfracOwn 1) (response۰to_val <$> responses) ∗
    ([∗ list] i ↦ request ∈ requests, request۰model γ i request) ∗
    ([∗ list] i ↦ response ∈ responses, response۰model γ i response).

  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %statuses{}
      & %requests{}
      & %responses{}
      & >Hstatuses_model
      & >Hrequests_model
      & >Hresponses_model
      & Hrequests
      & Hresponses
      )
    ".
  Definition ws_deques_private۰inv t ι (sz : nat) : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata۰inv)⌝ ∗
    ⌜sz = γ.(metadata۰size)⌝ ∗
    l ↪ γ ∗
    l.[size] ↦□ #γ.(metadata۰size) ∗
    l.[queues] ↦□ γ.(metadata۰queues۰array) ∗
    ⌜length γ.(metadata۰queues) = γ.(metadata۰size)⌝ ∗
    array۰model γ.(metadata۰queues۰array) DfracDiscarded γ.(metadata۰queues) ∗
    l.[statuses] ↦□ γ.(metadata۰statuses۰array) ∗
    array۰inv γ.(metadata۰statuses۰array) γ.(metadata۰size) ∗
    l.[requests] ↦□ γ.(metadata۰requests۰array) ∗
    array۰inv γ.(metadata۰requests۰array) γ.(metadata۰size) ∗
    l.[responses] ↦□ γ.(metadata۰responses۰array) ∗
    array۰inv γ.(metadata۰responses۰array) γ.(metadata۰size) ∗
    inv ι (inv۰inner γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Ht_eq{};->}
      & {%Hι_eq{};->}
      & {%Hsz_eq{};->}
      & #Hmeta{_{}}
      & #Hl{}_size
      & #Hl{}_queues
      & %Hqueues{}_length
      & #Hqueues{}_model
      & #Hl{}_statuses
      & #Hstatuses{}_inv
      & #Hl{}_requests
      & #Hrequests{}_inv
      & #Hl{}_responses
      & #Hresponses{}_inv
      & #Hinv{}
      )
    ".

  Definition ws_deques_private۰model t vss : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    models۰auth γ vss.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Hmodels_auth{_{}}
      )
    ".

  Definition ws_deques_private۰owner t i status ws : iProp Σ :=
    ∃ l γ queue vs Ψ_sender Ψ_receiver,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    ⌜γ.(metadata۰queues) !! i = Some queue⌝ ∗
    queue_3۰model queue vs ∗
    models۰at γ i vs ∗
    ⌜vs `suffix_of` ws⌝ ∗
    owner₁ γ i Nonblocked ∗
    channels۰sender γ i Ψ_sender None ∗
    channels۰receiver γ i Ψ_receiver None.
  #[local] Instance : CustomIpat "owner" :=
    " ( %l{;_}
      & %γ{;_}
      & %queue{}
      & %vs{}
      & %Ψ_sender{_{}}
      & %Ψ_receiver{_{}}
      & %Heq{}
      & #Hmeta_{}
      & %Hqueues_lookup{_{}}
      & Hqueue_model{_{}}
      & Hmodels_at{_{}}
      & %Hws{}
      & Howner₁{_{}}
      & Hchannels_sender{_{}}
      & Hchannels_receiver{_{}}
      )
    ".

  #[local] Instance owner₂ｰtimeless γ i status :
    Timeless (owner₂ γ i status).
  Proof.
    apply _.
  Qed.
  #[local] Instance channels۰waitingｰtimeless γ i :
    Timeless (channels۰waiting γ i).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deques_private۰modelｰtimeless t vss :
    Timeless (ws_deques_private۰model t vss).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_deques_private۰invｰpersistent t ι sz :
    Persistent (ws_deques_private۰inv t ι sz).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelsｰalloc sz :
    ⊢ |==>
      ∃ γ_models,
      models۰auth' γ_models sz (replicate sz []) ∗
      [∗ list] i ∈ seq 0 sz,
        models۰at' γ_models i [].
  Proof.
    iMod ghost_listｰalloc as "(%γ_models & $ & Hats)".
    iSplitR.
    - iPureIntro. apply length_replicate.
    - iApply (big_sepLｰreplicate₁ with "Hats").
  Qed.
  #[local] Lemma models۰authｰlength γ vss :
    models۰auth γ vss ⊢
    ⌜length vss = γ.(metadata۰size)⌝.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma modelsｰlookup γ vss i vs :
    models۰auth γ vss -∗
    models۰at γ i vs -∗
    ⌜vss !! i = Some vs⌝.
  Proof.
    iIntros "(:models۰auth) Hat".
    iApply (ghost_listｰlookup with "Hauth Hat").
  Qed.
  #[local] Lemma modelsｰupdate {γ vss i vs} vs' :
    models۰auth γ vss -∗
    models۰at γ i vs ==∗
      models۰auth γ (<[i := vs']> vss) ∗
      models۰at γ i vs'.
  Proof.
    iIntros "(:models۰auth) Hat".
    iMod (ghost_listｰupdateｰat with "Hauth Hat") as "($ & $)".
    iPureIntro. simp_length.
  Qed.

  Opaque models۰auth'.

  #[local] Lemma ownerｰalloc sz :
    ⊢ |==>
      ∃ γ_owners,
      ( [∗ list] i ∈ seq 0 sz,
        owner₁' γ_owners i Nonblocked
      ) ∗
      ( [∗ list] i ∈ seq 0 sz,
        owner₂' γ_owners i Nonblocked
      ).
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 sz,
        |==>
        ∃ γ_owner,
        twins۰twin₁ (twins۰G := ws_deques_private۰G۰owner۰G) γ_owner (DfracOwn 1) Nonblocked ∗
        twins۰twin₂ (twins۰G := ws_deques_private۰G۰owner۰G) γ_owner Nonblocked
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iApply twinsｰalloc'.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepLｰexists with "H") as "(%γ_owners & _ & H)".
    iDestruct (big_sepL2_sep with "H") as "(H1 & H2)".
    iDestruct (big_sepL2ｰretractｰr with "H1") as "(_ & H1)".
    iDestruct (big_sepL2ｰretractｰr with "H2") as "(_ & H2)".
    iDestruct (big_sepLｰseqｰindex₂ with "H1") as "H1".
    { simp_length. }
    iDestruct (big_sepLｰseqｰindex₂ with "H2") as "H2".
    { simp_length. }
    iSteps.
  Qed.
  #[local] Lemma ownerｰagree γ i status1 status2 :
    owner₁ γ i status1 -∗
    owner₂ γ i status2 -∗
    ⌜status1 = status2⌝.
  Proof.
    iIntros "(:owner₁ =1) (:owner₂ =2)". simp.
    iApply (twinsｰagreeｰL with "Htwin₁ Htwin₂").
  Qed.
  #[local] Lemma ownerｰupdate {γ i status1 status2} status :
    owner₁ γ i status1 -∗
    owner₂ γ i status2 ==∗
      owner₁ γ i status ∗
      owner₂ γ i status.
  Proof.
    iIntros "(:owner₁ =1) (:owner₂ =2)". simp.
    iMod (twinsｰupdate with "Htwin₁ Htwin₂") as "(Htwin₁ & Htwin₂)".
    iSteps.
  Qed.

  Opaque owner₁'.
  Opaque owner₂'.

  #[local] Lemma channelsｰalloc sz :
    ⊢ |==>
      ∃ γ_channels,
      ( [∗ list] i ∈ seq 0 sz,
        channels۰waiting' γ_channels i
      ) ∗
      ( [∗ list] i ∈ seq 0 sz,
        channels۰sender' γ_channels i inhabitant None ∗
        channels۰receiver' γ_channels i inhabitant None
      ).
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 sz,
        |==>
        ∃ γ_channel,
        ( ∃ gen,
          ghost_var (ghost_var۰G := ws_deques_private۰G۰channel۰generation۰G) γ_channel.2 (DfracOwn (1/2)) gen ∗
          oneshot۰pending gen (DfracOwn 1) ()
        ) ∗
        ( ∃ gen,
          ghost_pred γ_channel.1 (DfracOwn (3/4)) inhabitant ∗
          ghost_pred γ_channel.1 (DfracOwn (1/4)) inhabitant ∗
          ghost_var γ_channel.2 (DfracOwn (1/2)) gen
        )
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iMod (ghost_predｰalloc inhabitant) as "(%γ_pred & Hpred)".
      iEval (rewrite -Qp.three_quarter_quarter) in "Hpred". iDestruct "Hpred" as "(Hpred_1 & Hpred_2)".
      iMod (oneshotｰalloc ()) as "(%gen & Hpending)".
      iMod (ghost_varｰalloc (ghost_var۰G := ws_deques_private۰G۰channel۰generation۰G) gen) as "(%γ_state & Hgeneration_1 & Hgeneration_2)".
      iExists (γ_pred, γ_state). iSteps.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepLｰexists with "H") as "(%γ_channels & _ & H)".
    iDestruct (big_sepL2_sep with "H") as "(H1 & H2)".
    iDestruct (big_sepL2ｰretractｰr with "H1") as "(_ & H1)".
    iDestruct (big_sepL2ｰretractｰr with "H2") as "(_ & H2)".
    iDestruct (big_sepLｰseqｰindex₂ with "H1") as "H1".
    { simp_length. }
    iDestruct (big_sepLｰseqｰindex₂ with "H2") as "H2".
    { simp_length. }
    iExists γ_channels. iSplitL "H1".
    1: iApply (big_sepL_impl with "H1").
    2: iApply (big_sepL_impl with "H2").
    all: iSteps.
  Qed.
  #[local] Lemma channels۰senderｰexclusive γ i Ψ1 state1 Ψ2 state2 :
    channels۰sender γ i Ψ1 state1 -∗
    channels۰sender γ i Ψ2 state2 -∗
    False.
  Proof.
    iIntros "(:channels۰sender =1) (:channels۰sender =2)". simp.
    iDestruct (ghost_predｰdfracｰne with "Hpred_1 Hpred_2") as %?; naive_solver.
  Qed.
  #[local] Lemma channelsｰwaitingｰreceiver γ i Ψ o :
    ▷ channels۰waiting γ i -∗
    channels۰receiver γ i Ψ (Some o) -∗
    ◇ False.
  Proof.
    iIntros ">(:channels۰waiting =1) (:channels۰receiver =2 done=)". simp.
    iDestruct (ghost_varｰagreeｰL with "Hgeneration_1 Hgeneration_2") as %<-.
    iApply (oneshotｰpendingｰshot with "Hpending_1 Hshot_2").
  Qed.
  #[local] Lemma channelsｰsenderｰreceiverｰagree γ i Ψ1 o1 Ψ2 o2 E :
    ▷ channels۰sender γ i Ψ1 (Some o1) -∗
    channels۰receiver γ i Ψ2 (Some o2) ={E}=∗
      ▷^2 (Ψ1 o1 ≡ Ψ2 o1) ∗
      ⌜o1 = o2⌝ ∗
      ▷ channels۰sender γ i Ψ1 (Some o1) ∗
      channels۰receiver γ i Ψ2 (Some o1).
  Proof.
    iIntros "(:channels۰sender =1 > done=) (:channels۰receiver =2 done=)". simp.
    iDestruct "Hgeneration_1" as ">Hgeneration_1".
    iDestruct "Hshot_1" as ">Hshot_1".
    iDestruct (ghost_predｰagree o1 with "Hpred_1 [$Hpred_2]") as "#Heq".
    iDestruct (ghost_varｰagreeｰL with "Hgeneration_1 Hgeneration_2") as %<-.
    iDestruct (oneshot۰shotｰagree with "Hshot_1 Hshot_2") as %<-.
    iFrame "#∗". iSteps.
  Qed.
  #[local] Lemma channelsｰprepare {γ i Ψ1 Ψ2} Ψ :
    channels۰sender γ i Ψ1 None -∗
    channels۰receiver γ i Ψ2 None ==∗
      channels۰sender γ i Ψ None ∗
      channels۰receiver γ i Ψ None.
  Proof.
    iIntros "(:channels۰sender =1) (:channels۰receiver =2)". simp.
    iDestruct (ghost_predｰcombine inhabitant with "Hpred_1 Hpred_2") as "(_ & Hpred)". rewrite dfrac_op_own Qp.three_quarter_quarter.
    iMod (ghost_predｰupdate Ψ with "Hpred") as "Hpred".
    iEval (rewrite -Qp.three_quarter_quarter) in "Hpred". iDestruct "Hpred" as "(Hpred_1 & Hpred_2)".
    iSteps.
  Qed.
  #[local] Lemma channelsｰsend {γ i Ψ} o :
    channels۰waiting γ i -∗
    channels۰sender γ i Ψ None ==∗
    channels۰sender γ i Ψ (Some o).
  Proof.
    iIntros "(:channels۰waiting =1) (:channels۰sender =2)". simp.
    iMod (oneshotｰupdateｰshot o with "Hpending_1") as "#Hshot".
    iSteps.
  Qed.
  #[local] Lemma channelsｰreceive γ i Ψ1 Ψ2 o :
    ▷ channels۰sender γ i Ψ1 (Some o) -∗
    channels۰receiver γ i Ψ2 None -∗
    ◇ (
      ▷ channels۰sender γ i Ψ1 (Some o) ∗
      channels۰receiver γ i Ψ2 (Some o)
    ).
  Proof.
    iIntros "(:channels۰sender =1 > done=) (:channels۰receiver =2)". simp.
    iDestruct "Hgeneration_1" as ">Hgeneration_1".
    iDestruct "Hshot_1" as ">Hshot_1".
    iDestruct (ghost_varｰagreeｰL with "Hgeneration_1 Hgeneration_2") as %<-.
    iModIntro. iFrameSteps.
  Qed.
  #[local] Lemma channelsｰreset γ i Ψ1 o1 Ψ2 o2 E :
    ▷ channels۰sender γ i Ψ1 (Some o1) -∗
    channels۰receiver γ i Ψ2 (Some o2) ={E}=∗
      channels۰waiting γ i ∗
      ▷ channels۰sender γ i Ψ1 None ∗
      channels۰receiver γ i Ψ2 None.
  Proof.
    iIntros "(:channels۰sender =1 > done=) (:channels۰receiver =2)". simp.
    iDestruct "Hgeneration_1" as ">Hgeneration_1".
    iMod (oneshotｰalloc ()) as "(%gen & Hpending)".
    iDestruct (ghost_varｰcombine with "Hgeneration_1 Hgeneration_2") as "(_ & Hgeneration)". rewrite dfrac_op_own Qp.half_half.
    iMod (ghost_varｰupdate (ghost_var۰G := ws_deques_private۰G۰channel۰generation۰G) gen with "Hgeneration") as "Hgeneration".
    iDestruct "Hgeneration" as "(Hgeneration_1 & Hgeneration_2)".
    iSteps.
  Qed.

  Opaque channels۰waiting'.
  Opaque channels۰sender'.
  Opaque channels۰receiver'.

  #[local] Lemma request۰modelｰupdate {γ i request} request' :
    (request' = RequestBlocked ∨ request' = RequestNone) →
    ▷ request۰model γ i request -∗
    owner₁ γ i Nonblocked -∗
    ◇ (
      ▷ request۰model γ i request' ∗
      owner₁ γ i Nonblocked ∗
      if request is RequestSome j then
        ▷ request۰model۰nonblocked' γ i j
      else
        True
    ).
  Proof.
    iIntros "%Hrequest' Hrequest Howner₁".
    destruct request as [| | j].
    1,2: iFrame; naive_solver.
    iDestruct "Hrequest" as "(:request۰model >)".
    - iDestruct (ownerｰagree with "Howner₁ Howner₂") as %[=].
    - iFrame. naive_solver.
  Qed.
  #[local] Lemma request۰modelｰrespond γ i request :
    ▷ request۰model γ i request -∗
    owner₁ γ i Nonblocked ==∗
    ◇ (
      ▷ request۰model γ i request ∗
      if request is RequestSome j then
        owner₁ γ i Blocked ∗
        ▷ request۰model۰nonblocked' γ i j
      else
        owner₁ γ i Nonblocked
    ).
  Proof.
    iIntros "Hrequest Howner₁".
    destruct request as [| | j].
    1,2: iFrame; naive_solver.
    iDestruct "Hrequest" as "(:request۰model >)".
    - iDestruct (ownerｰagree with "Howner₁ Howner₂") as %[=].
    - iMod (ownerｰupdate Blocked with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iFrameSteps.
  Qed.
  #[local] Lemma request۰modelｰunblock γ i request :
    ▷ request۰model γ i request -∗
    owner₁ γ i Blocked ==∗
    ◇ (
      ▷ request۰model γ i RequestNone ∗
      owner₁ γ i Nonblocked
    ).
  Proof.
    iIntros "Hrequest Howner₁".
    destruct request as [| | j].
    1,2: iDestruct "Hrequest" as ">Howner₂".
    1,2: iDestruct (ownerｰagree with "Howner₁ Howner₂") as %[=].
    iDestruct "Hrequest" as "(:request۰model >)".
    - iMod (ownerｰupdate with "Howner₁ Howner₂") as "(Howner₁ & Howner₂)".
      iFrameSteps.
    - iDestruct (ownerｰagree with "Howner₁ Howner₂") as %[=].
  Qed.

  #[local] Lemma response۰modelｰsender γ i response Ψ state :
    ▷ response۰model γ i response -∗
    channels۰sender γ i Ψ state -∗
    ◇ (
      ⌜response = ResponseWaiting⌝ ∗
      channels۰waiting γ i ∗
      channels۰sender γ i Ψ state
    ).
  Proof.
    iIntros "Hresponse Hchannels_sender".
    destruct response.
    1: iDestruct "Hresponse" as ">Hresponse".
    1: iModIntro; iSteps.
    all: iDestruct "Hresponse" as "(:response۰model =1)".
    all: iDestruct (channels۰senderｰexclusive with "Hchannels_sender Hchannels_sender_1") as ">%".
    all: done.
  Qed.
  #[local] Lemma response۰modelｰreceiver γ i response Ψ o E :
    ▷ response۰model γ i response -∗
    channels۰receiver γ i Ψ (Some o) ={E}=∗
      ∃ Ψ_,
      ▷^2 (Ψ_ o ≡ Ψ o) ∗
      ⌜response = o⌝ ∗
      ▷ channels۰sender γ i Ψ_ (Some o) ∗
      channels۰receiver γ i Ψ (Some o) ∗
      ▷ Ψ_ o.
  Proof.
    iIntros "Hresponse Hchannels_receiver".
    destruct response.
    1: iMod (channelsｰwaitingｰreceiver with "Hresponse Hchannels_receiver") as %[].
    all: iDestruct "Hresponse" as "(:response۰model =1)".
    all: iMod (channelsｰsenderｰreceiverｰagree with "Hchannels_sender_1 Hchannels_receiver") as "(Heq & <- & $ & $)".
    all: iFrame "#∗"; iSteps.
  Qed.

  Lemma ws_deques_private۰invｰagree t ι1 sz1 ι2 sz2 :
    ws_deques_private۰inv t ι1 sz1 -∗
    ws_deques_private۰inv t ι2 sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simp.
    iDestruct (pointstoｰagree with "Hl1_size Hl2_size") as %?. naive_solver.
  Qed.

  Lemma ws_deques_private۰ownerｰexclusive t i status1 ws1 status2 ws2 :
    ws_deques_private۰owner t i status1 ws1 -∗
    ws_deques_private۰owner t i status2 ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. simp.
    iApply (queue_3۰modelｰexclusive with "Hqueue_model_1 Hqueue_model_2").
  Qed.

  Lemma ws_deques_privateｰinvｰmodel t ι sz vss :
    ws_deques_private۰inv t ι sz -∗
    ws_deques_private۰model t vss -∗
    ⌜length vss = sz⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-.
    iApply (models۰authｰlength with "Hmodels_auth").
  Qed.
  Lemma ws_deques_privateｰinvｰowner t ι sz i status ws :
    ws_deques_private۰inv t ι sz -∗
    ws_deques_private۰owner t i status ws -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-.
    apply lookup_lt_Some in Hqueues_lookup.
    iSteps.
  Qed.

  Lemma ws_deques_privateｰmodelｰowner t vss i status ws :
    ws_deques_private۰model t vss -∗
    ws_deques_private۰owner t i status ws -∗
      ∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:model =1) (:owner =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. simp.
    iDestruct (modelsｰlookup with "Hmodels_auth_1 Hmodels_at_2") as %Hlookup.
    iSteps.
  Qed.

  Lemma ws_deques_private٠createｰspec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_deques_private٠create #sz
    {{{
      t
    , RET t;
      ws_deques_private۰inv t ι ₊sz ∗
      ws_deques_private۰model t (replicate ₊sz []) ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_deques_private۰owner t i Nonblocked []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.
    wp۰apply (array٠unsafe_makeｰspec with "[//]") as (responses_array) "Hresponses_model"; first done.
    iDestruct (array۰modelｰtoｰinv with "Hresponses_model") as "#Hresponses_inv".
    wp۰apply (array٠makeｰspec with "[//]") as (requests_array) "(_ & Hrequests_model)".
    iDestruct (array۰modelｰtoｰinv with "Hrequests_model") as "#Hrequests_inv".
    wp۰apply (array٠unsafe_makeｰspec with "[//]") as (statuses_array) "Hstatuses_model"; first done.
    iDestruct (array۰modelｰtoｰinv with "Hstatuses_model") as "#Hstatuses_inv".
    wp۰apply (array٠unsafe_initｰspecｰdisentangled (λ _ queue, queue_3۰model queue [])) as (queues_array queues) "(%Hqueues_length & Hqueues_model & Hqueues)"; first done.
    { iIntros "!> %i %Hi".
      wp۰apply (queue_3٠createｰspec with "[//]").
      iSteps.
    }
    iDestruct (array۰modelｰtoｰinv with "Hqueues_model") as "#Hqueues_inv".
    iMod (array۰modelｰpersist with "Hqueues_model") as "#Hqueues_model".
    wp۰block l as "Hmeta" "#Hl_size #Hl_queues #Hl_statuses #Hl_requests #Hl_responses".

    iMod modelsｰalloc as "(%γ_models & Hmodels_auth & Hmodels_ats)".
    iMod ownerｰalloc as "(%γ_owners & Howners₁ & Howners₂)".
    iMod channelsｰalloc as "(%γ_channels & Hchannels_1 & Hchannels_2)".

    pose γ :=
      {|metadata۰queues۰array := queues_array
      ; metadata۰queues := queues
      ; metadata۰statuses۰array := statuses_array
      ; metadata۰requests۰array := requests_array
      ; metadata۰responses۰array := responses_array
      ; metadata۰size := ₊sz
      ; metadata۰inv := ι
      ; metadata۰models := γ_models
      ; metadata۰owners := γ_owners
      ; metadata۰channels := γ_channels
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodels_auth Hqueues Hmodels_ats Howners₁ Hchannels_2".

    - rewrite Hqueues_length. simp_length.
      iEval (rewrite -(fmap_replicate status۰to_val _ Nonblocked)) in "Hstatuses_model".
      iEval (rewrite -(fmap_replicate request۰to_val _ RequestNone)) in "Hrequests_model".
      iEval (rewrite -(fmap_replicate response۰to_val _ ResponseWaiting)) in "Hresponses_model".
      iExists l, γ. rewrite Z2Nat.id //. iStep 14.
      iApply inv_alloc.
      iSteps. iSplitL "Howners₂" => /=.
      + iApply big_sepLｰreplicate₂.
        iApply (big_sepL_impl with "Howners₂").
        iSteps.
      + rewrite big_sepLｰreplicate.
        iApply (big_sepL_impl with "Hchannels_1").
        iSteps.

    - iSteps.
      iDestruct (big_sepL_sep_2 with "Hmodels_ats Howners₁") as "H".
      iDestruct (big_sepL_sep_2 with "H Hchannels_2") as "H".
      iDestruct (big_sepLｰtoｰseqｰ0 with "Hqueues") as "Hqueues". rewrite Hqueues_length.
      iDestruct (big_sepL_sep_2 with "Hqueues H") as "H".
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_deques_private٠sizeｰspec t ι sz :
    {{{
      ws_deques_private۰inv t ι sz
    }}}
      ws_deques_private٠size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    iSteps.
  Qed.

  Lemma ws_deques_private٠blockｰspec t ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Nonblocked ws
    }}}
      ws_deques_private٠block t #i
    {{{
      RET ();
      ws_deques_private۰owner t i_ Blocked ws
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp۰rec.
    iApply (wpｰframeｰwand with "[- Howner₁]"); first iAccu.
    wp۰load.

    awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hstatuses_inv") without "Howner₁"; first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iAaccIntro with "Hstatuses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ Blocked).
    iIntros "%𝑠𝑡𝑎𝑡𝑢𝑠 (_ & Hstatuses_model) !>".
    iSplitL. { iFrameSteps. }
    iIntros "_ Howner₁".

    wp۰load.

    awp۰apply (array٠unsafe_xchgｰspecｰatomicｰinv with "Hrequests_inv"); first lia.
    iInv "Hinv" as "(:inv۰inner =2)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ RequestBlocked).
    iIntros "%𝑟𝑒𝑞𝑢𝑒𝑠𝑡 (%Hrequests2_lookup & Hrequests_model)".
    apply list_lookup_fmap_Some in Hrequests2_lookup as (request & -> & Hrequests2_lookup).
    iDestruct (big_sepL_insert_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
    iMod (request۰modelｰupdate RequestBlocked with "Hrequest Howner₁") as "(Hrequest & Howner₁ & H)"; first auto.
    iDestruct ("Hrequests" $! RequestBlocked with "Hrequest") as "Hrequests".
    iSplitR "Howner₁ H". { iFrameSteps. }
    iIntros "!> _".

    destruct request as [| | j]; [iSteps.. |].
    iDestruct "H" as "(:request۰model۰nonblocked' >)".

    wp۰load.

    iApply fupdｰwp.
    iMod "HΧ" as "(%vss & Hmodels_auth & _ & HΧ)".
    iMod ("HΧ" $! None with "Hmodels_auth") as "HΧ".
    iModIntro.

    awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hresponses_inv") without "Howner₁"; first lia.
    iInv "Hinv" as "(:inv۰inner =3)".
    iAaccIntro with "Hresponses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseNone).
    iIntros "%𝑟𝑒𝑠𝑝𝑜𝑛𝑠𝑒 (%Hresponses3_lookup & Hresponses_model)".
    apply list_lookup_fmap_Some_1 in Hresponses3_lookup as (reponse & -> & Hresponses3_lookup).
    iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
    iMod (response۰modelｰsender with "Hresponse Hchannels_sender") as "(-> & Hchannels_waiting & Hchannels_sender)".
    iMod (channelsｰsend with "Hchannels_waiting Hchannels_sender") as "Hchannels_sender".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.

  Lemma ws_deques_private٠unblockｰspec t ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Blocked ws
    }}}
      ws_deques_private٠unblock t #i
    {{{
      RET ();
      ws_deques_private۰owner t i_ Nonblocked ws
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp۰rec.
    iApply (wpｰframeｰwand with "[- Howner₁]"); first iAccu.
    wp۰load.

    awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hrequests_inv"); first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ RequestNone).
    iIntros "%𝑟𝑒𝑞𝑢𝑒𝑠𝑡 (%Hrequests1_lookup & Hrequests_model)".
    apply list_lookup_fmap_Some_1 in Hrequests1_lookup as (request & -> & Hrequests1_lookup).
    iDestruct (big_sepL_insert_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
    iMod (request۰modelｰupdate RequestNone with "Hrequest Howner₁") as "(Hrequest & Howner₁ & H)"; first auto.
    iDestruct ("Hrequests" $! RequestNone with "Hrequest") as "Hrequests".
    iSplitR "Howner₁". { iFrameSteps. }
    iIntros "!> _".

    wp۰load.

    awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hstatuses_inv") without "Howner₁"; first lia.
    iInv "Hinv" as "(:inv۰inner =2)".
    iAaccIntro with "Hstatuses_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ Nonblocked).
    iIntros "%𝑠𝑡𝑎𝑡𝑢𝑠 (_ & Hstatuses_model) !>".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma ws_deques_private٠respondｰspec {t ι sz i i_} ws :
    i = ⁺i_ →
    {{{
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Nonblocked ws
    }}}
      ws_deques_private٠respond t #i
    {{{
      RET ();
      ws_deques_private۰owner t i_ Nonblocked ws
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp۰rec.
    iApply (wpｰframeｰwand with "[- Hqueue_model Hmodels_at Howner₁]"); first iAccu.
    wp۰load.

    awp۰apply (array٠unsafe_getｰspecｰatomicｰinv with "Hrequests_inv") without "Hqueue_model Hmodels_at"; first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id.
    iIntros "%𝑟𝑒𝑞𝑢𝑒𝑠𝑡 (%Hrequests1_lookup & Hrequests_model)".
    apply list_lookup_fmap_Some in Hrequests1_lookup as (request & -> & Hrequests1_lookup).
    iDestruct (big_sepL_lookup_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
    iMod (request۰modelｰrespond with "Hrequest Howner₁") as ">(Hrequest & H)".
    iDestruct ("Hrequests" with "Hrequest") as "Hrequests".
    iSplitR "H". { iFrameSteps. }
    iIntros "!> _ (Hqueue_model & Hmodels_at)".

    destruct request as [| | j]; [iSteps.. |].
    iDestruct "H" as "(Howner₁ & (:request۰model۰nonblocked' >))".

    wp۰load.
    wp۰apply (array٠unsafe_getｰspec with "Hqueues_model") as "_"; [lia | done | lia |].
    wp۰apply (queue_3٠pop_frontｰspec with "Hqueue_model") as "Hqueue_model".

    wp۰bind (Match _ _ _ _).
    wp۰apply (wpｰwand (λ res,
      ⌜res = response۰to_val $ head vs⌝
    )%I) as "%res ->".
    { destruct vs; iSteps. }

    wp۰load.

    awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hresponses_inv") without "Hqueue_model Howner₁"; first lia.
    iInv "Hinv" as "(:inv۰inner =2)".
    iAaccIntro with "Hresponses_model"; first iSteps.
    rewrite Nat2Z.id -list_fmap_insert.
    iIntros "%𝑟𝑒𝑠𝑝𝑜𝑛𝑠𝑒 (%Hresponses2_lookup & Hresponses_model)".
    apply list_lookup_fmap_Some in Hresponses2_lookup as (response & -> & Hresponses2_lookup).
    iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
    iMod (response۰modelｰsender with "Hresponse Hchannels_sender") as "(-> & Hchannels_waiting & Hchannels_sender)".
    iMod (channelsｰsend (head vs) with "Hchannels_waiting Hchannels_sender") as "Hchannels_sender".

    iAssert (
      |={_}=>
      models۰at γ i_ (tail vs) ∗
      response۰model γ j (head vs)
    )%I with "[Hmodels_at Hchannels_sender HΧ]" as ">(Hmodels_at & Hresponse)".
    { iMod "HΧ" as "(%vss & Hmodels_auth & _ & HΧ)".
      iDestruct (modelsｰlookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
      destruct vs as [| v vs]; first iSteps.
      iMod (modelsｰupdate vs with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
      iMod ("HΧ" $! (Some v) with "[$Hmodels_auth //]") as "HΧ".
      iSteps.
    }

    iSplitR "Hmodels_at". { iFrameSteps. }
    iIntros "!> _ (Hqueue_model & Howner₁)".

    wp۰load.

    awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hrequests_inv") without "Hqueue_model Hmodels_at"; first lia.
    iInv "Hinv" as "(:inv۰inner =3)".
    iAaccIntro with "Hrequests_model"; first iSteps.
    rewrite Nat2Z.id -(list_fmap_insert _ _ _ RequestNone).
    iIntros "%𝑟𝑒𝑞𝑢𝑒𝑠𝑡 (%Hrequests3_lookup & Hrequests_model)".
    apply list_lookup_fmap_Some_1 in Hrequests3_lookup as (request & -> & Hrequests3_lookup).
    iDestruct (big_sepL_insert_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
    iMod (request۰modelｰunblock with "Hrequest Howner₁") as ">(Hrequest & Howner₁)".
    iDestruct ("Hrequests" $! RequestNone with "Hrequest") as "Hrequests".
    iSplitR "Howner₁". { iFrameSteps. }
    iIntros "!> _".

    iSteps. iPureIntro. apply suffixｰtail. done.
  Qed.

  Lemma ws_deques_private٠pushｰspec t ι sz i i_ ws v :
    i = ⁺i_ →
    <<<
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Nonblocked ws
    | ∀∀ vss,
      ws_deques_private۰model t vss
    >>>
      ws_deques_private٠push t #i v
      @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deques_private۰model t (<[i_ := vs ++ [v]]> vss)
    | RET ();
      ws_deques_private۰owner t i_ Nonblocked (vs ++ [v])
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_getｰspec with "Hqueues_model") as "_"; [lia | done | lia |].
    wp۰apply (queue_3٠pushｰspec with "Hqueue_model") as "Hqueue_model".

    iApply fupdｰwp.
    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelsｰlookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
    iMod (modelsｰupdate (vs ++ [v]) with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
    iMod ("HΦ" with "[Hmodels_auth]") as "HΦ"; first iSteps.
    iModIntro.

    wp۰apply+ (ws_deques_private٠respondｰspec with "[- HΦ] HΦ"); [done | iFrameSteps].
  Qed.

  Lemma ws_deques_private٠popｰspec t ι sz i i_ ws :
    i = ⁺i_ →
    <<<
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Nonblocked ws
    | ∀∀ vss,
      ws_deques_private۰model t vss
    >>>
      ws_deques_private٠pop t #i
      @ ↑ι
    <<<
      ∃∃ o ws',
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_deques_private۰model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ⌜vs ++ [v] `suffix_of` ws⌝ ∗
          ⌜ws' = vs⌝ ∗
          ws_deques_private۰model t (<[i_ := vs]> vss)
      end
    | RET o;
      ws_deques_private۰owner t i_ Nonblocked ws'
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_getｰspec with "Hqueues_model") as "_"; [lia | done | lia |].
    wp۰apply (queue_3٠pop_backｰspec with "Hqueue_model") as (o) "Hqueue_model".

    iApply fupdｰwp.
    iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelsｰlookup with "Hmodels_auth Hmodels_at") as %Hvss_lookup.
    destruct o as [v |].

    - iDestruct "Hqueue_model" as "(%vs' & -> & Hqueue_model)".
      iMod (modelsｰupdate vs' with "Hmodels_auth Hmodels_at") as "(Hmodels_auth & Hmodels_at)".
      iMod ("HΦ" $! (Some v) with "[Hmodels_auth]") as "HΦ"; first iSteps.
      iModIntro.

      wp۰apply+ (ws_deques_private٠respondｰspec with "[- HΦ]") as "Howner"; [done | iFrameSteps |].
      wp۰pures.
      iApply ("HΦ" with "Howner").

    - iDestruct "Hqueue_model" as "(-> & Hqueue_model)".
      iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.
      iModIntro.

      wp۰apply+ (ws_deques_private٠respondｰspec [] with "[- HΦ]") as "Howner"; [done | iFrameSteps |].
      wp۰pures.
      iApply ("HΦ" with "Howner").
  Qed.

  #[local] Lemma ws_deques_private٠steal_to₂ｰspec l γ i i_ Ψ backoff :
    i = ⁺i_ →
    i_ < γ.(metadata۰size) →
    {{{
      l ↪ γ ∗
      l.[responses] ↦□ γ.(metadata۰responses۰array) ∗
      array۰inv γ.(metadata۰responses۰array) γ.(metadata۰size) ∗
      inv γ.(metadata۰inv) (inv۰inner γ) ∗
      channels۰receiver γ i_ Ψ None ∗
      backoff۰model backoff
    }}}
      ws_deques_private٠steal_to₂ #l #i backoff
    {{{
      o Ψ_sender Ψ_receiver
    , RET o;
      channels۰sender γ i_ Ψ_sender None ∗
      channels۰receiver γ i_ Ψ_receiver None ∗
      Ψ o
    }}}.
  Proof.
    iIntros (-> Hi) "%Φ (#Hmeta & #Hl_responses & #Hresponses_inv & #Hinv & Hchannels_receiver & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec. wp۰load.

    awp۰apply (array٠unsafe_getｰspecｰatomicｰinv with "Hresponses_inv") without "HΦ"; first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iAaccIntro with "Hresponses_model"; first iSteps.
    rewrite Nat2Z.id.
    iIntros "%𝑟𝑒𝑠𝑝𝑜𝑛𝑠𝑒 (%Hresponses1_lookup & Hresponses_model)".
    apply list_lookup_fmap_Some in Hresponses1_lookup as (response & -> & Hresponses1_lookup).
    destruct response as [| | v].

    - iSplitR "Hchannels_receiver Hbackoff". { iFrameSteps. }
      iIntros "!> _ HΦ".

      wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as "{% backoff} %backoff Hbackoff".
      wp۰apply+ ("HLöb" with "Hchannels_receiver Hbackoff HΦ").

    - iDestruct (big_sepL_lookup_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iDestruct "Hresponse" as "(:response۰model =1)".
      iMod (channelsｰreceive with "Hchannels_sender_1 Hchannels_receiver") as "(Hchannels_sender & Hchannels_receiver)".
      iSplitR "Hchannels_receiver". { iFrameSteps. }
      iIntros "!> _ HΦ".

      wp۰load.

      awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hresponses_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iAaccIntro with "Hresponses_model"; first iSteps.
      rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseWaiting).
      iIntros "%𝑟𝑒𝑠𝑝𝑜𝑛𝑠𝑒 (%Hresponses2_lookup & Hresponses_model)".
      apply list_lookup_fmap_Some in Hresponses2_lookup as (response & -> & Hresponses2_lookup).
      iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iMod (response۰modelｰreceiver with "Hresponse Hchannels_receiver") as "(%Ψ_ & Heq & -> & Hchannels_sender & Hchannels_receiver & HΨ)".
      iMod (channelsｰreset with "Hchannels_sender Hchannels_receiver") as "(Hchannels_waiting & Hchannels_sender & Hchannels_receiver)".
      iDestruct ("Hresponses" $! ResponseWaiting with "[$Hchannels_waiting]") as "Hresponses".
      iSplitR "Hchannels_sender Hchannels_receiver Heq HΨ". { iFrameSteps. }
      iIntros "!> H£ HΦ".

      wp۰pures.
      iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
      iRewrite "Heq" in "HΨ".
      iApply ("HΦ" $! None).
      iSteps.

    - iDestruct (big_sepL_lookup_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iDestruct "Hresponse" as "(:response۰model =1)".
      iMod (channelsｰreceive with "Hchannels_sender_1 Hchannels_receiver") as "(Hchannels_sender & Hchannels_receiver)".
      iSplitR "Hchannels_receiver". { iFrameSteps. }
      iIntros "!> _ HΦ".

      wp۰load.

      awp۰apply (array٠unsafe_setｰspecｰatomicｰinv with "Hresponses_inv") without "HΦ"; first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iAaccIntro with "Hresponses_model"; first iSteps.
      rewrite Nat2Z.id -(list_fmap_insert _ _ _ ResponseWaiting).
      iIntros "%𝑟𝑒𝑠𝑝𝑜𝑛𝑠𝑒 (%Hresponses2_lookup & Hresponses_model)".
      apply list_lookup_fmap_Some in Hresponses2_lookup as (response & -> & Hresponses2_lookup).
      iDestruct (big_sepL_insert_acc with "Hresponses") as "(Hresponse & Hresponses)"; first done.
      iMod (response۰modelｰreceiver with "Hresponse Hchannels_receiver") as "(%Ψ_ & Heq & -> & Hchannels_sender & Hchannels_receiver & HΨ)".
      iMod (channelsｰreset with "Hchannels_sender Hchannels_receiver") as "(Hchannels_waiting & Hchannels_sender & Hchannels_receiver)".
      iDestruct ("Hresponses" $! ResponseWaiting with "[$Hchannels_waiting]") as "Hresponses".
      iSplitR "Hchannels_sender Hchannels_receiver Heq HΨ". { iFrameSteps. }
      iIntros "!> H£ HΦ".

      wp۰pures.
      iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
      iRewrite "Heq" in "HΨ".
      iApply ("HΦ" $! (Some v)).
      iSteps.
  Qed.

  #[local] Lemma ws_deques_private٠steal_to₁ｰspec l γ i i_ Ψ :
    i = ⁺i_ →
    i_ < γ.(metadata۰size) →
    {{{
      l ↪ γ ∗
      l.[responses] ↦□ γ.(metadata۰responses۰array) ∗
      array۰inv γ.(metadata۰responses۰array) γ.(metadata۰size) ∗
      inv γ.(metadata۰inv) (inv۰inner γ) ∗
      channels۰receiver γ i_ Ψ None
    }}}
      ws_deques_private٠steal_to₁ #l #i
    {{{
      o Ψ_sender Ψ_receiver
    , RET o;
      channels۰sender γ i_ Ψ_sender None ∗
      channels۰receiver γ i_ Ψ_receiver None ∗
      Ψ o
    }}}.
  Proof.
    iIntros (-> Hi) "%Φ (Hmeta & Hl_responses & Hresponses_inv & Hinv & Hchannels_receiver) HΦ".

    wp۰rec.
    wp۰apply+ (ws_deques_private٠steal_to₂ｰspec with "[- HΦ] HΦ"). 1,2: done. 1: iFrameSteps.
  Qed.
  Lemma ws_deques_private٠steal_toｰspec t ι (sz : nat) i i_ ws j :
    i = ⁺i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Blocked ws
    | ∀∀ vss,
      ws_deques_private۰model t vss
    >>>
      ws_deques_private٠steal_to t #i #j
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_private۰model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! ₊j = Some (v :: vs)⌝ ∗
          ws_deques_private۰model t (<[₊j := vs]> vss)
      end
    | RET o;
      ws_deques_private۰owner t i_ Blocked ws
    >>>.
  Proof.
    iIntros (-> Hj) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    opose proof* lookup_lt_Some; first done.

    wp۰rec.
    iApply (wpｰframeｰwand with "[- Hchannels_sender Hchannels_receiver HΦ]"); first iAccu.
    wp۰load.

    awp۰apply (array٠unsafe_getｰspecｰatomicｰinv with "Hstatuses_inv") without "Hchannels_sender Hchannels_receiver HΦ"; first lia.
    iInv "Hinv" as "(:inv۰inner =1)".
    iAaccIntro with "Hstatuses_model"; first iSteps.
    iIntros "%𝑠𝑡𝑎𝑡𝑢𝑠 (%Hstatuses1_lookup & Hstatuses_model) !>".
    apply list_lookup_fmap_Some in Hstatuses1_lookup as (status & -> & Hstatuses1_lookup).
    iSplitL. { iFrameSteps. }
    iIntros "_ (Hchannels_sender & Hchannels_receiver & HΦ)".

    destruct status; wp۰pures.

    - iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.

      iSteps.

    - wp۰load.

      awp۰apply (array٠unsafe_casｰspecｰatomicｰinv with "Hrequests_inv"); first lia.
      iInv "Hinv" as "(:inv۰inner =2)".
      iAaccIntro with "Hrequests_model"; first iSteps.
      rewrite -(list_fmap_insert _ _ _ (RequestSome _)).
      iIntros "%b %𝑟𝑒𝑞𝑢𝑒𝑠𝑡 (%Hrequests2_lookup & %Hcas & Hrequests_model)".
      apply list_lookup_fmap_Some in Hrequests2_lookup as (request & -> & Hrequests2_lookup).
      destruct b.

      + destruct request; zoo۰simp in Hcas; first done.
        iMod (channelsｰprepare (λ o, ws_deques_private۰owner #l i_ Blocked ws -∗ Φ o)%I with "Hchannels_sender Hchannels_receiver") as "(Hchannels_sender & Hchannels_receiver)".
        iDestruct (big_sepL_insert_acc with "Hrequests") as "(Hrequest & Hrequests)"; first done.
        iDestruct ("Hrequests" $! (RequestSome i_) with "[Hrequest Hchannels_sender HΦ]") as "Hrequests".
        { iSteps.
          rewrite /request۰au. iAuIntro.
          iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vss (:model)". injection Heq as <-.
          iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iAaccIntro with "Hmodels_auth"; first iSteps. iIntros (o) "Hmodels_auth".
          iExists o. iRevert "Hmodels_auth".
          destruct o; iSteps.
        }
        iSplitR "Hchannels_receiver". { iFrameSteps. }
        iIntros "!> _".

        wp۰apply+ (ws_deques_private٠steal_to₁ｰspec with "[$Hmeta $Hl_responses $Hresponses_inv $Hinv $Hchannels_receiver]"); [lia.. |].
        iSteps.

      + iSplitR "Hchannels_sender Hchannels_receiver HΦ". { iFrameSteps. }
        iIntros "!> _".

        iMod "HΦ" as "(%vss & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iMod ("HΦ" $! None with "[Hmodels_auth]") as "HΦ"; first iSteps.

        iSteps.
  Qed.
End ws_deques_private۰G.

#[global] Opaque ws_deques_private۰inv.
#[global] Opaque ws_deques_private۰model.
#[global] Opaque ws_deques_private۰owner.

Section ws_deques_private۰G.
  Context `{ws_deques_private۰G : WsDequesPrivateG Σ}.

  #[local] Lemma ws_deques_private٠steal_as₁ｰspec t ι (sz : nat) i i_ ws round (n : nat) :
    i = ⁺i_ →
    <<<
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) n
    | ∀∀ vss,
      ws_deques_private۰model t vss
    >>>
      ws_deques_private٠steal_as₁ t #sz #i round #n
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_private۰model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques_private۰model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques_private۰owner t i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & Hround) HΦ".
    iDestruct (ws_deques_privateｰinvｰowner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (n).

    wp۰rec. wp۰pures.
    case_bool_decide as Hcase; wp۰pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel [$Howner Hround]"); first iSteps.

    - wp۰apply (random٠round٠nextｰspec' with "Hround") as (j) "(%Hj & Hround)"; first lia.
      wp۰pures.
      rewrite Nat2Z.id.
      pose k := (i_ + 1 + j) `mod` sz.
      assert ((i_ + 1 + j) `rem` sz = k)%Z as ->.
      { rewrite Z.rem_mod_nonneg; lia. }
      awp۰apply+ (ws_deques_private٠steal_toｰspec with "[$Hinv $Howner]") without "Hround"; [done | lia |].
      iApply (aaccｰaupd with "HΦ"); first done. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([ v |]).

      + rewrite Nat2Z.id.
        iSteps as (vs Hlookup) "Hmodel". iExists (Some v). iSteps. iExists k. iSteps. iPureIntro.
        clear Hlookup. rewrite {}/k.
        destruct_decide (i_ + 1 + j < sz).
        * rewrite Nat.mod_small //. lia.
        * assert (i_ + 1 + j < sz * 2) as ?%Nat.Div0.div_lt_upper_bound by lia.
          assert ((i_ + 1 + j) `div` sz = 1) by lia.
          lia.

      + iSteps as "HΦ Howner Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        iSteps.
  Qed.
  Lemma ws_deques_private٠steal_asｰspec t ι sz i i_ ws round :
    i = ⁺i_ →
    0 < sz →
    <<<
      ws_deques_private۰inv t ι sz ∗
      ws_deques_private۰owner t i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques_private۰model t vss
    >>>
      ws_deques_private٠steal_as t #i round
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_private۰model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques_private۰model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques_private۰owner t i_ Blocked ws ∗
      random۰round۰model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Hsz %Φ (#Hinv & Hround) HΦ".

    wp۰rec.
    wp۰apply+ (ws_deques_private٠sizeｰspec with "Hinv") as "_".
    wp۰pures.
    assert (sz - 1 = (sz - 1)%nat)%Z as -> by lia.
    wp۰apply (ws_deques_private٠steal_as₁ｰspec with "[$Hinv $Hround] HΦ"); first done.
  Qed.
End ws_deques_private۰G.

Require zoo_parabs.ws_deques_private__opaque.
