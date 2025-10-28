From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  function
  list
  relations.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_mono
  lib.mono_list
  lib.saved_pred
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  identifier
  wise_prophets.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  domain
  inf_array
  int
  optional.
From zoo_saturn Require Export
  base
  inf_mpmc_queue_2__code.
From zoo_saturn Require Import
  inf_mpmc_queue_2__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types front back : nat.
Implicit Types v t : val.
Implicit Types o : option val.
Implicit Types vs : list val.
Implicit Types hist : list (option val).
Implicit Types slot : optional val.
Implicit Types slots : nat → optional val.
Implicit Types η : gname.
Implicit Types ηs : list gname.

#[local] Program Definition global_prophet := {|
  typed_prophet_type :=
    identifier ;
  typed_prophet_of_val v :=
    match v with
    | ValId id =>
        Some id
    | _ =>
        None
    end ;
  typed_prophet_to_val id :=
    #id ;
|}.
Solve Obligations of global_prophet with
  try done.
Next Obligation.
  naive_solver.
Qed.
Implicit Types past prophs : list global_prophet.(typed_prophet_type).
Implicit Types pasts prophss : nat → list global_prophet.(typed_prophet_type).

#[local] Program Definition local_prophet := {|
  typed_prophet1_type :=
    nat ;
  typed_prophet1_of_val v :=
    match v with
    | ValInt i =>
        Some (Z.to_nat i)
    | _ =>
        None
    end ;
  typed_prophet1_to_val i :=
    #i ;
|}.
Solve Obligations of local_prophet with
  try done.
Next Obligation.
  intros i v ->. rewrite /= Nat2Z.id //.
Qed.

Inductive lstate :=
  | Producer
  | ProducerProducer
  | ProducerConsumer
  | Consumer
  | ConsumerProducer η
  | ConsumerConsumer.
#[local] Canonical lstate_O {SI : sidx} :=
  leibnizO lstate.
Implicit Types lstate : lstate.
Implicit Types lstates : list lstate.

#[local] Definition lstate_winner lstate :=
  match lstate with
  | Producer =>
      Producer
  | ProducerProducer =>
      Producer
  | ProducerConsumer =>
      Consumer
  | Consumer =>
      Consumer
  | ConsumerProducer η =>
      Producer
  | ConsumerConsumer =>
      Consumer
  end.

#[local] Definition lstate_measure lstate :=
  match lstate with
  | Producer
  | Consumer =>
      0
  | ProducerProducer
  | ProducerConsumer
  | ConsumerProducer _
  | ConsumerConsumer =>
      1
  end.

Inductive lstep : lstate → lstate → Prop :=
  | lstep_producer_producer :
      lstep Producer ProducerProducer
  | lstep_producer_consumer :
      lstep Consumer ProducerConsumer
  | lstep_consumer_producer η :
      lstep Producer (ConsumerProducer η)
  | lstep_consumer_consumer :
      lstep Consumer ConsumerConsumer.

#[local] Lemma lstep_measure lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate_measure lstate1 < lstate_measure lstate2.
Proof.
  intros []; simpl; lia.
Qed.
#[local] Lemma lstep_tc_measure lstate1 lstate2 :
  tc lstep lstate1 lstate2 →
  lstate_measure lstate1 < lstate_measure lstate2.
Proof.
  intros Hlsteps.
  apply transitive_tc; first apply _.
  eapply (tc_congruence lstate_measure); last done.
  apply lstep_measure.
Qed.
#[local] Lemma lstep_rtc_measure lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate_measure lstate1 ≤ lstate_measure lstate2.
Proof.
  intros [<- | Hlsteps%lstep_tc_measure]%rtc_tc; lia.
Qed.

#[local] Instance lsteps_antisymm :
  AntiSymm (=) (rtc lstep).
Proof.
  intros lstate1 lstate2 Hlsteps1 Hlsteps2%lstep_rtc_measure.
  apply rtc_tc in Hlsteps1 as [<- | Hlsteps1%lstep_tc_measure]; first done.
  lia.
Qed.

#[local] Lemma lstate_winner_lb lstate :
  rtc lstep (lstate_winner lstate) lstate.
Proof.
  destruct lstate; eauto using rtc, lstep.
Qed.
#[local] Lemma lstep_winner lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate_winner lstate1 = lstate_winner lstate2.
Proof.
  intros Hlstep. invert Hlstep; done.
Qed.
#[local] Lemma lsteps_winner lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate_winner lstate1 = lstate_winner lstate2.
Proof.
  intros Hlsteps.
  apply preorder_rtc; [apply _.. |].
  eapply (rtc_congruence lstate_winner); last done.
  apply lstep_winner.
Qed.

Class InfMpmcQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_mpmc_queue_2_G_inf_array_G :: InfArrayG Σ ;
  #[local] inf_mpmc_queue_2_G_prophets_G :: WiseProphetsG Σ global_prophet ;
  #[local] inf_mpmc_queue_2_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] inf_mpmc_queue_2_G_history_G :: MonoListG Σ (option val) ;
  #[local] inf_mpmc_queue_2_G_lstate_G :: AuthMonoG Σ lstep ;
  #[local] inf_mpmc_queue_2_G_lstates_G :: MonoListG Σ gname ;
  #[local] inf_mpmc_queue_2_G_saved_pred_G :: SavedPredG Σ val ;
  #[local] inf_mpmc_queue_2_G_producer_G :: OneshotG Σ () () ;
  #[local] inf_mpmc_queue_2_G_producers_G :: MonoListG Σ gname ;
  #[local] inf_mpmc_queue_2_G_consumer_G :: OneshotG Σ () () ;
  #[local] inf_mpmc_queue_2_G_consumers_G :: MonoListG Σ gname ;
}.

Definition inf_mpmc_queue_2_Σ := #[
  inf_array_Σ ;
  wise_prophets_Σ global_prophet ;
  twins_Σ (leibnizO (list val)) ;
  mono_list_Σ (option val) ;
  mono_list_Σ gname ;
  auth_mono_Σ lstep ;
  saved_pred_Σ val ;
  oneshot_Σ () () ;
  mono_list_Σ gname ;
  oneshot_Σ () () ;
  mono_list_Σ gname
].
#[global] Instance subG_inf_mpmc_queue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_mpmc_queue_2_Σ Σ →
  InfMpmcQueue2G Σ.
Proof.
  solve_inG.
Qed.

Section inf_mpmc_queue_2_G.
  Context `{inf_mpmc_queue_2_G : InfMpmcQueue2G Σ}.

  Implicit Types Ψ : val → iProp Σ.

  Record metadata := {
    metadata_data : val ;
    metadata_inv : namespace ;
    metadata_prophet : prophet_id ;
    metadata_prophet_name : wise_prophets_name ;
    metadata_model : gname ;
    metadata_history : gname ;
    metadata_lstates : gname ;
    metadata_producers : gname ;
    metadata_consumers : gname ;
  }.
  Implicit Type γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition history_auth γ :=
    history_auth' γ.(metadata_history).
  #[local] Definition history_at γ i o :=
    mono_list_at γ.(metadata_history) i o.

  #[local] Definition lstates_auth' γ_lstates lstates : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_lstates (DfracOwn 1) ηs ∗
    [∗ list] η; lstate ∈ ηs; lstates,
      auth_mono_auth _ η DfracDiscarded lstate.
  #[local] Definition lstates_auth γ :=
    lstates_auth' γ.(metadata_lstates).
  #[local] Instance : CustomIpatFormat "lstates_auth" :=
    " ( %ηs &
        Hauth &
        Hηs
      )
    ".
  #[local] Definition lstates_at γ i lstate : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_lstates) i η ∗
    auth_mono_auth _ η DfracDiscarded lstate.
  #[local] Instance : CustomIpatFormat "lstates_at" :=
    " ( %η{} &
        #Hat{_{}} &
        #Hη_auth{_{}}
      )
    ".
  #[local] Definition lstates_lb γ i lstate : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_lstates) i η ∗
    auth_mono_lb _ η lstate.
  #[local] Instance : CustomIpatFormat "lstates_lb" :=
    " ( %η{} &
        #Hat{_{}} &
        #Hη_lb{_{}}
      )
    ".

  #[local] Definition producers_auth' γ_producers i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_producers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition producers_auth γ :=
    producers_auth' γ.(metadata_producers).
  #[local] Instance : CustomIpatFormat "producers_auth" :=
    " ( %ηs &
        Hauth &
        %Hηs
      )
    ".
  #[local] Definition producers_at γ i own : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_producers) i η ∗
    match own with
    | Own =>
        oneshot_pending η (DfracOwn 1) ()
    | Discard =>
        oneshot_shot η ()
    end.
  #[local] Instance : CustomIpatFormat "producers_at" :=
    " ( %η{} &
        Hat{_{}} &
        Hη{}
      )
    ".

  #[local] Definition consumers_auth' γ_consumers i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_consumers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition consumers_auth γ :=
    consumers_auth' γ.(metadata_consumers).
  #[local] Instance : CustomIpatFormat "consumers_auth" :=
    " ( %ηs{} &
        Hauth{} &
        %Hηs{}
      )
    ".
  #[local] Definition consumers_at γ i own : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_consumers) i η ∗
    match own with
    | Own =>
        oneshot_pending η (DfracOwn 1) ()
    | Discard =>
        oneshot_shot η ()
    end.
  #[local] Instance : CustomIpatFormat "consumers_at" :=
    " ( %η{} &
        Hat{_{}} &
        Hη{}
      )
    ".
  #[local] Definition consumers_lb γ i : iProp Σ :=
    ∃ ηs,
    mono_list_lb γ.(metadata_consumers) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Instance : CustomIpatFormat "consumers_lb" :=
    " ( %ηs{} &
        Hlb{} &
        %Hηs{}
      )
    ".

  #[local] Definition winner γ i : iProp Σ :=
    ∃ id prophs,
    wise_prophets_full global_prophet γ.(metadata_prophet_name) i prophs ∗
    ⌜head prophs = Some id⌝ ∗
    identifier_model' id.
  #[local] Instance : CustomIpatFormat "winner" :=
    " ( %id{} &
        %prophs{} &
        Hprophet_full{_{}} &
        %Hprophs{} &
        Hid{}
      )
    ".

  #[local] Definition consumer_au γ Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      ∀∀ v vs',
      ⌜vs = v :: vs'⌝ ∗
      model₁ γ vs'
    , COMM
      Ψ v
    }>.

  #[local] Definition inv_lstate_left γ back i lstate : iProp Σ :=
    match lstate with
    | ProducerProducer =>
        ∃ v,
        history_at γ i (Some v) ∗
        winner γ i
    | ProducerConsumer =>
        history_at γ i None
    | ConsumerProducer η =>
        ∃ Ψ v,
        consumers_lb γ (S i) ∗
        saved_pred η Ψ ∗
        history_at γ i (Some v) ∗
        ( Ψ v
        ∨ consumers_at γ i Discard
        )
    | ConsumerConsumer =>
        consumers_lb γ (S i)
    | _ =>
        False
    end.
  #[local] Instance : CustomIpatFormat "inv_lstate_left_producer" :=
    " ( %v &
        #Hhistory_at &
        Hwinner
      )
    ".
  #[local] Instance : CustomIpatFormat "inv_lstate_left_consumer" :=
    " ( %Ψ &
        %v_ &
        #Hconsumers_lb &
        #Hη_ &
        #Hhistory_at_ &
        HΨ
      )
    ".

  #[local] Definition inv_lstate_right γ i lstate : iProp Σ :=
    match lstate with
    | ConsumerProducer η =>
        ∃ Ψ,
        saved_pred η Ψ ∗
        consumer_au γ Ψ
    | ConsumerConsumer =>
        winner γ i
    | _ =>
        False
    end.
  #[local] Instance : CustomIpatFormat "inv_lstate_right" :=
    " ( %Ψ &
        #Hη &
        Hconsumer_au
      )
    ".

  #[local] Definition inv_slot γ i slot past : iProp Σ :=
    match slot with
    | Nothing =>
        ⌜past = []⌝
    | Something v =>
        history_at γ i (Some v) ∗
        producers_at γ i Discard ∗
        lstates_lb γ i Producer
    | Anything =>
        consumers_at γ i Discard ∗
        ( lstates_lb γ i Consumer
        ∨ producers_at γ i Discard
        )
    end.
  #[local] Instance : CustomIpatFormat "inv_slot_nothing" :=
    "%Hpast".
  #[local] Instance : CustomIpatFormat "inv_slot_something" :=
    " ( #Hhistory_at{_{suff}} &
        #Hproducers_at{_{suff}} &
        #Hlstates_lb_producer
      )
    ".
  #[local] Instance : CustomIpatFormat "inv_slot_anything" :=
    " ( #Hconsumers_at{_{suff}} &
        { _{suff}
        ; [ #Hlstates_lb_consumer
          | #Hproducers_at_
          ]
        }
      )
    ".

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ front back hist slots vs lstates pasts prophss,
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    inf_array_model γ.(metadata_data) slots ∗
    model₂ γ vs ∗
    ⌜vs = oflatten (drop front hist)⌝ ∗
    history_auth γ hist ∗
    ⌜length hist = back⌝ ∗
    lstates_auth γ lstates ∗
    ⌜length lstates = front `max` back⌝ ∗
    wise_prophets_model global_prophet γ.(metadata_prophet) γ.(metadata_prophet_name) pasts prophss ∗
    producers_auth γ back ∗
    consumers_auth γ front ∗
    ( [∗ list] i ↦ lstate ∈ take back lstates,
      inv_lstate_left γ back i lstate
    ) ∗
    ( [∗ list] k ↦ lstate ∈ drop back lstates,
      inv_lstate_right γ (back + k) lstate
    ) ∗
    ( ∀ i,
      inv_slot γ i (slots i) (pasts i)
    ).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    " ( %front{} &
        %back{} &
        %hist{} &
        %slots{} &
        %vs{} &
        %lstates{} &
        %pasts{} &
        %prophss{} &
        Hl_front &
        Hl_back &
        >Hdata_model &
        Hmodel₂ &
        >%Hvs{} &
        Hhistory_auth &
        >%Hhist{} &
        Hlstates_auth &
        >%Hlstates{} &
        >Hprophet_model &
        Hproducers_auth &
        Hconsumers_auth &
        Hlstates_left &
        Hlstates_right &
        Hslots
      )
    ".
  Definition inf_mpmc_queue_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    l.[proph] ↦□ #γ.(metadata_prophet) ∗
    inf_array_inv γ.(metadata_data) ∗
    inv γ.(metadata_inv) (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %l &
        %γ &
        -> &
        -> &
        #Hmeta &
        #Hl_data &
        #Hl_proph &
        #Hdata_inv &
        #Hinv
      )
    ".

  Definition inf_mpmc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    " ( %l{;_} &
        %γ{;_} &
        %Heq{} &
        Hmeta_{} &
        Hmodel₁{_{}}
      )
    ".

  #[global] Instance inf_mpmc_queue_2_model_timeless t vs :
    Timeless (inf_mpmc_queue_2_model t vs).
  Proof.
    apply _.
  Qed.

  #[local] Instance lstates_at_persistent γ i lstate :
    Persistent (lstates_at γ i lstate).
  Proof.
    apply _.
  Qed.
  #[local] Instance lstates_lb_persistent γ i lstate :
    Persistent (lstates_lb γ i lstate).
  Proof.
    apply _.
  Qed.
  #[local] Instance producers_at_persistent γ i :
    Persistent (producers_at γ i Discard).
  Proof.
    apply _.
  Qed.
  #[local] Instance consumers_at_persistent γ i :
    Persistent (consumers_at γ i Discard).
  Proof.
    apply _.
  Qed.
  #[local] Instance consumers_lb_persistent γ i :
    Persistent (consumers_lb γ i).
  Proof.
    apply _.
  Qed.
  #[local] Instance inv_slot_persistent γ i slot past :
    Persistent (inv_slot γ i slot past).
  Proof.
    destruct slot; apply _.
  Qed.
  #[global] Instance inf_mpmc_queue_2_inv_persistent t ι :
    Persistent (inf_mpmc_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma model_update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins_update.
  Qed.

  #[local] Lemma history_alloc :
    ⊢ |==>
      ∃ γ_history,
      history_auth' γ_history [].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma history_at_lookup γ hist i o :
    history_auth γ hist -∗
    history_at γ i o -∗
    ⌜hist !! i = Some o⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  #[local] Lemma history_at_agree γ i o1 o2 :
    history_at γ i o1 -∗
    history_at γ i o2 -∗
    ⌜o1 = o2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (mono_list_at_agree with "Hat1 Hat2") as %[= <-]. done.
  Qed.
  #[local] Lemma history_at_get {γ hist} i o :
    hist !! i = Some o →
    history_auth γ hist ⊢
    history_at γ i o.
  Proof.
    apply mono_list_at_get.
  Qed.
  #[local] Lemma history_update {γ hist} o :
    history_auth γ hist ⊢ |==>
      history_auth γ (hist ++ [o]) ∗
      history_at γ (length hist) o.
  Proof.
    iIntros "Hhistory_auth".
    iMod (mono_list_update_snoc o with "Hhistory_auth") as "Hhistory_auth".
    iDestruct (mono_list_at_get with "Hhistory_auth") as "#Hhistory_at".
    { rewrite list_lookup_middle //. }
    iSteps.
  Qed.

  #[local] Lemma lstates_alloc :
    ⊢ |==>
      ∃ γ_lstates,
      lstates_auth' γ_lstates [].
  Proof.
    iMod (mono_list_alloc []) as "(%γ_lstates & $)".
    iSteps.
  Qed.
  #[local] Lemma lstates_at_lookup γ lstates i lstate :
    lstates_auth γ lstates -∗
    lstates_at γ i lstate -∗
    ⌜lstates !! i = Some lstate⌝.
  Proof.
    iIntros "(:lstates_auth) (:lstates_at)".
    iDestruct (mono_list_at_valid with "Hauth Hat") as %Hηs_lookup.
    iDestruct (big_sepL2_lookup_l with "Hηs") as "(%lstate_ & %Hlstates_lookup & Hη_auth_)"; first done.
    iDestruct (auth_mono_auth_agree_L with "Hη_auth Hη_auth_") as %<-.
    iSteps.
  Qed.
  #[local] Lemma lstates_lb_get {γ lstates} i lstate :
    lstates !! i = Some lstate →
    lstates_auth γ lstates -∗
    lstates_lb γ i (lstate_winner lstate).
  Proof.
    iIntros "%Hlstates_lookup (:lstates_auth)".
    iDestruct (big_sepL2_lookup_r with "Hηs") as "(%η & %Hηs_lookup & Hη_auth)"; first done.
    iDestruct (auth_mono_lb_get with "Hη_auth") as "Hη_lb".
    iDestruct (auth_mono_lb_mono with "Hη_lb") as "Hη_lb".
    { apply lstate_winner_lb. }
    iDestruct (mono_list_at_get with "Hauth") as "#Hat"; first done.
    iSteps.
  Qed.
  #[local] Lemma lstates_lb_agree γ i lstate1 lstate2 :
    lstates_lb γ i lstate1 -∗
    lstates_lb γ i lstate2 -∗
    ⌜lstate_winner lstate1 = lstate_winner lstate2⌝.
  Proof.
    iIntros "(:lstates_lb =1) (:lstates_lb =2)".
    iDestruct (mono_list_at_agree with "Hat_1 Hat_2") as %<-.
    iDestruct (auth_mono_lb_agree with "Hη_lb_1 Hη_lb_2") as %(lstate & ->%lsteps_winner & ->%lsteps_winner).
    iSteps.
  Qed.
  #[local] Lemma lstates_update {γ lstates} lstate :
    lstates_auth γ lstates ⊢ |==>
      lstates_auth γ (lstates ++ [lstate]) ∗
      lstates_lb γ (length lstates) (lstate_winner lstate) ∗
      lstates_at γ (length lstates) lstate.
  Proof.
    iIntros "(:lstates_auth)".
    iMod (auth_mono_alloc _ lstate) as "(%η & Hη_auth)".
    iMod (auth_mono_auth_persist with "Hη_auth") as "#Hη_auth".
    iMod (mono_list_update_snoc η with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iDestruct (auth_mono_lb_get with "Hη_auth") as "#Hη_lb".
    iDestruct (auth_mono_lb_mono _ (lstate_winner lstate) with "Hη_lb") as "#Hη_lb_winner".
    { destruct lstate; eauto using rtc, lstep. }
    iDestruct (big_sepL2_length with "Hηs") as %->.
    iDestruct (big_sepL2_snoc_2 with "Hηs Hη_auth") as "Hηs".
    iSteps.
  Qed.

  #[local] Lemma producers_alloc :
    ⊢ |==>
      ∃ γ_producers,
      producers_auth' γ_producers 0.
  Proof.
    iMod (mono_list_alloc []) as "(%γ_producers & $)".
    iSteps.
  Qed.
  #[local] Lemma producers_at_exclusive γ i own :
    producers_at γ i Own -∗
    producers_at γ i own -∗
    False.
  Proof.
    iIntros "(:producers_at =1) (:producers_at =2)".
    iDestruct (mono_list_at_agree with "Hat_1 Hat_2") as %<-.
    destruct own.
    - iApply (oneshot_pending_exclusive with "Hη1 Hη2").
    - iApply (oneshot_pending_shot with "Hη1 Hη2").
  Qed.
  #[local] Lemma producers_at_discard γ i :
    producers_at γ i Own ⊢ |==>
    producers_at γ i Discard.
  Proof.
    iIntros "(:producers_at)".
    iMod (oneshot_update_shot with "Hη") as "Hη".
    iSteps.
  Qed.
  #[local] Lemma producers_update γ i :
    producers_auth γ i ⊢ |==>
      producers_auth γ (S i) ∗
      producers_at γ i Own.
  Proof.
    iIntros "(:producers_auth)".
    iMod oneshot_alloc as "(%η & Hη_pending)".
    iMod (mono_list_update_snoc η with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. simpl_length/=. iSteps.
  Qed.

  #[local] Lemma consumers_alloc :
    ⊢ |==>
      ∃ γ_consumers,
      consumers_auth' γ_consumers 0.
  Proof.
    iMod (mono_list_alloc []) as "(%γ_consumers & $)".
    iSteps.
  Qed.
  #[local] Lemma consumers_at_exclusive γ i own :
    consumers_at γ i Own -∗
    consumers_at γ i own -∗
    False.
  Proof.
    iIntros "(:consumers_at =1) (:consumers_at =2)".
    iDestruct (mono_list_at_agree with "Hat_1 Hat_2") as %<-.
    destruct own.
    - iApply (oneshot_pending_exclusive with "Hη1 Hη2").
    - iApply (oneshot_pending_shot with "Hη1 Hη2").
  Qed.
  #[local] Lemma consumers_at_discard γ i :
    consumers_at γ i Own ⊢ |==>
    consumers_at γ i Discard.
  Proof.
    iIntros "(:consumers_at)".
    iMod (oneshot_update_shot with "Hη") as "Hη".
    iSteps.
  Qed.
  #[local] Lemma consumers_lb_valid γ i j :
    consumers_auth γ i -∗
    consumers_lb γ j -∗
    ⌜j ≤ i⌝.
  Proof.
    iIntros "(:consumers_auth =1) (:consumers_lb =2)".
    iDestruct (mono_list_lb_valid with "Hauth1 Hlb2") as %?%prefix_length.
    iSteps.
  Qed.
  #[local] Lemma consumers_lb_le {γ i1} i2 :
    i2 ≤ i1 →
    consumers_lb γ i1 ⊢
    consumers_lb γ i2.
  Proof.
    iIntros "% (:consumers_lb)".
    iDestruct (mono_list_lb_mono (take i2 ηs) with "Hlb") as "$".
    { apply prefix_take. }
    simpl_length. iSteps.
  Qed.
  #[local] Lemma consumers_lb_get γ i :
    consumers_auth γ i ⊢
    consumers_lb γ i.
  Proof.
    iIntros "(:consumers_auth)".
    iDestruct (mono_list_lb_get with "Hauth") as "Hlb".
    iSteps.
  Qed.
  #[local] Lemma consumers_lb_get' {γ i} i' :
    i' ≤ i →
    consumers_auth γ i ⊢
    consumers_lb γ i'.
  Proof.
    iIntros "% Hauth".
    iDestruct (consumers_lb_get with "Hauth") as "Hlb".
    iDestruct (consumers_lb_le with "Hlb") as "Hlb"; first done.
    iSteps.
  Qed.
  #[local] Lemma consumers_update γ i :
    consumers_auth γ i ⊢ |==>
      consumers_auth γ (S i) ∗
      consumers_at γ i Own.
  Proof.
    iIntros "(:consumers_auth)".
    iMod oneshot_alloc as "(%η & Hη_pending)".
    iMod (mono_list_update_snoc η with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. simpl_length/=. iSteps.
  Qed.

  Opaque lstates_auth'.
  Opaque lstates_at.
  Opaque lstates_lb.
  Opaque producers_auth'.
  Opaque producers_at.
  Opaque consumers_auth'.
  Opaque consumers_at.
  Opaque consumers_lb.

  #[local] Lemma winner_exclusive γ i :
    winner γ i -∗
    winner γ i -∗
    False.
  Proof.
    iIntros "(:winner =1) (:winner =2)".
    iDestruct (wise_prophets_full_agree with "Hprophet_full_1 Hprophet_full_2") as %->. simplify.
    iApply (identifier_model_exclusive with "Hid1 Hid2").
  Qed.

  #[local] Lemma inv_slot_not_nothing_past {γ i slot past1} past2 :
    slot ≠ Nothing →
    inv_slot γ i slot past1 ⊣⊢
    inv_slot γ i slot past2.
  Proof.
    destruct slot; iSteps.
  Qed.

  Lemma inf_mpmc_queue_2_model_exclusive t vs1 vs2 :
    inf_mpmc_queue_2_model t vs1 -∗
    inf_mpmc_queue_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma inf_mpmc_queue_2_create_spec ι :
    {{{
      True
    }}}
      inf_mpmc_queue_2_create ()
    {{{ t,
      RET t;
      inf_mpmc_queue_2_inv t ι ∗
      inf_mpmc_queue_2_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply (wise_prophets_wp_proph global_prophet with "[//]") as "%pid %γ_prophet %prophss Hprophet_model".
    wp_apply (inf_array_create_spec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
    wp_block l as "Hmeta" "(Hl_data & Hl_front & Hl_back & Hl_proph & _)".
    iMod (pointsto_persist with "Hl_data") as "#Hl_data".
    iMod (pointsto_persist with "Hl_proph") as "#Hl_proph".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod lstates_alloc as "(%γ_lstates & Hlstates_auth)".
    iMod producers_alloc as "(%γ_producers & Hproducers_auth)".
    iMod consumers_alloc as "(%γ_consumers & Hconsumers_auth)".

    pose γ := {|
      metadata_data := data ;
      metadata_inv := ι ;
      metadata_prophet := pid ;
      metadata_prophet_name := γ_prophet ;
      metadata_model := γ_model ;
      metadata_history := γ_history ;
      metadata_lstates := γ_lstates ;
      metadata_producers := γ_producers ;
      metadata_consumers := γ_consumers ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iSteps. iExists (λ _, Nothing). iSteps. iExists []. iSteps.
  Qed.

  Lemma inf_mpmc_queue_2_size_spec t ι :
    <<<
      inf_mpmc_queue_2_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2_model t vs
    >>>
      inf_mpmc_queue_2_size t @ ↑ι
    <<<
      inf_mpmc_queue_2_model t vs
    | sz,
      RET #sz;
      ⌜length vs ≤ sz⌝
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (consumers_lb_get with "Hconsumers_auth") as "#Hconsumers_lb1".
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    wp_smart_apply (typed_prophet1_wp_proph local_prophet with "[//]") as (pid proph) "Hproph".
    wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct_decide (proph = front1) as -> | Hproph.

    - destruct_decide (front2 = front1) as -> | ?.

      + iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

        iSplitR "Hproph HΦ". { iFrameSteps. }
        iModIntro. clear- Hvs2 Hhist2.

        wp_pures.

        wp_bind (_.{front})%E.
        iInv "Hinv" as "(:inv_inner =3)".
        wp_load.
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iModIntro. clear -Hvs2 Hhist2.

        wp_smart_apply (typed_prophet1_wp_resolve with "Hproph"); [done.. |].
        iSteps.
        wp_apply int_positive_part_spec.
        iSteps. iPureIntro.
        rewrite Hvs2. simpl_length. lia.

      + iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb1") as %?.
        iDestruct (consumers_lb_get with "Hconsumers_auth") as "#Hconsumers_lb2".
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iModIntro.

        wp_pures.

        wp_bind (_.{front})%E.
        iInv "Hinv" as "(:inv_inner =3)".
        wp_load.
        iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb2") as %?.
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iModIntro.

        wp_smart_apply (typed_prophet1_wp_resolve with "Hproph"); [done.. |].
        iSteps.

    - iSplitR "Hproph HΦ". { iFrameSteps. }
      iModIntro. clear- Hproph.

      wp_pures.

      wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner =3)".
      wp_load.
      iSplitR "Hproph HΦ". { iFrameSteps. }
      iModIntro. clear- Hproph.

      wp_smart_apply (typed_prophet1_wp_resolve with "Hproph"); [done.. |].
      iSteps.
  Qed.

  Lemma inf_mpmc_queue_2_is_empty_spec t ι :
    <<<
      inf_mpmc_queue_2_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2_model t vs
    >>>
      inf_mpmc_queue_2_is_empty t @ ↑ι
    <<<
      inf_mpmc_queue_2_model t vs
    | b,
      RET #b;
      ⌜if b then vs = [] else True⌝
    >>>.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.

    awp_apply (inf_mpmc_queue_2_size_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; iSteps. iPureIntro.
    case_bool_decide as Hlength; last done.
    apply nil_length_inv. lia.
  Qed.

  Lemma inf_mpmc_queue_2_push_spec t ι v :
    <<<
      inf_mpmc_queue_2_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2_model t vs
    >>>
      inf_mpmc_queue_2_push t v @ ↑ι
    <<<
      inf_mpmc_queue_2_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (wp_id with "[//]") as (id) "Hid".
    wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(:inv_inner =1)".
    wp_faa.
    iMod (producers_update with "Hproducers_auth") as "(Hproducers_auth & Hproducers_at)".
    iDestruct (wise_prophets_full_get' _ back1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
    destruct_decide (front1 ≤ back1) as Hfirst | Hlast.

    - rewrite Nat.max_r // in Hlstates1.
      rewrite firstn_all2; first lia.

      destruct_decide (head prophs = Some id) as Hwinner | Hloser.

      + iMod (history_update (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
        iMod (lstates_update ProducerProducer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1.
        iDestruct (big_sepL_snoc_2 ProducerProducer with "Hlstates_left [Hid]") as "Hlstates_left".
        { rewrite Hlstates1. iSteps. }

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
        iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iFrameSteps.

        iSplitR "Hproducers_at HΦ".
        { iFrame.
          rewrite firstn_all2. { simpl_length/=. lia. }
          rewrite (skipn_all2 (n := S back1)).
          { simpl_length/=. lia. }
          iFrameSteps; iPureIntro.
          - rewrite drop_app_le; first lia.
            rewrite oflatten_snoc_Some Hvs1 //.
          - simpl_length/=. lia.
          - simpl_length/=. lia.
        }
        iModIntro. clear- Hwinner.

        do 2 wp_load.

        wp_apply (inf_array_cas_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
        rewrite Nat2Z.id in Hslots2 |- *.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        destruct b; last first.
        { iDestruct ("Hslots" $! back1) as "Hslot".
          destruct (slots2 back1).
          - exfalso. done.
          - iDestruct "Hslot" as "(:inv_slot_anything)".
            + iDestruct (lstates_lb_agree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
            + iDestruct (producers_at_exclusive with "Hproducers_at Hproducers_at_") as %[].
          - iDestruct "Hslot" as "(:inv_slot_something suff=)".
            iDestruct (producers_at_exclusive with "Hproducers_at Hproducers_at_") as %[].
        }
        iMod (producers_at_discard with "Hproducers_at") as "#Hproducers_at".
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { rewrite -(fn_compose_insert _ _ _ (Something v)).
          iFrameSteps.
          rewrite function.fn_lookup_insert. case_decide.
          - subst. iSteps.
          - rewrite fn_lookup_alter_ne //.
        }
        iSteps.

      + iMod (history_update None with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
        iMod (lstates_update ProducerConsumer with "Hlstates_auth") as "(Hlstates_auth & Hlstates_lb & _)".
        iDestruct (big_sepL_snoc_2 ProducerConsumer with "Hlstates_left []") as "Hlstates_left".
        { rewrite Hlstates1 //. }
        iSplitR "HΦ".
        { iFrame.
          rewrite firstn_all2. { simpl_length/=. lia. }
          rewrite (skipn_all2 (n := S back1)).
          { simpl_length/=. lia. }
          iFrameSteps; iPureIntro.
          - rewrite drop_app_le; first lia.
            rewrite oflatten_snoc_None Hvs1 //.
          - simpl_length/=. lia.
          - simpl_length/=. lia.
        }
        iModIntro. clear- Hloser.

        do 2 wp_load.

        wp_apply (inf_array_cas_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
        rewrite Nat2Z.id in Hslots2 |- *.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        destruct b.
        { iDestruct ("Hslots" $! back1) as "Hslot".
          destruct (slots2 back1).
          - iDestruct "Hslot" as "(:inv_slot_nothing)".
            iDestruct (wise_prophets_full_valid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          - exfalso. done.
          - exfalso. done.
        }
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { iFrameSteps.
          rewrite function.fn_lookup_alter. case_decide; last done.
          subst. rewrite inv_slot_not_nothing_past //.
          intros Heq. rewrite Heq // in Hslots2.
        }
        iSteps.

    - rewrite drop_ge /= in Hvs1; first lia. subst vs1.
      rewrite Nat.max_l in Hlstates1; first lia.
      iDestruct (consumers_lb_get' (S back1) with "Hconsumers_auth") as "#Hconsumers_lb"; first lia.
      destruct (lookup_lt_is_Some_2 lstates1 back1) as (lstate & Hlstates_lookup); first lia.
      iDestruct (lstates_lb_get with "Hlstates_auth") as "#Hlstates_lb"; first done.
      erewrite drop_S; last done.
      iDestruct "Hlstates_right" as "(Hlstate & Hlstates_right)".

      destruct lstate as [| | | | η |].
      all: try iDestruct "Hlstate" as %[].

      + iDestruct "Hlstate" as "(:inv_lstate_right)".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update [v] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iFrameSteps.

        iMod "Hconsumer_au" as "(%vs & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΨ" with "[$Hmodel₁ //]") as "HΨ".

        iMod (history_update (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_lb)". rewrite Hhist1.
        iDestruct (big_sepL_snoc_2 (ConsumerProducer η) with "Hlstates_left [HΨ]") as "Hlstates_left".
        { rewrite /= length_take Nat.min_l; first lia. iSteps. }
        iSplitR "Hproducers_at HΦ".
        { rewrite -take_S_r //.
          setoid_rewrite Nat.add_succ_r.
          iFrameSteps; iPureIntro.
          - rewrite drop_ge //. { simpl_length/=. lia. }
          - simpl_length/=. lia.
        }
        iIntros "!> {%}".

        do 2 wp_load.

        wp_apply (inf_array_cas_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
        rewrite Nat2Z.id in Hslots2 |- *.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        destruct b; last first.
        { iDestruct ("Hslots" $! back1) as "Hslot".
          destruct (slots2 back1).
          - iDestruct "Hslot" as "(:inv_slot_nothing)".
            iDestruct (wise_prophets_full_valid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          - iDestruct "Hslot" as "(:inv_slot_anything)".
            + iDestruct (lstates_lb_agree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
            + iDestruct (producers_at_exclusive with "Hproducers_at Hproducers_at_") as %[].
          - iDestruct "Hslot" as "(:inv_slot_something suff=)".
            iDestruct (producers_at_exclusive with "Hproducers_at Hproducers_at_") as %[].
        }
        iMod (producers_at_discard with "Hproducers_at") as "#Hproducers_at".
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { rewrite -(fn_compose_insert _ _ _ (Something v)).
          iFrameSteps.
          rewrite function.fn_lookup_insert. case_decide.
          - subst. iSteps.
          - rewrite fn_lookup_alter_ne //.
        }
        iSteps.

      + iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
        { iIntros (Hwinner).
          iEval (rewrite /= Nat.add_0_r) in "Hlstate".
          iDestruct (winner_exclusive with "Hlstate [Hid]") as %[]; first iSteps.
        }

        iMod (history_update None with "Hhistory_auth") as "(Hhistory_auth & _)".
        iDestruct (big_sepL_snoc_2 ConsumerConsumer with "Hlstates_left []") as "Hlstates_left".
        { rewrite /= length_take Nat.min_l; first lia. iSteps. }
        iSplitR "HΦ".
        { rewrite -take_S_r //.
          setoid_rewrite Nat.add_succ_r.
          iFrameSteps; iPureIntro.
          - rewrite drop_ge //. { simpl_length/=. lia. }
          - simpl_length/=. lia.
        }
        iModIntro. clear- Hloser.

        do 2 wp_load.

        wp_apply (inf_array_cas_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
        rewrite Nat2Z.id in Hslots2 |- *.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        destruct b.
        { iDestruct ("Hslots" $! back1) as "Hslot".
          destruct (slots2 back1).
          - iDestruct "Hslot" as "(:inv_slot_nothing)".
            iDestruct (wise_prophets_full_valid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          - exfalso. done.
          - exfalso. done.
        }
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { iFrameSteps.
          rewrite function.fn_lookup_alter. case_decide; last done.
          subst. rewrite inv_slot_not_nothing_past //.
          intros Heq. rewrite Heq // in Hslots2.
        }
        iSteps.
  Qed.

  Lemma inf_mpmc_queue_2_pop_spec t ι :
    <<<
      inf_mpmc_queue_2_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2_model t vs
    >>>
      inf_mpmc_queue_2_pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = v :: vs'⌝ ∗
      inf_mpmc_queue_2_model t vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (wp_id with "[//]") as (id) "Hid".
    wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(:inv_inner =1)".
    wp_faa.
    iDestruct (wise_prophets_full_get' _ front1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
    destruct_decide (back1 ≤ front1) as Hfirst | Hlast.

    - rewrite drop_ge /= in Hvs1; first lia. subst vs1.
      rewrite Nat.max_l // in Hlstates1.

      iMod (consumers_update with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

      destruct_decide (head prophs = Some id) as Hwinner | Hloser.

      + iMod (lstates_update ConsumerConsumer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1.
        iDestruct (big_sepL_snoc_2 ConsumerConsumer with "Hlstates_right [Hid]") as "Hlstates_right".
        { rewrite length_drop Hlstates1 -Nat.le_add_sub; first lia.
          iSteps.
        }

        iSplitR "Hconsumers_at HΦ".
        { iFrame.
          rewrite (drop_ge hist1); first lia.
          rewrite take_app_le; first lia.
          rewrite drop_app_le; first lia.
          iFrameSteps. iPureIntro.
          simpl_length/=. lia.
        }
        iModIntro. clear- Hwinner.

        do 2 wp_load.

        wp_apply (inf_array_xchg_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e % % Hdata_model".
        rewrite Nat2Z.id.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
        destruct (slots2 front1); first last.
        { iDestruct "Hslot" as "(:inv_slot_something)".
          iDestruct (lstates_lb_agree with "Hlstates_lb Hlstates_lb_producer") as %[=].
        } {
          iDestruct "Hslot" as "(:inv_slot_anything suff=)".
          iDestruct (consumers_at_exclusive with "Hconsumers_at Hconsumers_at_") as %[].
        }
        iMod (consumers_at_discard with "Hconsumers_at") as "#Hconsumers_at".
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { rewrite -(fn_compose_insert _ _ _ Anything).
          iFrameSteps.
          rewrite function.fn_lookup_insert. case_decide.
          - subst. iSteps.
          - rewrite fn_lookup_alter_ne //.
        }
        iSteps.

      + iMod (saved_pred_alloc Φ) as "(%η & #Hη)".
        iMod (lstates_update (ConsumerProducer η) with "Hlstates_auth") as "(Hlstates_auth & _ & #Hlstates_at)". rewrite Hlstates1.
        iDestruct (big_sepL_snoc_2 (ConsumerProducer η) with "Hlstates_right [HΦ]") as "Hlstates_right".
        { iSteps.
          rewrite /consumer_au. iAuIntro.
          iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iAaccIntro with "Hmodel₁"; iSteps.
        }

        iSplitR "Hconsumers_at".
        { iFrame.
          rewrite (drop_ge hist1); first lia.
          rewrite take_app_le; first lia.
          rewrite drop_app_le; first lia.
          iFrameSteps. iPureIntro.
          simpl_length/=. lia.
        }
        iModIntro. clear- Hloser.

        do 2 wp_load.

        wp_apply (inf_array_xchg_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e % % Hdata_model".
        rewrite Nat2Z.id.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
        destruct (slots2 front1) as [| | v].
        { iDestruct "Hslot" as "(:inv_slot_nothing)".
          iDestruct (wise_prophets_full_valid with "Hprophet_model Hprophet_full") as %Hprophs.
          exfalso.
          rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
        } {
          iDestruct "Hslot" as "(:inv_slot_anything suff=)".
          iDestruct (consumers_at_exclusive with "Hconsumers_at Hconsumers_at_") as %[].
        }
        iDestruct "Hslot" as "(:inv_slot_something)".

        iDestruct (lstates_at_lookup with "Hlstates_auth Hlstates_at") as %Hlstates2_lookup.
        iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at") as %?%lookup_lt_Some.
        iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
        { rewrite lookup_take_Some. naive_solver. }
        iDestruct "Hlstate" as "(:inv_lstate_left_consumer suff=)".
        iDestruct (history_at_agree with "Hhistory_at Hhistory_at_") as %[= <-].
        iDestruct (saved_pred_agree v with "Hη Hη_") as "#Heq".
        iDestruct "HΨ" as "[HΦ | Hconsumers_at_]"; last first.
        { iDestruct (consumers_at_exclusive with "Hconsumers_at Hconsumers_at_") as %[]. }

        iMod (consumers_at_discard with "Hconsumers_at") as "#Hconsumers_at".
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { rewrite -(fn_compose_insert _ _ _ Anything).
          iFrameSteps.
          rewrite function.fn_lookup_insert. case_decide.
          - subst. iSteps.
          - rewrite fn_lookup_alter_ne //.
        }
        iIntros "!> {%}".

        wp_pures.
        iRewrite "Heq". iSteps.

    - rewrite Nat.max_r in Hlstates1; first lia.
      destruct (lookup_lt_is_Some_2 lstates1 front1) as (lstate & Hlstates_lookup); first lia.
      iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
      { rewrite lookup_take_Some. naive_solver lia. }
      destruct lstate.
      all: try iDestruct "Hlstate" as %[].
      1,2: iMod (consumers_update with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

      + iDestruct "Hlstate" as "(:inv_lstate_left_producer)".
        iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at") as %Hhist1_lookup.
        erewrite drop_S, oflatten_cons_Some in Hvs1; last done.

        iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
        { iIntros (Hwinner).
          iDestruct (winner_exclusive with "Hwinner [Hid]") as %[]; first iSteps.
        }

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
        iMod (model_update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.

        iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
        iModIntro. clear- Hloser.

        do 2 wp_load.

        wp_apply (inf_array_xchg_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e % % Hdata_model".
        rewrite Nat2Z.id.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
        destruct (slots2 front1) as [| | v_].
        { iDestruct "Hslot" as "(:inv_slot_nothing)".
          iDestruct (wise_prophets_full_valid with "Hprophet_model Hprophet_full") as %Hprophs.
          exfalso.
          rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
        } {
          iDestruct "Hslot" as "(:inv_slot_anything suff=)".
          iDestruct (consumers_at_exclusive with "Hconsumers_at Hconsumers_at_") as %[].
        }
        iDestruct "Hslot" as "(:inv_slot_something suff=)".
        iDestruct (history_at_agree with "Hhistory_at Hhistory_at_") as %[= <-].
        iMod (consumers_at_discard with "Hconsumers_at") as "#Hconsumers_at".
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { rewrite -(fn_compose_insert _ _ _ Anything).
          iFrameSteps.
          rewrite function.fn_lookup_insert. case_decide.
          - subst. iSteps.
          - rewrite fn_lookup_alter_ne //.
        }
        iSteps.

      + iDestruct (history_at_lookup with "Hhistory_auth Hlstate") as %Hhist1_lookup.
        erewrite drop_S, oflatten_cons_None in Hvs1; last done.
        iDestruct (lstates_lb_get with "Hlstates_auth") as "#Hlstates_lb"; first done.

        iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        do 2 wp_load.

        wp_apply (inf_array_xchg_resolve_spec with "Hdata_inv"); first lia.
        iMod (inv_acc with "Hinv") as "((:inv_inner =2) & Hclose1)"; first done.
        iStep. iIntros "%e % % Hdata_model".
        rewrite Nat2Z.id.
        wp_apply (wise_prophets_wp_resolve' with "Hprophet_model"); [done.. |].
        wp_pures.
        iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
        iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
        destruct (slots2 front1) as [| | v]; first last.
        { iDestruct "Hslot" as "(:inv_slot_something)".
          iDestruct (lstates_lb_agree with "Hlstates_lb Hlstates_lb_producer") as %[=].
        } {
          iDestruct "Hslot" as "(:inv_slot_anything suff=)".
          iDestruct (consumers_at_exclusive with "Hconsumers_at Hconsumers_at_") as %[].
        }
        iMod (consumers_at_discard with "Hconsumers_at") as "#Hconsumers_at".
        iMod ("Hclose1" with "[- HΦ]") as "_".
        { rewrite -(fn_compose_insert _ _ _ Anything).
          iFrameSteps.
          rewrite function.fn_lookup_insert. case_decide.
          - subst. iSteps.
          - rewrite fn_lookup_alter_ne //.
        }
        iSteps.

      + iDestruct "Hlstate" as "(:inv_lstate_left_consumer)".
        iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb") as %?. lia.

      + iDestruct (consumers_lb_valid with "Hconsumers_auth Hlstate") as %?. lia.
  Qed.
End inf_mpmc_queue_2_G.

From zoo_saturn Require
  inf_mpmc_queue_2__opaque.

#[global] Opaque inf_mpmc_queue_2_inv.
#[global] Opaque inf_mpmc_queue_2_model.
