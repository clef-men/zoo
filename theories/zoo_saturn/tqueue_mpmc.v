Require Import Stdlib.micromega.ZifyNat.

Require Import zoo.prelude.
Require Import zoo.common.function.
Require Import zoo.common.list.
Require Import zoo.common.relations.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_identifier.
Require Import zoo.program_logic.prophet_multi.
Require Export zoo_saturn.tqueue_mpmc__code.
Require Import zoo_saturn.tqueue_mpmc__types.
Require Import zoo.options.

#[local] Arguments Nat.min : simpl never.
#[local] Arguments Nat.max : simpl never.

Implicit Type b : bool.
Implicit Type front back : nat.
Implicit Type v : val.
Implicit Type vs : list val.
Implicit Type hist : list (option val).
Implicit Type slot : optional val.
Implicit Type slots : list (optional val).
Implicit Type η : gname.
Implicit Type ηs : list gname.
Implicit Type past prophs : list identifier.
Implicit Type pasts prophss : nat → list identifier.

Zoo name :=
  { self : location
  ; capacity : nat
  ; initial : nat
  ; data : val
  ; inv : namespace
  ; prophet : prophet_multi۰name
  ; model : gname
  ; history : gname
  ; lstates : gname
  ; producers : gname
  ; consumers : gname
  ; nonfull : gname
  }.

Variant lstate :=
  | Producer
  | ProducerProducer
  | ProducerConsumer
  | Consumer
  | ConsumerProducer η
  | ConsumerConsumer.
#[local] Canonical lstate۰O {SI : sidx} :=
  leibnizO lstate.
Implicit Type lstate : lstate.
Implicit Type lstates : list lstate.

#[local] Definition lstate۰winner lstate :=
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

#[local] Definition lstate۰measure lstate :=
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

Variant lstep : lstate → lstate → Prop :=
  | lstepｰproducerｰproducer :
      lstep Producer ProducerProducer
  | lstepｰproducerｰconsumer :
      lstep Consumer ProducerConsumer
  | lstepｰconsumerｰproducer η :
      lstep Producer (ConsumerProducer η)
  | lstepｰconsumerｰconsumer :
      lstep Consumer ConsumerConsumer.

#[local] Lemma lstepｰmeasure lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate۰measure lstate1 < lstate۰measure lstate2.
Proof.
  intros []; simpl; lia.
Qed.
#[local] Lemma lstepｰtcｰmeasure lstate1 lstate2 :
  tc lstep lstate1 lstate2 →
  lstate۰measure lstate1 < lstate۰measure lstate2.
Proof.
  intros Hlsteps.
  apply transitiveｰtc; first apply _.
  eapply (tc_congruence lstate۰measure); last done.
  apply lstepｰmeasure.
Qed.
#[local] Lemma lstepｰrtcｰmeasure lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate۰measure lstate1 ≤ lstate۰measure lstate2.
Proof.
  intros [<- | Hlsteps%lstepｰtcｰmeasure]%rtc_tc; lia.
Qed.

#[local] Instance lstepsｰantisymm :
  AntiSymm (=) (rtc lstep).
Proof.
  intros lstate1 lstate2 Hlsteps1 Hlsteps2%lstepｰrtcｰmeasure.
  apply rtc_tc in Hlsteps1 as [<- | Hlsteps1%lstepｰtcｰmeasure]; first done.
  lia.
Qed.

#[local] Lemma lstate۰winnerｰlb lstate :
  rtc lstep (lstate۰winner lstate) lstate.
Proof.
  destruct lstate; eauto using rtc, lstep.
Qed.
#[local] Lemma lstepｰwinner lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate۰winner lstate1 = lstate۰winner lstate2.
Proof.
  intros Hlstep. inv Hlstep; done.
Qed.
#[local] Lemma lstepsｰwinner lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate۰winner lstate1 = lstate۰winner lstate2.
Proof.
  intros Hlsteps.
  apply preorderｰrtc; [apply _.. |].
  eapply (rtc_congruence lstate۰winner); last done.
  apply lstepｰwinner.
Qed.

Zoo global :=
  { prophet : prophet_multi prophet_identifier
  ; model : twins (leibnizO (list val))
  ; history : mono_list (option val)
  ; lstate : auth_mono lstep
  ; lstates : mono_list gname
  ; saved_pred : saved_pred val
  ; oneshot : oneshot () ()
  ; producers : mono_list gname
  ; consumers : mono_list gname
  }.

Section tqueue_mpmc۰G.
  Context `{tqueue_mpmc۰G : TqueueMpmcG Σ}.

  Implicit Type Ψ : val → iProp Σ.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(tqueue_mpmc۰name۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(tqueue_mpmc۰name۰model) vs.

  #[local] Definition history۰auth' γ_history hist :=
    mono_list۰auth γ_history (DfracOwn 1) hist.
  #[local] Definition history۰auth γ :=
    history۰auth' γ.(tqueue_mpmc۰name۰history).
  #[local] Definition history۰at γ i (o : option val) :=
    mono_list۰at γ.(tqueue_mpmc۰name۰history) i o.

  #[local] Definition lstates۰auth' γ_lstates lstates : iProp Σ :=
    ∃ ηs,
    mono_list۰auth γ_lstates (DfracOwn 1) ηs ∗
    [∗ list] η; lstate ∈ ηs; lstates,
      auth_mono۰auth _ η DfracDiscarded lstate.
  #[local] Definition lstates۰auth γ :=
    lstates۰auth' γ.(tqueue_mpmc۰name۰lstates).
  #[local] Instance : CustomIpat "lstates۰auth" :=
    " ( %ηs
      & Hauth
      & Hηs
      )
    ".
  #[local] Definition lstates۰at γ i lstate : iProp Σ :=
    ∃ η,
    mono_list۰at γ.(tqueue_mpmc۰name۰lstates) i η ∗
    auth_mono۰auth _ η DfracDiscarded lstate.
  #[local] Instance : CustomIpat "lstates۰at" :=
    " ( %η{}
      & #Hat{_{}}
      & #Hη_auth{_{}}
      )
    ".
  #[local] Definition lstates۰lb γ i lstate : iProp Σ :=
    ∃ η,
    mono_list۰at γ.(tqueue_mpmc۰name۰lstates) i η ∗
    auth_mono۰lb _ η lstate.
  #[local] Instance : CustomIpat "lstates۰lb" :=
    " ( %η{}
      & #Hat{_{}}
      & #Hη_lb{_{}}
      )
    ".

  #[local] Definition producers۰auth' γ_producers i : iProp Σ :=
    ∃ ηs,
    mono_list۰auth γ_producers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition producers۰auth γ :=
    producers۰auth' γ.(tqueue_mpmc۰name۰producers).
  #[local] Instance : CustomIpat "producers۰auth" :=
    " ( %ηs
      & Hauth
      & %Hηs
      )
    ".
  #[local] Definition producers۰at γ i own : iProp Σ :=
    ∃ η,
    mono_list۰at γ.(tqueue_mpmc۰name۰producers) i η ∗
    match own with
    | Own =>
        oneshot۰pending η (DfracOwn 1) ()
    | Discard =>
        oneshot۰shot η ()
    end.
  #[local] Instance : CustomIpat "producers۰at" :=
    " ( %η{}
      & Hat{_{}}
      & Hη{}
      )
    ".

  #[local] Definition consumers۰auth' γ_consumers i : iProp Σ :=
    ∃ ηs,
    mono_list۰auth γ_consumers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition consumers۰auth γ :=
    consumers۰auth' γ.(tqueue_mpmc۰name۰consumers).
  #[local] Instance : CustomIpat "consumers۰auth" :=
    " ( %ηs{}
      & Hauth{}
      & %Hηs{}
      )
    ".
  #[local] Definition consumers۰at γ i own : iProp Σ :=
    ∃ η,
    mono_list۰at γ.(tqueue_mpmc۰name۰consumers) i η ∗
    match own with
    | Own =>
        oneshot۰pending η (DfracOwn 1) ()
    | Discard =>
        oneshot۰shot η ()
    end.
  #[local] Instance : CustomIpat "consumers۰at" :=
    " ( %η{}
      & Hat{_{}}
      & Hη{}
      )
    ".
  #[local] Definition consumers۰lb γ i : iProp Σ :=
    ∃ ηs,
    mono_list۰lb γ.(tqueue_mpmc۰name۰consumers) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Instance : CustomIpat "consumers۰lb" :=
    " ( %ηs{}
      & Hlb{}
      & %Hηs{}
      )
    ".

  #[local] Definition winner γ i : iProp Σ :=
    ∃ id prophs,
    prophet_multi۰full prophet_identifier γ.(tqueue_mpmc۰name۰prophet) i prophs ∗
    ⌜head prophs = Some id⌝ ∗
    identifier۰model id.
  #[local] Instance : CustomIpat "winner" :=
    " ( %id{}
      & %prophs{}
      & Hprophet_full{_{}}
      & %Hprophs{}
      & Hid{}
      )
    ".

  Please Definition tqueue_mpmc۰nonfull γ : iProp Σ :=
    oneshot۰pending γ.(tqueue_mpmc۰name۰nonfull) (DfracOwn 1) ().

  Please Definition tqueue_mpmc۰full γ : iProp Σ :=
    oneshot۰shot γ.(tqueue_mpmc۰name۰nonfull) ().

  Please Definition tqueue_mpmc۰finished γ : iProp Σ :=
    consumers۰lb γ γ.(tqueue_mpmc۰name۰capacity).

  #[local] Definition consumer۰au γ Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(tqueue_mpmc۰name۰inv), ∅ <{
      ∀∀ v vs',
      ⌜vs = v :: vs'⌝ ∗
      model₁ γ vs'
    , COMM
      Ψ v
    }>.

  #[local] Definition inv۰lstate۰left γ i lstate : iProp Σ :=
    match lstate with
    | ProducerProducer =>
        ∃ v,
        history۰at γ i (Some v) ∗
        ( winner γ i
        ∨ ⌜i < γ.(tqueue_mpmc۰name۰initial)⌝
        )
    | ProducerConsumer =>
        history۰at γ i None
    | ConsumerProducer η =>
        ∃ Ψ v,
        consumers۰lb γ ˖i ∗
        saved_pred η Ψ ∗
        history۰at γ i (Some v) ∗
        ( Ψ v
        ∨ consumers۰at γ i Discard
        )
    | ConsumerConsumer =>
        consumers۰lb γ ˖i
    | _ =>
        False
    end.
  #[local] Instance : CustomIpat "inv۰lstate۰left۰producer" :=
    " ( %v
      & #Hhistory_at
      & Hwinner
      )
    ".
  #[local] Instance : CustomIpat "inv۰lstate۰left۰consumer" :=
    " ( %Ψ
      & %v_
      & #Hconsumers_lb
      & #Hη_
      & #Hhistory_at_
      & HΨ
      )
    ".

  #[local] Definition inv۰lstate۰right γ i lstate : iProp Σ :=
    match lstate with
    | ConsumerProducer η =>
        ∃ Ψ,
        saved_pred η Ψ ∗
        consumer۰au γ Ψ
    | ConsumerConsumer =>
        winner γ i
    | _ =>
        False
    end.
  #[local] Instance : CustomIpat "inv۰lstate۰right" :=
    " ( %Ψ
      & #Hη
      & Hconsumer_au
      )
    ".

  #[local] Definition inv۰slot γ i slot past : iProp Σ :=
    match slot with
    | Nothing =>
        ⌜past = [] ∧ γ.(tqueue_mpmc۰name۰initial) ≤ i⌝
    | Something v =>
        history۰at γ i (Some v) ∗
        producers۰at γ i Discard ∗
        lstates۰lb γ i Producer
    | Anything =>
        consumers۰at γ i Discard ∗
        ( lstates۰lb γ i Consumer
        ∨ producers۰at γ i Discard
        )
    end.
  #[local] Instance : CustomIpat "inv۰slot۰nothing" :=
    " (%Hpast & %Hinitial)
    ".
  #[local] Instance : CustomIpat "inv۰slot۰something" :=
    " ( #Hhistory_at{_{suff}}
      & #Hproducers_at{_{suff}}
      & #Hlstates_lb_producer
      )
    ".
  #[local] Instance : CustomIpat "inv۰slot۰anything" :=
    " ( #Hconsumers_at{_{suff}}
      & { _{suff}
        ; [ #Hlstates_lb_consumer
          | #Hproducers_at_
          ]
        }
      )
    ".

  #[local] Definition inv۰nonfull γ back : iProp Σ :=
    if decide (back < γ.(tqueue_mpmc۰name۰capacity)) then
      tqueue_mpmc۰nonfull γ
    else
      tqueue_mpmc۰full γ.

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ front back hist slots vs lstates pasts prophss,
    γ.(tqueue_mpmc۰name۰self).[front] ↦ #front ∗
    γ.(tqueue_mpmc۰name۰self).[back] ↦ #back ∗
    array۰model γ.(tqueue_mpmc۰name۰data) (DfracOwn 1) (optional۰to_val <$> slots) ∗
    ⌜length slots = γ.(tqueue_mpmc۰name۰capacity)⌝ ∗
    model₂ γ vs ∗
    ⌜vs = oflatten (drop front hist)⌝ ∗
    history۰auth γ hist ∗
    ⌜length hist = back `min` γ.(tqueue_mpmc۰name۰capacity)⌝ ∗
    lstates۰auth γ lstates ∗
    ⌜length lstates = (front `max` back) `min` γ.(tqueue_mpmc۰name۰capacity)⌝ ∗
    prophet_multi۰model prophet_identifier γ.(tqueue_mpmc۰name۰prophet) pasts prophss ∗
    producers۰auth γ back ∗
    consumers۰auth γ front ∗
    ( [∗ list] i ↦ lstate ∈ take back lstates,
      inv۰lstate۰left γ i lstate
    ) ∗
    ( [∗ list] k ↦ lstate ∈ drop back lstates,
      inv۰lstate۰right γ (back + k) lstate
    ) ∗
    ( [∗ list] i ↦ slot ∈ slots,
      inv۰slot γ i slot (pasts i)
    ) ∗
    inv۰nonfull γ back.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %front{}
      & %back{}
      & %hist{}
      & %slots{}
      & %vs{}
      & %lstates{}
      & %pasts{}
      & %prophss{}
      & Ht_front
      & Ht_back
      & >Hdata_model
      & >%Hslots{}
      & Hmodel₂
      & >%Hvs{}
      & Hhistory_auth
      & >%Hhist{}
      & Hlstates_auth
      & >%Hlstates{}
      & >Hprophet_model
      & Hproducers_auth
      & Hconsumers_auth
      & Hlstates_left
      & Hlstates_right
      & Hslots
      & Hnonfull
      )
    ".
  Please Definition tqueue_mpmc۰inv γ ι : iProp Σ :=
    ⌜ι = γ.(tqueue_mpmc۰name۰inv)⌝ ∗
    γ.(tqueue_mpmc۰name۰self).[capacity] ↦□ #γ.(tqueue_mpmc۰name۰capacity) ∗
    γ.(tqueue_mpmc۰name۰self).[data] ↦□ γ.(tqueue_mpmc۰name۰data) ∗
    γ.(tqueue_mpmc۰name۰self).[proph] ↦□ γ.(tqueue_mpmc۰name۰prophet) ∗
    inv γ.(tqueue_mpmc۰name۰inv) (inv۰inner γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( ->
      & #Ht_capacity
      & #Ht_data
      & #Ht_proph
      & #Hinv
      )
    ".

  Please Definition tqueue_mpmc۰model :=
    model₁.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  Zoo derive Timeless for tqueue_mpmc۰nonfull.
  Zoo derive Timeless for tqueue_mpmc۰full.
  Zoo derive Timeless for tqueue_mpmc۰model.

  #[local] Zoo derive Persistent for lstates۰at.
  #[local] Zoo derive Persistent for lstates۰lb.
  #[local] Zoo derive Persistent for producers۰at:discarded.
  #[local] Zoo derive Persistent for consumers۰at:discarded.
  #[local] Zoo derive Persistent for consumers۰lb.
  #[local] Instance inv۰slotｰpersistent γ i slot past :
    Persistent (inv۰slot γ i slot past).
  Proof.
    destruct slot; apply _.
  Qed.
  Zoo derive Persistent for tqueue_mpmc۰inv.
  Zoo derive Persistent for tqueue_mpmc۰full.
  Zoo derive Persistent for tqueue_mpmc۰finished.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma historyｰalloc :
    ⊢ |==>
      ∃ γ_history,
      history۰auth' γ_history [].
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma history۰atｰlookup γ hist i (o : option val) :
    history۰auth γ hist -∗
    history۰at γ i o -∗
    ⌜hist !! i = Some o⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma history۰atｰagree γ i (o1 o2 : option val) :
    history۰at γ i o1 -∗
    history۰at γ i o2 -∗
    ⌜o1 = o2⌝.
  Proof.
    iIntros "Hat1 Hat2".
    iDestruct (mono_list۰atｰagree with "Hat1 Hat2") as %[= <-]. done.
  Qed.
  #[local] Lemma historyｰupdate {γ hist} (o : option val) :
    history۰auth γ hist ⊢ |==>
      history۰auth γ (hist ++ [o]) ∗
      history۰at γ (length hist) o.
  Proof.
    iIntros "Hhistory_auth".
    iMod (mono_listｰupdateｰsnoc o with "Hhistory_auth") as "Hhistory_auth".
    iDestruct (mono_list۰atｰget with "Hhistory_auth") as "#Hhistory_at".
    { rewrite list_lookup_middle //. }
    iSteps.
  Qed.

  #[local] Lemma lstatesｰalloc :
    ⊢ |==>
      ∃ γ_lstates,
      lstates۰auth' γ_lstates [].
  Proof.
    iMod (mono_listｰalloc []) as "(%γ_lstates & $)".
    iSteps.
  Qed.
  #[local] Lemma lstates۰atｰlookup γ lstates i lstate :
    lstates۰auth γ lstates -∗
    lstates۰at γ i lstate -∗
    ⌜lstates !! i = Some lstate⌝.
  Proof.
    iIntros "(:lstates۰auth) (:lstates۰at)".
    iDestruct (mono_list۰atｰvalid with "Hauth Hat") as %Hηs_lookup.
    iDestruct (big_sepL2_lookup_l with "Hηs") as "(%lstate_ & %Hlstates_lookup & Hη_auth_)"; first done.
    iDestruct (auth_mono۰authｰagreeｰL with "Hη_auth Hη_auth_") as %<-.
    iSteps.
  Qed.
  #[local] Lemma lstates۰lbｰget {γ lstates} i lstate :
    lstates !! i = Some lstate →
    lstates۰auth γ lstates -∗
    lstates۰lb γ i (lstate۰winner lstate).
  Proof.
    iIntros "%Hlstates_lookup (:lstates۰auth)".
    iDestruct (big_sepL2_lookup_r with "Hηs") as "(%η & %Hηs_lookup & Hη_auth)"; first done.
    iDestruct (auth_mono۰lbｰget with "Hη_auth") as "Hη_lb".
    iApply auth_mono۰lbｰmono in "Hη_lb".
    { apply lstate۰winnerｰlb. }
    iDestruct (mono_list۰atｰget with "Hauth") as "#Hat"; first done.
    iSteps.
  Qed.
  #[local] Lemma lstates۰lbｰagree γ i lstate1 lstate2 :
    lstates۰lb γ i lstate1 -∗
    lstates۰lb γ i lstate2 -∗
    ⌜lstate۰winner lstate1 = lstate۰winner lstate2⌝.
  Proof.
    iIntros "(:lstates۰lb =1) (:lstates۰lb =2)".
    iDestruct (mono_list۰atｰagree with "Hat_1 Hat_2") as %<-.
    iDestruct (auth_mono۰lbｰagree with "Hη_lb_1 Hη_lb_2") as %(lstate & ->%lstepsｰwinner & ->%lstepsｰwinner).
    iSteps.
  Qed.
  #[local] Lemma lstatesｰupdate {γ lstates} lstate :
    lstates۰auth γ lstates ⊢ |==>
      lstates۰auth γ (lstates ++ [lstate]) ∗
      lstates۰lb γ (length lstates) (lstate۰winner lstate) ∗
      lstates۰at γ (length lstates) lstate.
  Proof.
    iIntros "(:lstates۰auth)".
    iMod (auth_monoｰalloc _ lstate) as "(%η & Hη_auth)".
    iMod (auth_mono۰authｰpersist with "Hη_auth") as "#Hη_auth".
    iMod (mono_listｰupdateｰsnoc η with "Hauth") as "Hauth".
    iDestruct (mono_list۰atｰget with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iDestruct (auth_mono۰lbｰget with "Hη_auth") as "#Hη_lb".
    iDestruct (auth_mono۰lbｰmono _ (lstate۰winner lstate) with "Hη_lb") as "#Hη_lb_winner".
    { destruct lstate; eauto using rtc, lstep. }
    iDestruct (big_sepL2_length with "Hηs") as %->.
    iDestruct (big_sepL2ｰsnoc₂ with "Hηs Hη_auth") as "Hηs".
    iSteps.
  Qed.
  Opaque lstates۰auth'.
  Opaque lstates۰at.
  Opaque lstates۰lb.

  #[local] Lemma producersｰalloc :
    ⊢ |==>
      ∃ γ_producers,
      producers۰auth' γ_producers 0.
  Proof.
    iMod (mono_listｰalloc []) as "(%γ_producers & $)".
    iSteps.
  Qed.
  #[local] Lemma producers۰atｰexclusive γ i own :
    producers۰at γ i Own -∗
    producers۰at γ i own -∗
    False.
  Proof.
    iIntros "(:producers۰at =1) (:producers۰at =2)".
    iDestruct (mono_list۰atｰagree with "Hat_1 Hat_2") as %<-.
    destruct own.
    - iApply (oneshot۰pendingｰexclusive with "Hη1 Hη2").
    - iApply (oneshotｰpendingｰshot with "Hη1 Hη2").
  Qed.
  #[local] Lemma producers۰atｰdiscard γ i :
    producers۰at γ i Own ⊢ |==>
    producers۰at γ i Discard.
  Proof.
    iIntros "(:producers۰at)".
    iMod (oneshotｰupdateｰshot with "Hη") as "Hη".
    iSteps.
  Qed.
  #[local] Lemma producersｰupdate γ i :
    producers۰auth γ i ⊢ |==>
      producers۰auth γ ˖i ∗
      producers۰at γ i Own.
  Proof.
    iIntros "(:producers۰auth)".
    iMod oneshotｰalloc as "(%η & Hη_pending)".
    iMod (mono_listｰupdateｰsnoc η with "Hauth") as "Hauth".
    iDestruct (mono_list۰atｰget with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. simp_length/=. iSteps.
  Qed.
  Opaque producers۰auth'.
  Opaque producers۰at.

  #[local] Lemma consumersｰalloc :
    ⊢ |==>
      ∃ γ_consumers,
      consumers۰auth' γ_consumers 0.
  Proof.
    iMod (mono_listｰalloc []) as "(%γ_consumers & $)".
    iSteps.
  Qed.
  #[local] Lemma consumers۰atｰexclusive γ i own :
    consumers۰at γ i Own -∗
    consumers۰at γ i own -∗
    False.
  Proof.
    iIntros "(:consumers۰at =1) (:consumers۰at =2)".
    iDestruct (mono_list۰atｰagree with "Hat_1 Hat_2") as %<-.
    destruct own.
    - iApply (oneshot۰pendingｰexclusive with "Hη1 Hη2").
    - iApply (oneshotｰpendingｰshot with "Hη1 Hη2").
  Qed.
  #[local] Lemma consumers۰atｰdiscard γ i :
    consumers۰at γ i Own ⊢ |==>
    consumers۰at γ i Discard.
  Proof.
    iIntros "(:consumers۰at)".
    iMod (oneshotｰupdateｰshot with "Hη") as "Hη".
    iSteps.
  Qed.
  #[local] Lemma consumers۰lbｰvalid γ i j :
    consumers۰auth γ i -∗
    consumers۰lb γ j -∗
    ⌜j ≤ i⌝.
  Proof.
    iIntros "(:consumers۰auth =1) (:consumers۰lb =2)".
    iDestruct (mono_list۰lbｰvalid with "Hauth1 Hlb2") as %?%prefix_length.
    iSteps.
  Qed.
  #[local] Lemma consumers۰lbｰle {γ i1} i2 :
    i2 ≤ i1 →
    consumers۰lb γ i1 ⊢
    consumers۰lb γ i2.
  Proof.
    iIntros "% (:consumers۰lb)".
    iDestruct (mono_list۰lbｰmono (take i2 ηs) with "Hlb") as "$".
    { apply prefix_take. }
    simp_length. iSteps.
  Qed.
  #[local] Lemma consumers۰lbｰget γ i :
    consumers۰auth γ i ⊢
    consumers۰lb γ i.
  Proof.
    iIntros "(:consumers۰auth)".
    iDestruct (mono_list۰lbｰget with "Hauth") as "Hlb".
    iSteps.
  Qed.
  #[local] Lemma consumers۰lbｰget' {γ i} i' :
    i' ≤ i →
    consumers۰auth γ i ⊢
    consumers۰lb γ i'.
  Proof.
    iIntros "% Hauth".
    iDestruct (consumers۰lbｰget with "Hauth") as "Hlb".
    iApply consumers۰lbｰle in "Hlb"; first done.
    iSteps.
  Qed.
  #[local] Lemma consumersｰupdate γ i :
    consumers۰auth γ i ⊢ |==>
      consumers۰auth γ ˖i ∗
      consumers۰at γ i Own.
  Proof.
    iIntros "(:consumers۰auth)".
    iMod oneshotｰalloc as "(%η & Hη_pending)".
    iMod (mono_listｰupdateｰsnoc η with "Hauth") as "Hauth".
    iDestruct (mono_list۰atｰget with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. simp_length/=. iSteps.
  Qed.
  #[local] Instance consumers۰auth'ｰtimeless γ_consumers i :
    Timeless (consumers۰auth' γ_consumers i).
  Proof.
    apply _.
  Qed.
  Opaque consumers۰auth'.
  Opaque consumers۰at.
  Opaque consumers۰lb.

  #[local] Lemma winnerｰexclusive γ i :
    winner γ i -∗
    winner γ i -∗
    False.
  Proof.
    iIntros "(:winner =1) (:winner =2)".
    iDestruct (prophet_multi۰fullｰagree with "Hprophet_full_1 Hprophet_full_2") as %->. simp.
    iApply (identifier۰modelｰexclusive with "Hid1 Hid2").
  Qed.

  #[local] Lemma inv۰nonfullｰfull γ back :
    γ.(tqueue_mpmc۰name۰capacity) ≤ back →
    inv۰nonfull γ back ⊢
    tqueue_mpmc۰full γ.
  Proof.
    intros. rewrite /inv۰nonfull decide_False //. lia.
  Qed.
  #[local] Lemma inv۰nonfullｰfull' γ back :
    γ.(tqueue_mpmc۰name۰capacity) ≤ back →
    inv۰nonfull γ back ⊢
    inv۰nonfull γ ˖back.
  Proof.
    intros. rewrite /inv۰nonfull !decide_False //; lia.
  Qed.
  #[local] Lemma inv۰nonfullｰnonfull γ back :
    back < γ.(tqueue_mpmc۰name۰capacity) →
    inv۰nonfull γ back ⊢
    tqueue_mpmc۰nonfull γ.
  Proof.
    intros. rewrite /inv۰nonfull decide_True //.
  Qed.
  #[local] Lemma inv۰nonfullｰupdate γ back :
    tqueue_mpmc۰nonfull γ ⊢ |==>
    inv۰nonfull γ ˖back.
  Proof.
    iIntros "Hnonfull".
    rewrite /inv۰nonfull. case_decide; first iSteps.
    iApply (oneshotｰupdateｰshot with "Hnonfull").
  Qed.

  #[local] Lemma inv۰slotｰnotｰnothingｰpast {γ i slot past1} past2 :
    slot ≠ Nothing →
    inv۰slot γ i slot past1 ⊣⊢
    inv۰slot γ i slot past2.
  Proof.
    destruct slot; iSteps.
  Qed.
  #[local] Lemma inv۰slotsｰresolve {γ slots pasts} i slot proph :
    i < length slots →
    slot ≠ Nothing →
    ( [∗ list] k ↦ slot ∈ slots,
      inv۰slot γ k slot (pasts k)
    ) -∗
    inv۰slot γ i slot [] -∗
    [∗ list] k ↦ slot ∈ <[i := slot]> slots,
      inv۰slot γ k slot (alter (.++ [proph]) i pasts k).
  Proof.
    iIntros "%Hi %Hslot Hslots #Hslot".
    destruct (lookup_lt_is_Some_2 slots i) as (slot_old & Hlookup); first done.
    iDestruct (big_sepL_insert_acc with "Hslots") as "(_ & Hslots)"; first done.
    iDestruct ("Hslots" with "[]") as "Hslots".
    { rewrite (inv۰slotｰnotｰnothingｰpast []) //. }
    iApply (big_sepL_impl with "Hslots").
    iIntros "!> %k %slot' %Hlookup' Hslot'".
    destruct_decide (k = i) as -> | Hk.
    - rewrite list_lookup_insert decide_True // in Hlookup'. simplify_eq.
      destruct slot'; [done | iSteps..].
    - rewrite fn_lookup_alter_ne //.
  Qed.

  #[local] Lemma inv۰slotsｰresolve' {γ slots pasts} i slot proph :
    slots !! i = Some slot →
    slot ≠ Nothing →
    ( [∗ list] k ↦ slot ∈ slots,
      inv۰slot γ k slot (pasts k)
    ) ⊢
    [∗ list] k ↦ slot ∈ slots,
      inv۰slot γ k slot (alter (.++ [proph]) i pasts k).
  Proof.
    iIntros "%Hlookup %Hslot Hslots".
    iApply (big_sepL_impl with "Hslots").
    iIntros "!> %k %slot' %Hlookup' Hslot'".
    destruct_decide (k = i) as -> | Hk.
    - simplify_eq. destruct slot; [done | iSteps..].
    - rewrite fn_lookup_alter_ne //.
  Qed.

  Lemma tqueue_mpmc۰modelｰexclusive γ vs1 vs2 :
    tqueue_mpmc۰model γ vs1 -∗
    tqueue_mpmc۰model γ vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma tqueue_mpmcｰfullｰnonfull γ :
    tqueue_mpmc۰full γ -∗
    tqueue_mpmc۰nonfull γ -∗
    False.
  Proof.
    iIntros "Hfull Hnonfull".
    iApply (oneshotｰpendingｰshot with "Hnonfull Hfull").
  Qed.

  Lemma tqueue_mpmcｰmodelｰfinished γ ι vs E :
    ↑ι ⊆ E →
    tqueue_mpmc۰inv γ ι -∗
    tqueue_mpmc۰model γ vs -∗
    tqueue_mpmc۰finished γ ={E}=∗
      ⌜vs = []⌝ ∗
      tqueue_mpmc۰model γ vs.
  Proof.
    iIntros "% (:inv) (:model) #Hfinished".
    iInv "Hinv" as "(:inv۰inner =1)".
    iMod "Hconsumers_auth" as "Hconsumers_auth".
    iMod "Hmodel₂" as "Hmodel₂".
    iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hfinished") as %?.
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    assert (vs1 = []) as Hvs1'.
    { rewrite Hvs1 drop_ge //. lia. }
    iFrameSteps.
  Qed.

  Lemma tqueue_mpmc٠createｰspec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      tqueue_mpmc٠create #cap
    {{{
      γ
    , RET γ;
      tqueue_mpmc۰inv γ ι ∗
      tqueue_mpmc۰model γ []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".
    Z_to_nat cap.

    wp۰rec.
    wp۰apply (array٠makeｰspec with "[//]") as (data) "(_ & Hdata_model)".
    wp۰apply+ (prophet_multiｰwpｰproph prophet_identifier with "[//]") as "%γ_prophet %prophss Hprophet_model".
    wp۰block t as "#Ht_capacity #Ht_data Ht_front Ht_back #Ht_proph".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
    iMod lstatesｰalloc as "(%γ_lstates & Hlstates_auth)".
    iMod producersｰalloc as "(%γ_producers & Hproducers_auth)".
    iMod consumersｰalloc as "(%γ_consumers & Hconsumers_auth)".
    iMod (oneshotｰalloc ()) as "(%γ_nonfull & Hnonfull)".

    pose γ :=
      {|tqueue_mpmc۰name۰self := t
      ; tqueue_mpmc۰name۰capacity := cap
      ; tqueue_mpmc۰name۰initial := 0
      ; tqueue_mpmc۰name۰data := data
      ; tqueue_mpmc۰name۰inv := ι
      ; tqueue_mpmc۰name۰prophet := γ_prophet
      ; tqueue_mpmc۰name۰model := γ_model
      ; tqueue_mpmc۰name۰history := γ_history
      ; tqueue_mpmc۰name۰lstates := γ_lstates
      ; tqueue_mpmc۰name۰producers := γ_producers
      ; tqueue_mpmc۰name۰consumers := γ_consumers
      ; tqueue_mpmc۰name۰nonfull := γ_nonfull
      |}.

    iAssert (|==> inv۰nonfull γ 0)%I with "[Hnonfull]" as ">Hnonfull".
    { rewrite /inv۰nonfull. case_decide; first iSteps.
      iApply (oneshotｰupdateｰshot with "Hnonfull").
    }

    iMod (inv_alloc _ _ (inv۰inner γ) with "[- Hmodel₁ HΦ]") as "#Hinv".
    { iExists 0, 0, [], (replicate cap Nothing), [], [], (λ _, []), prophss.
      rewrite Nat2Z.id fmap_replicate. iFrameSteps.
      - simp_length.
      - iApply big_sepL_intro. iIntros "!> %i %slot %Hlookup".
        apply lookup_replicate in Hlookup as (-> & _). iSteps.
    }

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma tqueue_mpmc٠makeｰspec ι cap v :
    (0 < cap)%Z →
    {{{
      True
    }}}
      tqueue_mpmc٠make #cap v
    {{{
      γ
    , RET γ;
      tqueue_mpmc۰inv γ ι ∗
      tqueue_mpmc۰model γ [v]
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".
    Z_to_nat cap. destruct cap as [| cap]; first lia.

    wp۰rec.
    wp۰apply+ (array٠makeｰspec with "[//]") as (data) "(_ & Hdata_model)".
    wp۰apply+ (array٠unsafe_setｰspec with "Hdata_model") as "Hdata_model".
    { simp_length. lia. }
    wp۰apply+ (prophet_multiｰwpｰproph prophet_identifier with "[//]") as "%γ_prophet %prophss Hprophet_model".
    wp۰block t as "#Ht_capacity #Ht_data Ht_front Ht_back #Ht_proph".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
    iMod lstatesｰalloc as "(%γ_lstates & Hlstates_auth)".
    iMod producersｰalloc as "(%γ_producers & Hproducers_auth)".
    iMod consumersｰalloc as "(%γ_consumers & Hconsumers_auth)".
    iMod (oneshotｰalloc ()) as "(%γ_nonfull & Hnonfull)".

    pose γ :=
      {|tqueue_mpmc۰name۰self := t
      ; tqueue_mpmc۰name۰capacity := ˖cap
      ; tqueue_mpmc۰name۰initial := 1
      ; tqueue_mpmc۰name۰data := data
      ; tqueue_mpmc۰name۰inv := ι
      ; tqueue_mpmc۰name۰prophet := γ_prophet
      ; tqueue_mpmc۰name۰model := γ_model
      ; tqueue_mpmc۰name۰history := γ_history
      ; tqueue_mpmc۰name۰lstates := γ_lstates
      ; tqueue_mpmc۰name۰producers := γ_producers
      ; tqueue_mpmc۰name۰consumers := γ_consumers
      ; tqueue_mpmc۰name۰nonfull := γ_nonfull
      |}.

    iMod (modelｰupdate (γ := γ) [v] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod (historyｰupdate (γ := γ) (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)".
    iMod (lstatesｰupdate (γ := γ) ProducerProducer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)".
    iMod (producersｰupdate γ with "Hproducers_auth") as "(Hproducers_auth & Hproducers_at)".
    iMod (producers۰atｰdiscard with "Hproducers_at") as "#Hproducers_at".
    iMod (inv۰nonfullｰupdate γ 0 with "Hnonfull") as "Hnonfull".

    iAssert ([∗ list] k ↦ slot ∈ replicate cap Nothing, inv۰slot γ ˖k slot [])%I as "Hslots".
    { iApply big_sepL_intro. iIntros "!> %i %slot %Hlookup".
      apply lookup_replicate in Hlookup as (-> & _). iSteps.
    }
    iAssert (winner γ 0 ∨ ⌜0 < γ.(tqueue_mpmc۰name۰initial)⌝)%I as "Hwinner".
    { iRight. iSteps. }
    iMod (inv_alloc _ _ (inv۰inner γ) with "[- Hmodel₁ HΦ]") as "#Hinv".
    { iExists 0, 1, [Some v], (Something v :: replicate cap Nothing), [v], [ProducerProducer], (λ _, []), prophss.
      rewrite Nat2Z.id fmap_cons fmap_replicate. iFrame "∗ #".
      iSteps. simp_length.
    }

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma tqueue_mpmc٠is_emptyｰspec γ ι :
    <<<
      tqueue_mpmc۰inv γ ι
    | ∀∀ vs,
      tqueue_mpmc۰model γ vs
    >>>
      tqueue_mpmc٠is_empty γ
      @ ↑ι
    <<<
      ∃∃ b,
      ⌜if b then vs = [] else True⌝ ∗
      tqueue_mpmc۰model γ vs
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (consumers۰lbｰget with "Hconsumers_auth") as "#Hconsumers_lb".
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    wp۰pures.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰load.
    iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb") as %?.
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" $! (bool_decide (⁺back2 ≤ ⁺front1)%Z) with "[$Hmodel₁]") as "HΦ".
    { iPureIntro.
      case_bool_decide; last done.
      rewrite Hvs2 drop_ge //. lia.
    }
    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!> {%}".

    wp۰pures.
    iSteps.
  Qed.

  #[local] Lemma tqueue_mpmc٠push₁ｰspec γ ι v E Φ :
    tqueue_mpmc۰inv γ ι -∗
    ( |={⊤ ∖ ↑ι, E}=>
      ∃ vs,
      tqueue_mpmc۰model γ vs ∗
        ∀ b,
        ( if b then
            tqueue_mpmc۰model γ (vs ++ [v]) ∗
            tqueue_mpmc۰nonfull γ
          else
            tqueue_mpmc۰model γ vs ∗
            tqueue_mpmc۰full γ
        ) ={E}=∗
          ( if b then
              tqueue_mpmc۰nonfull γ
            else
              True
          ) ∗
            |={E, ⊤ ∖ ↑ι}=>
            Φ #b
    ) -∗
    WP tqueue_mpmc٠push₁ γ v {{ Φ }}.
  Proof.
    iIntros "#Hinv' HΦ".
    iDestruct "Hinv'" as "(:inv)".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
    wp۰pures.

    wp۰bind (𝗳𝗮𝗮 _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰faa.
    iMod (producersｰupdate with "Hproducers_auth") as "(Hproducers_auth & Hproducers_at)".
    destruct_decide (γ.(tqueue_mpmc۰name۰capacity) ≤ back1) as Hback1 | Hback1.

    - iDestruct (inv۰nonfullｰfull with "Hnonfull") as "#Hfull"; first done.
      iDestruct (inv۰nonfullｰfull' with "Hnonfull") as "Hnonfull"; first done.
      iMod "HΦ" as "(%vs & (:model) & HΦ)".
      iMod ("HΦ" $! false with "[$Hmodel₁ $Hfull]") as "(_ & HΦ)".
      iMod "HΦ" as "HΦ".
      rewrite !take_ge; [lia.. |].
      rewrite !(drop_ge lstates1); [lia.. |].
      iSplitR "HΦ".
      { iExists front1, ˖back1, hist1, slots1, vs1, lstates1, pasts1, prophss1.
        rewrite take_ge; first lia.
        rewrite (drop_ge lstates1); first lia.
        assert (⁺˖back1 = ⁺back1 + 1)%Z as -> by lia.
        iFrame. iIntros "!>".
        iPureIntro. split_and!; try done; lia.
      }
      iIntros "!> {%- Hback1}".

      wp۰load. wp۰pures.
      rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - iDestruct (prophet_multi۰fullｰget' _ back1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
      rewrite Nat.min_l in Hhist1; first lia.
      destruct_decide (front1 ≤ back1) as Hfront1 | Hfront1.

      + assert (length lstates1 = back1) as Hlstates1' by lia.
        rewrite firstn_all2; first lia.

        destruct_decide (head prophs = Some id) as Hwinner | Hloser.

        * iMod (historyｰupdate (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
          iMod (lstatesｰupdate ProducerProducer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1'.
          iDestruct (big_sepLｰsnoc₂ ProducerProducer with "Hlstates_left [Hid]") as "Hlstates_left".
          { rewrite Hlstates1'. iExists v. iFrame "#". iLeft. iSteps. }

          iMod "HΦ" as "(%vs & (:model) & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (modelｰupdate (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iDestruct (inv۰nonfullｰnonfull with "Hnonfull") as "Hnonfull"; first lia.
          iMod ("HΦ" $! true with "[$Hmodel₁ $Hnonfull]") as "(Hnonfull & HΦ)".
          iMod "HΦ" as "HΦ".
          iMod (inv۰nonfullｰupdate _ back1 with "Hnonfull") as "Hnonfull".

          iSplitR "Hproducers_at HΦ".
          { iFrame.
            rewrite firstn_all2. { simp_length/=. lia. }
            rewrite (skipn_all2 (n := ˖back1)). { simp_length/=. lia. }
            iFrameSteps; iPureIntro.
            - rewrite drop_app_le; first lia.
              rewrite oflattenｰsnocｰSome Hvs1 //.
            - simp_length/=. lia.
            - simp_length/=. lia.
          }
          iIntros "!> {%- Hback1 Hwinner}".

          wp۰load. wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰pures.
          do 2 wp۰load.
          wp۰apply array٠unsafe_cas_resolveｰspec.
          iIntros "%e %Hatomic %He #He H£".
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
          iApply ("He" with "[%] Hdata_model").
          { simp_length. lia. }
          iIntros "!> %b %w %Hlookup %Hcmp Hdata_model".
          apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots2_lookup).
          rewrite Nat2Z.id in Hslots2_lookup |- *.
          iStep. iIntros "%prophs2 %Hprophss2 Hprophet_model".
          iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
          destruct b; last first.
          { destruct slot.
            - exfalso. done.
            - iDestruct "Hslot" as "(:inv۰slot۰anything)".
              + iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
              + iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
            - iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
              iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
          }
          apply optional۰to_valｰsimilarｰNothingｰr in Hcmp as ->.
          iMod (producers۰atｰdiscard with "Hproducers_at") as "#Hproducers_at".
          iSplitR "HΦ".
          { iFrame. iIntros "!> !>".
            iExists (<[back1 := Something v]> slots2).
            rewrite list_fmap_insert. iFrame.
            iSplitR. { simp_length. }
            iSplitR. { done. }
            iSplitR. { done. }
            iSplitR. { done. }
            iApply (inv۰slotsｰresolve with "Hslots"); [lia | done |].
            iSteps.
          }
          iSteps.

        * iMod (historyｰupdate None with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
          iMod (lstatesｰupdate ProducerConsumer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)".
          iDestruct (big_sepLｰsnoc₂ ProducerConsumer with "Hlstates_left []") as "Hlstates_left".
          { rewrite Hlstates1'. iSteps. }
          iDestruct (inv۰nonfullｰnonfull with "Hnonfull") as "Hnonfull"; first lia.
          iMod (inv۰nonfullｰupdate _ back1 with "Hnonfull") as "Hnonfull".

          iSplitR "HΦ".
          { iFrame.
            rewrite firstn_all2. { simp_length/=. lia. }
            rewrite (skipn_all2 (n := ˖back1)). { simp_length/=. lia. }
            iFrameSteps; iPureIntro.
            - rewrite drop_app_le; first lia.
              rewrite oflattenｰsnocｰNone Hvs1 //.
            - simp_length/=. lia.
            - simp_length/=. lia.
          }
          iIntros "!> {%- Hback1 Hloser}".

          wp۰load. wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰pures.
          do 2 wp۰load.
          wp۰apply array٠unsafe_cas_resolveｰspec.
          iIntros "%e %Hatomic %He #He H£".
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
          iApply ("He" with "[%] Hdata_model").
          { simp_length. lia. }
          iIntros "!> %b %w %Hlookup %Hcmp Hdata_model".
          apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots2_lookup).
          rewrite Nat2Z.id in Hslots2_lookup |- *.
          iStep. iIntros "%prophs2 %Hprophss2 Hprophet_model".
          iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
          destruct b.
          { apply optional۰to_valｰsimilarｰNothingｰr in Hcmp as ->.
            iDestruct "Hslot" as "(:inv۰slot۰nothing)".
            iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive.
          }
          assert (slot ≠ Nothing) as Hslot.
          { intros ->. done. }
          iSplitR "HΦ".
          { iFrameSteps.
            iApply (inv۰slotsｰresolve' with "Hslots"); done.
          }
          iIntros "!> {%}".
          wp۰pures.
          wp۰apply ("HLöb" with "HΦ").

      + rewrite drop_ge /= in Hvs1; first lia. subst vs1.
        assert (length lstates1 = front1 `min` γ.(tqueue_mpmc۰name۰capacity)) as Hlstates1' by lia.
        iDestruct (consumers۰lbｰget' ˖back1 with "Hconsumers_auth") as "#Hconsumers_lb"; first lia.
        destruct (lookup_lt_is_Some_2 lstates1 back1) as (lstate & Hlstates_lookup); first lia.
        iDestruct (lstates۰lbｰget with "Hlstates_auth") as "#Hlstates_lb"; first done.
        erewrite drop_S; last done.
        iDestruct "Hlstates_right" as "(Hlstate & Hlstates_right)".

        destruct lstate as [| | | | η |].
        all: try iDestruct "Hlstate" as %[].

        * iDestruct "Hlstate" as "(:inv۰lstate۰right)".

          iMod "HΦ" as "(%vs & (:model) & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate [v] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iDestruct (inv۰nonfullｰnonfull with "Hnonfull") as "Hnonfull"; first lia.
          iMod ("HΦ" $! true with "[$Hmodel₁ $Hnonfull]") as "(Hnonfull & HΦ)".
          iMod "HΦ" as "HΦ".
          iMod (inv۰nonfullｰupdate _ back1 with "Hnonfull") as "Hnonfull".

          iMod "Hconsumer_au" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΨ" with "[$Hmodel₁ //]") as "HΨ".

          iMod (historyｰupdate (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_lb)". rewrite Hhist1.
          iDestruct (big_sepLｰsnoc₂ (ConsumerProducer η) with "Hlstates_left [HΨ]") as "Hlstates_left".
          { rewrite /= length_take Nat.min_l; first lia. iSteps. }
          iSplitR "Hproducers_at HΦ".
          { rewrite -take_S_r //.
            setoid_rewrite Nat.add_succ_r.
            iFrameSteps; iPureIntro.
            - rewrite drop_ge //. simp_length/=. lia.
            - simp_length/=. lia.
          }
          iIntros "!> {%- Hback1}".

          wp۰load. wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰pures.
          do 2 wp۰load.
          wp۰apply array٠unsafe_cas_resolveｰspec.
          iIntros "%e %Hatomic %He #He H£".
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
          iApply ("He" with "[%] Hdata_model").
          { simp_length. lia. }
          iIntros "!> %b %w %Hlookup %Hcmp Hdata_model".
          apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots2_lookup).
          rewrite Nat2Z.id in Hslots2_lookup |- *.
          iStep. iIntros "%prophs2 %Hprophss2 Hprophet_model".
          iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
          destruct b; last first.
          { destruct slot.
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive.
            - iDestruct "Hslot" as "(:inv۰slot۰anything)".
              + iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
              + iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
            - iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
              iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
          }
          apply optional۰to_valｰsimilarｰNothingｰr in Hcmp as ->.
          iMod (producers۰atｰdiscard with "Hproducers_at") as "#Hproducers_at".
          iSplitR "HΦ".
          { iFrame. iIntros "!> !>".
            iExists (<[back1 := Something v]> slots2).
            rewrite list_fmap_insert. iFrame.
            iSplitR. { simp_length. }
            iSplitR. { done. }
            iSplitR. { done. }
            iSplitR. { done. }
            iApply (inv۰slotsｰresolve with "Hslots"); [lia | done |].
            iSteps.
          }
          iSteps.

        * iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
          { iIntros (Hwinner).
            iEval (rewrite /= Nat.add_0_r) in "Hlstate".
            iDestruct (winnerｰexclusive with "Hlstate [Hid]") as %[]; first iSteps.
          }

          iMod (historyｰupdate None with "Hhistory_auth") as "(Hhistory_auth & _)".
          iDestruct (big_sepLｰsnoc₂ ConsumerConsumer with "Hlstates_left []") as "Hlstates_left".
          { rewrite /= length_take Nat.min_l; first lia. iSteps. }
          iDestruct (inv۰nonfullｰnonfull with "Hnonfull") as "Hnonfull"; first lia.
          iMod (inv۰nonfullｰupdate _ back1 with "Hnonfull") as "Hnonfull".
          iSplitR "HΦ".
          { rewrite -take_S_r //.
            setoid_rewrite Nat.add_succ_r.
            iFrameSteps; iPureIntro.
            - rewrite drop_ge //. simp_length/=. lia.
            - simp_length/=. lia.
          }
          iIntros "!> {%- Hback1 Hloser}".

          wp۰load. wp۰pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp۰pures.
          do 2 wp۰load.
          wp۰apply array٠unsafe_cas_resolveｰspec.
          iIntros "%e %Hatomic %He #He H£".
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
          iApply ("He" with "[%] Hdata_model").
          { simp_length. lia. }
          iIntros "!> %b %w %Hlookup %Hcmp Hdata_model".
          apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots2_lookup).
          rewrite Nat2Z.id in Hslots2_lookup |- *.
          iStep. iIntros "%prophs2 %Hprophss2 Hprophet_model".
          iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
          destruct b.
          { apply optional۰to_valｰsimilarｰNothingｰr in Hcmp as ->.
            iDestruct "Hslot" as "(:inv۰slot۰nothing)".
            iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive.
          }
          assert (slot ≠ Nothing) as Hslot.
          { intros ->. done. }
          iSplitR "HΦ".
          { iFrameSteps.
            iApply (inv۰slotsｰresolve' with "Hslots"); done.
          }
          iIntros "!> {%}".
          wp۰pures.
          wp۰apply ("HLöb" with "HΦ").
  Qed.

  Lemma tqueue_mpmc٠pushｰspec γ ι v E Φ :
    tqueue_mpmc۰inv γ ι -∗
    ▷ (
      |={⊤ ∖ ↑ι, E}=>
      ∃ vs,
      tqueue_mpmc۰model γ vs ∗
        ∀ b,
        ( if b then
            tqueue_mpmc۰model γ (vs ++ [v]) ∗
            tqueue_mpmc۰nonfull γ
          else
            tqueue_mpmc۰model γ vs ∗
            tqueue_mpmc۰full γ
        ) ={E}=∗
          ( if b then
              tqueue_mpmc۰nonfull γ
            else
              True
          ) ∗
            |={E, ⊤ ∖ ↑ι}=>
            Φ #b
    ) -∗
    WP tqueue_mpmc٠push γ v {{ Φ }}.
  Proof.
    iIntros "#Hinv' HΦ".
    iDestruct "Hinv'" as "(:inv)".

    wp۰rec. wp۰pures.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    destruct_decide (γ.(tqueue_mpmc۰name۰capacity) ≤ back1) as Hback1 | Hback1.

    - iDestruct (inv۰nonfullｰfull with "Hnonfull") as "#Hfull"; first done.
      iMod "HΦ" as "(%vs & (:model) & HΦ)".
      iMod ("HΦ" $! false with "[$Hmodel₁ $Hfull]") as "(_ & HΦ)".
      iMod "HΦ" as "HΦ".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%- Hback1}".

      wp۰load. wp۰pures.
      rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%- Hback1}".

      wp۰load. wp۰pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp۰pures.
      wp۰apply (tqueue_mpmc٠push₁ｰspec with "[] HΦ").
      iSteps.
  Qed.

  Lemma tqueue_mpmc٠popｰspec γ ι :
    <<<
      tqueue_mpmc۰inv γ ι
    | ∀∀ vs,
      tqueue_mpmc۰model γ vs
    >>>
      tqueue_mpmc٠pop γ
      @ ↑ι
    <<<
      ∃∃ o vs',
      tqueue_mpmc۰model γ vs' ∗
      ⌜ match o with
        | Something v =>
            vs = v :: vs'
        | Nothing =>
            vs' = vs
        | Anything =>
            vs = [] ∧
            vs' = vs
        end
      ⌝
    | RET o;
      if o is Anything then
        tqueue_mpmc۰finished γ
      else
        True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (_.{front})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    destruct_decide (γ.(tqueue_mpmc۰name۰capacity) ≤ front1) as Hfront1 | Hfront1.

    - iDestruct (consumers۰lbｰget' γ.(tqueue_mpmc۰name۰capacity) with "Hconsumers_auth") as "#Hfinished"; first done.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      assert (vs1 = []) as Hvs1'.
      { rewrite Hvs1 drop_ge //. lia. }
      iMod ("HΦ" $! Anything vs1 with "[$Hmodel₁ //]") as "HΦ".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%- Hfront1}".

      wp۰load. wp۰pures.
      rewrite bool_decide_eq_true_2; first lia.
      wp۰pures.
      iApply "HΦ". iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%- Hfront1}".

      wp۰load. wp۰pures.
      rewrite bool_decide_eq_false_2; first lia.
      wp۰pures.
      wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
      wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰faa.
      destruct_decide (γ.(tqueue_mpmc۰name۰capacity) ≤ front2) as Hfront2 | Hfront2.

      + iMod (consumersｰupdate with "Hconsumers_auth") as "(Hconsumers_auth & _)".
        iDestruct (consumers۰lbｰget' γ.(tqueue_mpmc۰name۰capacity) with "Hconsumers_auth") as "#Hfinished"; first lia.
        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        assert (vs2 = []) as Hvs2'.
        { rewrite Hvs2 drop_ge //. lia. }
        iMod ("HΦ" $! Anything vs2 with "[$Hmodel₁ //]") as "HΦ".
        iSplitR "HΦ".
        { iExists ˖front2, back2, hist2, slots2, vs2, lstates2, pasts2, prophss2.
          assert (⁺˖front2 = ⁺front2 + 1)%Z as -> by lia.
          iFrame. iIntros "!>".
          iPureIntro. split_and!; try done; try lia.
          rewrite Hvs2' drop_ge //. lia.
        }
        iIntros "!> {%- Hfront2}".

        wp۰load. wp۰pures.
        rewrite bool_decide_eq_true_2; first lia.
        wp۰pures.
        iApply "HΦ". iSteps.

      + iDestruct (prophet_multi۰fullｰget' _ front2 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
        destruct_decide (back2 ≤ front2) as Hback2 | Hback2.

        * iMod (consumersｰupdate with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".
          rewrite drop_ge /= in Hvs2; first lia. subst vs2.
          assert (length lstates2 = front2) as Hlstates2' by lia.

          destruct_decide (head prophs = Some id) as Hwinner | Hloser.

          -- iMod (lstatesｰupdate ConsumerConsumer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates2'.
             iDestruct (big_sepLｰsnoc₂ ConsumerConsumer with "Hlstates_right [Hid]") as "Hlstates_right".
             { rewrite length_drop Hlstates2' -Nat.le_add_sub; first lia.
               iSteps.
             }

             iSplitR "Hconsumers_at HΦ".
             { iFrame.
               rewrite take_app_le; first lia.
               rewrite drop_app_le; first lia.
               iFrameSteps; iPureIntro.
               - rewrite drop_ge //. lia.
               - simp_length/=. lia.
             }
             iIntros "!> {%- Hfront2}".

             wp۰load. wp۰pures.
             rewrite bool_decide_eq_false_2; first lia.
             wp۰pures.
             do 2 wp۰load.
             wp۰apply array٠unsafe_xchg_resolveｰspec.
             iIntros "%e %Hatomic %He #He H£".
             iInv "Hinv" as "(:inv۰inner =3)".
             wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
             iApply ("He" with "[%] Hdata_model").
             { simp_length. lia. }
             iIntros "!> %w %Hlookup Hdata_model".
             apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots3_lookup).
             rewrite Nat2Z.id in Hslots3_lookup |- *.
             iStep. iIntros "%prophs3 %Hprophss3 Hprophet_model".
             iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
             destruct slot; first last.
             { iDestruct "Hslot" as "(:inv۰slot۰something)".
               iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_producer") as %[=].
             } {
               iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
               iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
             }
             iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
             iMod ("HΦ" $! Nothing vs with "[$Hmodel₁ //]") as "HΦ".
             iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
             iSplitR "HΦ".
             { iFrame. iIntros "!> !>".
               iExists (<[front2 := Anything]> slots3).
               rewrite list_fmap_insert. iFrame.
               iSplitR. { simp_length. }
               iSplitR. { done. }
               iSplitR. { done. }
               iSplitR. { done. }
               iApply (inv۰slotsｰresolve with "Hslots"); [lia | done |].
               iSteps.
             }
             iIntros "!> {%}".
             iApply "HΦ". iSteps.

          -- iMod (saved_predｰalloc (λ v, Φ (optional۰to_val (Something v)))) as "(%η & #Hη)".
             iMod (lstatesｰupdate (ConsumerProducer η) with "Hlstates_auth") as "(Hlstates_auth & _ & #Hlstates_at)". rewrite Hlstates2'.
             iDestruct (big_sepLｰsnoc₂ (ConsumerProducer η) with "Hlstates_right [HΦ]") as "Hlstates_right".
             { iExists _. iFrame "#".
               rewrite /consumer۰au. iAuIntro.
               iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
               iAaccIntro with "Hmodel₁"; first iSteps. iIntros "%v %vs' (-> & Hmodel₁) !>".
               iExists (Something v), vs'. iSteps.
             }

             iSplitR "Hconsumers_at".
             { iFrame.
               rewrite take_app_le; first lia.
               rewrite drop_app_le; first lia.
               iFrameSteps; iPureIntro.
               - rewrite drop_ge //. lia.
               - simp_length/=. lia.
             }
             iIntros "!> {%- Hfront2 Hloser}".

             wp۰load. wp۰pures.
             rewrite bool_decide_eq_false_2; first lia.
             wp۰pures.
             do 2 wp۰load.
             wp۰apply array٠unsafe_xchg_resolveｰspec.
             iIntros "%e %Hatomic %He #He H£".
             iInv "Hinv" as "(:inv۰inner =3)".
             wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
             iApply ("He" with "[%] Hdata_model").
             { simp_length. lia. }
             iIntros "!> %w %Hlookup Hdata_model".
             apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots3_lookup).
             rewrite Nat2Z.id in Hslots3_lookup |- *.
             iStep. iIntros "%prophs3 %Hprophss3 Hprophet_model".
             iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
             destruct slot as [| | v].
             { iDestruct "Hslot" as "(:inv۰slot۰nothing)".
               iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
               exfalso.
               rewrite fn_lookup_alter Hpast /= in Hprophs. naive.
             } {
               iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
               iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
             }
             iDestruct "Hslot" as "(:inv۰slot۰something)".

             iDestruct (lstates۰atｰlookup with "Hlstates_auth Hlstates_at") as %Hlstates3_lookup.
             iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at") as %?%lookup_lt_Some.
             iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
             { rewrite lookup_take_Some. naive lia. }
             iDestruct "Hlstate" as "(:inv۰lstate۰left۰consumer suff=)".
             iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_") as %[= <-].
             iDestruct (saved_predｰagree v with "Hη Hη_") as "HΨ_eq".
             iMod (lc_fupd_elim_later with "H£ HΨ_eq") as "#Heq".
             iDestruct "HΨ" as "[HΦ | Hconsumers_at_]"; last first.
             { iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[]. }

             iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
             iDestruct ("Hlstates_left" with "[]") as "Hlstates_left".
             { iExists Ψ, v. iFrame "#". }
             iSplitR "HΦ".
             { iFrame. iIntros "!> !>".
               iExists (<[front2 := Anything]> slots3).
               rewrite list_fmap_insert. iFrame.
               iSplitR. { simp_length. }
               iSplitR. { done. }
               iSplitR. { done. }
               iSplitR. { done. }
               iApply (inv۰slotsｰresolve with "Hslots"); [lia | done |].
               iSteps.
             }
             iIntros "!> {%}".
             iRewrite -"Heq" in "HΦ". iSteps.

        * destruct (lookup_lt_is_Some_2 lstates2 front2) as (lstate & Hlstates_lookup); first lia.
          iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
          { rewrite lookup_take_Some. naive lia. }
          destruct lstate.
          all: try iDestruct "Hlstate" as %[].
          1,2: iMod (consumersｰupdate with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

          -- iDestruct "Hlstate" as "(:inv۰lstate۰left۰producer)".
             iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at") as %Hhist2_lookup.
             erewrite drop_S, oflattenｰconsｰSome in Hvs2; last done.

             iAssert ⌜head prophs ≠ Some id ∨ front2 < γ.(tqueue_mpmc۰name۰initial)⌝%I as %Hloser.
             { iDestruct "Hwinner" as "[Hwinner | %]"; last (iPureIntro; right; done).
               iAssert ⌜head prophs ≠ Some id⌝%I as %?.
               { iIntros (Hwinner').
                 iDestruct (winnerｰexclusive with "Hwinner [Hid]") as %[]; first iSteps.
               }
               iPureIntro. left. done.
             }

             iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
             iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
             iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
             iMod ("HΦ" $! (Something v) with "[$Hmodel₁ //]") as "HΦ".

             iDestruct ("Hlstates_left" with "[Hwinner]") as "Hlstates_left".
             { iExists v. iFrame "∗ #". }
             iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
             iIntros "!> {%- Hfront2 Hloser}".

             wp۰load. wp۰pures.
             rewrite bool_decide_eq_false_2; first lia.
             wp۰pures.
             do 2 wp۰load.
             wp۰apply array٠unsafe_xchg_resolveｰspec.
             iIntros "%e %Hatomic %He #He H£".
             iInv "Hinv" as "(:inv۰inner =3)".
             wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
             iApply ("He" with "[%] Hdata_model").
             { simp_length. lia. }
             iIntros "!> %w %Hlookup Hdata_model".
             apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots3_lookup).
             rewrite Nat2Z.id in Hslots3_lookup |- *.
             iStep. iIntros "%prophs3 %Hprophss3 Hprophet_model".
             iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
             destruct slot as [| | v_].
             { iDestruct "Hslot" as "(:inv۰slot۰nothing)".
               destruct Hloser as [Hloser | Hinitial']; last lia.
               iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
               exfalso.
               rewrite fn_lookup_alter Hpast /= in Hprophs. naive.
             } {
               iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
               iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
             }
             iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
             iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_") as %[= <-].
             iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
             iSplitR "HΦ".
             { iFrame. iIntros "!> !>".
               iExists (<[front2 := Anything]> slots3).
               rewrite list_fmap_insert. iFrame.
               iSplitR. { simp_length. }
               iSplitR. { done. }
               iSplitR. { done. }
               iSplitR. { done. }
               iApply (inv۰slotsｰresolve with "Hslots"); [lia | done |].
               iSteps.
             }
             iIntros "!> {%}".
             iApply "HΦ". iSteps.

          -- iDestruct (history۰atｰlookup with "Hhistory_auth Hlstate") as %Hhist2_lookup.
             erewrite drop_S, oflattenｰconsｰNone in Hvs2; last done.
             iDestruct (lstates۰lbｰget with "Hlstates_auth") as "#Hlstates_lb"; first done.

             iDestruct ("Hlstates_left" with "Hlstate") as "Hlstates_left".
             iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
             iIntros "!> {%- Hfront2}".

             wp۰load. wp۰pures.
             rewrite bool_decide_eq_false_2; first lia.
             wp۰pures.
             do 2 wp۰load.
             wp۰apply array٠unsafe_xchg_resolveｰspec.
             iIntros "%e %Hatomic %He #He H£".
             iInv "Hinv" as "(:inv۰inner =3)".
             wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"); [done.. |].
             iApply ("He" with "[%] Hdata_model").
             { simp_length. lia. }
             iIntros "!> %w %Hlookup Hdata_model".
             apply list_lookup_fmap_Some in Hlookup as (slot & -> & Hslots3_lookup).
             rewrite Nat2Z.id in Hslots3_lookup |- *.
             iStep. iIntros "%prophs3 %Hprophss3 Hprophet_model".
             iDestruct (big_sepL_lookup with "Hslots") as "#Hslot"; first done.
             destruct slot; first last.
             { iDestruct "Hslot" as "(:inv۰slot۰something)".
               iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_producer") as %[=].
             } {
               iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
               iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
             }
             iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
             iMod ("HΦ" $! Nothing vs with "[$Hmodel₁ //]") as "HΦ".
             iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
             iSplitR "HΦ".
             { iFrame. iIntros "!> !>".
               iExists (<[front2 := Anything]> slots3).
               rewrite list_fmap_insert. iFrame.
               iSplitR. { simp_length. }
               iSplitR. { done. }
               iSplitR. { done. }
               iSplitR. { done. }
               iApply (inv۰slotsｰresolve with "Hslots"); [lia | done |].
               iSteps.
             }
             iIntros "!> {%}".
             iApply "HΦ". iSteps.

          -- iDestruct "Hlstate" as "(:inv۰lstate۰left۰consumer)".
             iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb") as %?. lia.

          -- iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hlstate") as %?. lia.
  Qed.
End tqueue_mpmc۰G.

Require zoo_saturn.tqueue_mpmc__opaque.

Please opacify.
