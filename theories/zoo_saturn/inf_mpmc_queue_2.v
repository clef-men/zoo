Require Import zoo.prelude.
Require Import zoo.common.countable.
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
Require Import zoo.program_logic.identifier.
Require Import zoo.program_logic.prophet_identifier.
Require Import zoo.program_logic.prophet_multi.
Require Import zoo.program_logic.prophet_nat.
Require Import zoo_std.domain.
Require Import zoo_std.inf_array.
Require Import zoo_std.int.
Require Import zoo_std.optional.
Require Export zoo_saturn.inf_mpmc_queue_2__code.
Require Import zoo_saturn.inf_mpmc_queue_2__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front back : nat.
Implicit Type v : val.
Implicit Type o : option val.
Implicit Type vs : list val.
Implicit Type hist : list (option val).
Implicit Type slot : optional val.
Implicit Type slots : nat → optional val.
Implicit Type η : gname.
Implicit Type ηs : list gname.
Implicit Type past prophs : list prophet_identifier.(prophet_typed۰type).
Implicit Type pasts prophss : nat → list prophet_identifier.(prophet_typed۰type).

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
  intros Hlstep. invert Hlstep; done.
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

Class InfMpmcQueue2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] inf_mpmc_queue_2۰G۰inf_array۰G :: InfArrayG Σ
  ; #[local] inf_mpmc_queue_2۰G۰prophet۰G :: ProphetMultiG Σ prophet_identifier
  ; #[local] inf_mpmc_queue_2۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  ; #[local] inf_mpmc_queue_2۰G۰history۰G :: MonoListG Σ (option val)
  ; #[local] inf_mpmc_queue_2۰G۰lstate۰G :: AuthMonoG Σ lstep
  ; #[local] inf_mpmc_queue_2۰G۰lstates۰G :: MonoListG Σ gname
  ; #[local] inf_mpmc_queue_2۰G۰saved_pred۰G :: SavedPredG Σ val
  ; #[local] inf_mpmc_queue_2۰G۰producer۰G :: OneshotG Σ () ()
  ; #[local] inf_mpmc_queue_2۰G۰producers۰G :: MonoListG Σ gname
  ; #[local] inf_mpmc_queue_2۰G۰consumer۰G :: OneshotG Σ () ()
  ; #[local] inf_mpmc_queue_2۰G۰consumers۰G :: MonoListG Σ gname
  }.

Definition inf_mpmc_queue_2۰Σ :=
  #[inf_array۰Σ
  ; prophet_multi۰Σ prophet_identifier
  ; twins۰Σ (leibnizO (list val))
  ; mono_list۰Σ (option val)
  ; mono_list۰Σ gname
  ; auth_mono۰Σ lstep
  ; saved_pred۰Σ val
  ; oneshot۰Σ () ()
  ; mono_list۰Σ gname
  ; oneshot۰Σ () ()
  ; mono_list۰Σ gname
  ].
#[global] Instance subGｰinf_mpmc_queue_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG inf_mpmc_queue_2۰Σ Σ →
  InfMpmcQueue2G Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section inf_mpmc_queue_2۰G.
    Context `{inf_mpmc_queue_2۰G : InfMpmcQueue2G Σ}.

    Implicit Type t : location.
    Implicit Type Ψ : val → iProp Σ.

    Record inf_mpmc_queue_2۰name :=
      { inf_mpmc_queue_2۰name۰data : val
      ; inf_mpmc_queue_2۰name۰inv : namespace
      ; inf_mpmc_queue_2۰name۰prophet : prophet_id
      ; inf_mpmc_queue_2۰name۰prophet_name : prophet_multi۰name
      ; inf_mpmc_queue_2۰name۰model : gname
      ; inf_mpmc_queue_2۰name۰history : gname
      ; inf_mpmc_queue_2۰name۰lstates : gname
      ; inf_mpmc_queue_2۰name۰producers : gname
      ; inf_mpmc_queue_2۰name۰consumers : gname
      }.
    Implicit Type γ : inf_mpmc_queue_2۰name.

    #[global] Instance inf_mpmc_queue_2۰nameｰeq_dec : EqDecision inf_mpmc_queue_2۰name :=
      ltac:(solve_decision).
    #[global] Instance inf_mpmc_queue_2۰nameｰcountable :
      Countable inf_mpmc_queue_2۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      twins۰twin₁ γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ vs :=
      model₁' γ.(inf_mpmc_queue_2۰name۰model) vs.
    #[local] Definition model₂' γ_model vs :=
      twins۰twin₂ γ_model vs.
    #[local] Definition model₂ γ vs :=
      model₂' γ.(inf_mpmc_queue_2۰name۰model) vs.

    #[local] Definition history۰auth' γ_history hist :=
      mono_list۰auth γ_history (DfracOwn 1) hist.
    #[local] Definition history۰auth γ :=
      history۰auth' γ.(inf_mpmc_queue_2۰name۰history).
    #[local] Definition history۰at γ i o :=
      mono_list۰at γ.(inf_mpmc_queue_2۰name۰history) i o.

    #[local] Definition lstates۰auth' γ_lstates lstates : iProp Σ :=
      ∃ ηs,
      mono_list۰auth γ_lstates (DfracOwn 1) ηs ∗
      [∗ list] η; lstate ∈ ηs; lstates,
        auth_mono۰auth _ η DfracDiscarded lstate.
    #[local] Definition lstates۰auth γ :=
      lstates۰auth' γ.(inf_mpmc_queue_2۰name۰lstates).
    #[local] Instance : CustomIpat "lstates۰auth" :=
      " ( %ηs
        & Hauth
        & Hηs
        )
      ".
    #[local] Definition lstates۰at γ i lstate : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_mpmc_queue_2۰name۰lstates) i η ∗
      auth_mono۰auth _ η DfracDiscarded lstate.
    #[local] Instance : CustomIpat "lstates۰at" :=
      " ( %η{}
        & #Hat{_{}}
        & #Hη_auth{_{}}
        )
      ".
    #[local] Definition lstates۰lb γ i lstate : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_mpmc_queue_2۰name۰lstates) i η ∗
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
      producers۰auth' γ.(inf_mpmc_queue_2۰name۰producers).
    #[local] Instance : CustomIpat "producers۰auth" :=
      " ( %ηs
        & Hauth
        & %Hηs
        )
      ".
    #[local] Definition producers۰at γ i own : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_mpmc_queue_2۰name۰producers) i η ∗
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
      consumers۰auth' γ.(inf_mpmc_queue_2۰name۰consumers).
    #[local] Instance : CustomIpat "consumers۰auth" :=
      " ( %ηs{}
        & Hauth{}
        & %Hηs{}
        )
      ".
    #[local] Definition consumers۰at γ i own : iProp Σ :=
      ∃ η,
      mono_list۰at γ.(inf_mpmc_queue_2۰name۰consumers) i η ∗
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
      mono_list۰lb γ.(inf_mpmc_queue_2۰name۰consumers) ηs ∗
      ⌜length ηs = i⌝.
    #[local] Instance : CustomIpat "consumers۰lb" :=
      " ( %ηs{}
        & Hlb{}
        & %Hηs{}
        )
      ".

    #[local] Definition winner γ i : iProp Σ :=
      ∃ id prophs,
      prophet_multi۰full prophet_identifier γ.(inf_mpmc_queue_2۰name۰prophet_name) i prophs ∗
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

    #[local] Definition consumer۰au γ Ψ : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(inf_mpmc_queue_2۰name۰inv), ∅ <{
        ∀∀ v vs',
        ⌜vs = v :: vs'⌝ ∗
        model₁ γ vs'
      , COMM
        Ψ v
      }>.

    #[local] Definition inv۰lstate۰left γ back i lstate : iProp Σ :=
      match lstate with
      | ProducerProducer =>
          ∃ v,
          history۰at γ i (Some v) ∗
          winner γ i
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
          ⌜past = []⌝
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
      " %Hpast
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

    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ front back hist slots vs lstates pasts prophss,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      inf_array۰model γ.(inf_mpmc_queue_2۰name۰data) slots ∗
      model₂ γ vs ∗
      ⌜vs = oflatten (drop front hist)⌝ ∗
      history۰auth γ hist ∗
      ⌜length hist = back⌝ ∗
      lstates۰auth γ lstates ∗
      ⌜length lstates = front `max` back⌝ ∗
      prophet_multi۰model prophet_identifier γ.(inf_mpmc_queue_2۰name۰prophet) γ.(inf_mpmc_queue_2۰name۰prophet_name) pasts prophss ∗
      producers۰auth γ back ∗
      consumers۰auth γ front ∗
      ( [∗ list] i ↦ lstate ∈ take back lstates,
        inv۰lstate۰left γ back i lstate
      ) ∗
      ( [∗ list] k ↦ lstate ∈ drop back lstates,
        inv۰lstate۰right γ (back + k) lstate
      ) ∗
      ( ∀ i,
        inv۰slot γ i (slots i) (pasts i)
      ).
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
        )
      ".
    Definition inf_mpmc_queue_2۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(inf_mpmc_queue_2۰name۰inv)⌝ ∗
      t.[data] ↦□ γ.(inf_mpmc_queue_2۰name۰data) ∗
      t.[proph] ↦□ #γ.(inf_mpmc_queue_2۰name۰prophet) ∗
      inf_array۰inv γ.(inf_mpmc_queue_2۰name۰data) ∗
      inv γ.(inf_mpmc_queue_2۰name۰inv) (inv۰inner t γ).
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Ht_data
        & #Ht_proph
        & #Hdata_inv
        & #Hinv
        )
      ".

    Definition inf_mpmc_queue_2۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[global] Instance inf_mpmc_queue_2۰modelｰtimeless γ vs :
      Timeless (inf_mpmc_queue_2۰model γ vs).
    Proof.
      apply _.
    Qed.

    #[local] Instance lstates۰atｰpersistent γ i lstate :
      Persistent (lstates۰at γ i lstate).
    Proof.
      apply _.
    Qed.
    #[local] Instance lstates۰lbｰpersistent γ i lstate :
      Persistent (lstates۰lb γ i lstate).
    Proof.
      apply _.
    Qed.
    #[local] Instance producers۰atｰpersistent γ i :
      Persistent (producers۰at γ i Discard).
    Proof.
      apply _.
    Qed.
    #[local] Instance consumers۰atｰpersistent γ i :
      Persistent (consumers۰at γ i Discard).
    Proof.
      apply _.
    Qed.
    #[local] Instance consumers۰lbｰpersistent γ i :
      Persistent (consumers۰lb γ i).
    Proof.
      apply _.
    Qed.
    #[local] Instance inv۰slotｰpersistent γ i slot past :
      Persistent (inv۰slot γ i slot past).
    Proof.
      destruct slot; apply _.
    Qed.
    #[global] Instance inf_mpmc_queue_2۰invｰpersistent t γ ι :
      Persistent (inf_mpmc_queue_2۰inv t γ ι).
    Proof.
      apply _.
    Qed.

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
    #[local] Lemma history۰atｰlookup γ hist i o :
      history۰auth γ hist -∗
      history۰at γ i o -∗
      ⌜hist !! i = Some o⌝.
    Proof.
      apply mono_list۰atｰvalid.
    Qed.
    #[local] Lemma history۰atｰagree γ i o1 o2 :
      history۰at γ i o1 -∗
      history۰at γ i o2 -∗
      ⌜o1 = o2⌝.
    Proof.
      iIntros "Hat1 Hat2".
      iDestruct (mono_list۰atｰagree with "Hat1 Hat2") as %[= <-]. done.
    Qed.
    #[local] Lemma history۰atｰget {γ hist} i o :
      hist !! i = Some o →
      history۰auth γ hist ⊢
      history۰at γ i o.
    Proof.
      apply mono_list۰atｰget.
    Qed.
    #[local] Lemma historyｰupdate {γ hist} o :
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
      iDestruct (auth_mono۰lbｰmono with "Hη_lb") as "Hη_lb".
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
      iSteps. simpl_length/=. iSteps.
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
      simpl_length. iSteps.
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
      iDestruct (consumers۰lbｰle with "Hlb") as "Hlb"; first done.
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
      iSteps. simpl_length/=. iSteps.
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
      iDestruct (prophet_multi۰fullｰagree with "Hprophet_full_1 Hprophet_full_2") as %->. simplify.
      iApply (identifier۰modelｰexclusive with "Hid1 Hid2").
    Qed.

    #[local] Lemma inv۰slotｰnotｰnothingｰpast {γ i slot past1} past2 :
      slot ≠ Nothing →
      inv۰slot γ i slot past1 ⊣⊢
      inv۰slot γ i slot past2.
    Proof.
      destruct slot; iSteps.
    Qed.

    Lemma inf_mpmc_queue_2۰modelｰexclusive γ vs1 vs2 :
      inf_mpmc_queue_2۰model γ vs1 -∗
      inf_mpmc_queue_2۰model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma inf_mpmc_queue_2٠createｰspec ι :
      {{{
        True
      }}}
        inf_mpmc_queue_2٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        inf_mpmc_queue_2۰inv t γ ι ∗
        inf_mpmc_queue_2۰model γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰apply (prophet_multiｰwpｰproph prophet_identifier with "[//]") as "%pid %γ_prophet %prophss Hprophet_model".
      wp۰apply (inf_array٠createｰspec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
      wp۰block t as "Hmeta" "(Ht_data & Ht_front & Ht_back & Ht_proph & _)".
      iMod (pointstoｰpersist with "Ht_data") as "#Ht_data".
      iMod (pointstoｰpersist with "Ht_proph") as "#Ht_proph".

      iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
      iMod lstatesｰalloc as "(%γ_lstates & Hlstates_auth)".
      iMod producersｰalloc as "(%γ_producers & Hproducers_auth)".
      iMod consumersｰalloc as "(%γ_consumers & Hconsumers_auth)".

      pose γ :=
        {|inf_mpmc_queue_2۰name۰data := data
        ; inf_mpmc_queue_2۰name۰inv := ι
        ; inf_mpmc_queue_2۰name۰prophet := pid
        ; inf_mpmc_queue_2۰name۰prophet_name := γ_prophet
        ; inf_mpmc_queue_2۰name۰model := γ_model
        ; inf_mpmc_queue_2۰name۰history := γ_history
        ; inf_mpmc_queue_2۰name۰lstates := γ_lstates
        ; inf_mpmc_queue_2۰name۰producers := γ_producers
        ; inf_mpmc_queue_2۰name۰consumers := γ_consumers
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (λ _, Nothing). iSteps. iExists []. iSteps.
    Qed.

    Lemma inf_mpmc_queue_2٠sizeｰspec t γ ι :
      <<<
        inf_mpmc_queue_2۰inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_2۰model γ vs
      >>>
        inf_mpmc_queue_2٠size #t @ ↑ι
      <<<
        inf_mpmc_queue_2۰model γ vs
      | sz,
        RET #sz;
        ⌜length vs ≤ sz⌝
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec.

      wp۰bind (_.{front})%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰load.
      iDestruct (consumers۰lbｰget with "Hconsumers_auth") as "#Hconsumers_lb1".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_nat₁ with "[//]") as (pid proph) "Hproph".
      wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰load.
      destruct_decide (proph = front1) as -> | Hproph.

      - destruct_decide (front2 = front1) as -> | ?.

        + iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΦ" with "Hmodel₁") as "HΦ".

          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {%- Hvs2 Hhist2}".

          wp۰pures.

          wp۰bind (_.{front})%E.
          iInv "Hinv" as "(:inv۰inner =3)".
          wp۰load.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {% -Hvs2 Hhist2}".

          wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
          iSteps. iPureIntro.
          rewrite Hvs2. simpl_length. lia.

        + iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb1") as %?.
          iDestruct (consumers۰lbｰget with "Hconsumers_auth") as "#Hconsumers_lb2".
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp۰pures.

          wp۰bind (_.{front})%E.
          iInv "Hinv" as "(:inv۰inner =3)".
          wp۰load.
          iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb2") as %?.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
          iSteps.

      - iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp۰pures.

        wp۰bind (_.{front})%E.
        iInv "Hinv" as "(:inv۰inner =3)".
        wp۰load.
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
        iSteps.
    Qed.

    Lemma inf_mpmc_queue_2٠is_emptyｰspec t γ ι :
      <<<
        inf_mpmc_queue_2۰inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_2۰model γ vs
      >>>
        inf_mpmc_queue_2٠is_empty #t @ ↑ι
      <<<
        inf_mpmc_queue_2۰model γ vs
      | b,
        RET #b;
        ⌜if b then vs = [] else True⌝
      >>>.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec.

      awp۰apply (inf_mpmc_queue_2٠sizeｰspec with "Hinv").
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; iSteps. iPureIntro.
      case_bool_decide as Hlength; last done.
      apply nil_length_inv. lia.
    Qed.

    Lemma inf_mpmc_queue_2٠pushｰspec t γ ι v :
      <<<
        inf_mpmc_queue_2۰inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_2۰model γ vs
      >>>
        inf_mpmc_queue_2٠push #t v @ ↑ι
      <<<
        inf_mpmc_queue_2۰model γ (vs ++ [v])
      | RET ();
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec.
      wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
      wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰faa.
      iMod (producersｰupdate with "Hproducers_auth") as "(Hproducers_auth & Hproducers_at)".
      iDestruct (prophet_multi۰fullｰget' _ back1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
      destruct_decide (front1 ≤ back1) as Hfirst | Hlast.

      - rewrite Nat.max_r // in Hlstates1.
        rewrite firstn_all2; first lia.

        destruct_decide (head prophs = Some id) as Hwinner | Hloser.

        + iMod (historyｰupdate (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
          iMod (lstatesｰupdate ProducerProducer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1.
          iDestruct (big_sepLｰsnoc₂ ProducerProducer with "Hlstates_left [Hid]") as "Hlstates_left".
          { rewrite Hlstates1. iSteps. }

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (modelｰupdate (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

          iSplitR "Hproducers_at HΦ".
          { iFrame.
            rewrite firstn_all2. { simpl_length/=. lia. }
            rewrite (skipn_all2 (n := ˖back1)).
            { simpl_length/=. lia. }
            iFrameSteps; iPureIntro.
            - rewrite drop_app_le; first lia.
              rewrite oflattenｰsnocｰSome Hvs1 //.
            - simpl_length/=. lia.
            - simpl_length/=. lia.
          }
          iIntros "!> {%- Hwinner}".

          do 2 wp۰load.

          wp۰apply (inf_array٠cas_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b; last first.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - exfalso. done.
            - iDestruct "Hslot" as "(:inv۰slot۰anything)".
              + iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
              + iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
            - iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
              iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
          }
          iMod (producers۰atｰdiscard with "Hproducers_at") as "#Hproducers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fnｰcomposeｰinsert _ _ _ (Something v)).
            iFrameSteps.
            rewrite fnｰlookupｰinsert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iMod (historyｰupdate None with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
          iMod (lstatesｰupdate ProducerConsumer with "Hlstates_auth") as "(Hlstates_auth & Hlstates_lb & _)".
          iDestruct (big_sepLｰsnoc₂ ProducerConsumer with "Hlstates_left []") as "Hlstates_left".
          { rewrite Hlstates1 //. }
          iSplitR "HΦ".
          { iFrame.
            rewrite firstn_all2. { simpl_length/=. lia. }
            rewrite (skipn_all2 (n := ˖back1)).
            { simpl_length/=. lia. }
            iFrameSteps; iPureIntro.
            - rewrite drop_app_le; first lia.
              rewrite oflattenｰsnocｰNone Hvs1 //.
            - simpl_length/=. lia.
            - simpl_length/=. lia.
          }
          iIntros "!> {%- Hloser}".

          do 2 wp۰load.

          wp۰apply (inf_array٠cas_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
            - exfalso. done.
            - exfalso. done.
          }
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { iFrameSteps.
            rewrite fnｰlookupｰalter. case_decide; last done.
            subst. rewrite inv۰slotｰnotｰnothingｰpast //.
            intros Heq. rewrite Heq // in Hslots2.
          }
          iSteps.

      - rewrite drop_ge /= in Hvs1; first lia. subst vs1.
        rewrite Nat.max_l in Hlstates1; first lia.
        iDestruct (consumers۰lbｰget' ˖back1 with "Hconsumers_auth") as "#Hconsumers_lb"; first lia.
        destruct (lookup_lt_is_Some_2 lstates1 back1) as (lstate & Hlstates_lookup); first lia.
        iDestruct (lstates۰lbｰget with "Hlstates_auth") as "#Hlstates_lb"; first done.
        erewrite drop_S; last done.
        iDestruct "Hlstates_right" as "(Hlstate & Hlstates_right)".

        destruct lstate as [| | | | η |].
        all: try iDestruct "Hlstate" as %[].

        + iDestruct "Hlstate" as "(:inv۰lstate۰right)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate [v] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

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
            - rewrite drop_ge //. { simpl_length/=. lia. }
            - simpl_length/=. lia.
          }
          iIntros "!> {%}".

          do 2 wp۰load.

          wp۰apply (inf_array٠cas_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b; last first.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
            - iDestruct "Hslot" as "(:inv۰slot۰anything)".
              + iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
              + iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
            - iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
              iDestruct (producers۰atｰexclusive with "Hproducers_at Hproducers_at_") as %[].
          }
          iMod (producers۰atｰdiscard with "Hproducers_at") as "#Hproducers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fnｰcomposeｰinsert _ _ _ (Something v)).
            iFrameSteps.
            rewrite fnｰlookupｰinsert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
          { iIntros (Hwinner).
            iEval (rewrite /= Nat.add_0_r) in "Hlstate".
            iDestruct (winnerｰexclusive with "Hlstate [Hid]") as %[]; first iSteps.
          }

          iMod (historyｰupdate None with "Hhistory_auth") as "(Hhistory_auth & _)".
          iDestruct (big_sepLｰsnoc₂ ConsumerConsumer with "Hlstates_left []") as "Hlstates_left".
          { rewrite /= length_take Nat.min_l; first lia. iSteps. }
          iSplitR "HΦ".
          { rewrite -take_S_r //.
            setoid_rewrite Nat.add_succ_r.
            iFrameSteps; iPureIntro.
            - rewrite drop_ge //. { simpl_length/=. lia. }
            - simpl_length/=. lia.
          }
          iIntros "!> {%- Hloser}".

          do 2 wp۰load.

          wp۰apply (inf_array٠cas_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
            - exfalso. done.
            - exfalso. done.
          }
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { iFrameSteps.
            rewrite fnｰlookupｰalter. case_decide; last done.
            subst. rewrite inv۰slotｰnotｰnothingｰpast //.
            intros Heq. rewrite Heq // in Hslots2.
          }
          iSteps.
    Qed.

    Lemma inf_mpmc_queue_2٠popｰspec t γ ι :
      <<<
        inf_mpmc_queue_2۰inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_2۰model γ vs
      >>>
        inf_mpmc_queue_2٠pop #t @ ↑ι
      <<<
        ∃∃ v vs',
        ⌜vs = v :: vs'⌝ ∗
        inf_mpmc_queue_2۰model γ vs'
      | RET v;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec.
      wp۰apply+ (wpｰid with "[//]") as (id) "Hid".
      wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰faa.
      iDestruct (prophet_multi۰fullｰget' _ front1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
      destruct_decide (back1 ≤ front1) as Hfirst | Hlast.

      - rewrite drop_ge /= in Hvs1; first lia. subst vs1.
        rewrite Nat.max_l // in Hlstates1.

        iMod (consumersｰupdate with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

        destruct_decide (head prophs = Some id) as Hwinner | Hloser.

        + iMod (lstatesｰupdate ConsumerConsumer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1.
          iDestruct (big_sepLｰsnoc₂ ConsumerConsumer with "Hlstates_right [Hid]") as "Hlstates_right".
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
          iIntros "!> {%- Hwinner}".

          do 2 wp۰load.

          wp۰apply (inf_array٠xchg_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1); first last.
          { iDestruct "Hslot" as "(:inv۰slot۰something)".
            iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_producer") as %[=].
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fnｰcomposeｰinsert _ _ _ Anything).
            iFrameSteps.
            rewrite fnｰlookupｰinsert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iMod (saved_predｰalloc Φ) as "(%η & #Hη)".
          iMod (lstatesｰupdate (ConsumerProducer η) with "Hlstates_auth") as "(Hlstates_auth & _ & #Hlstates_at)". rewrite Hlstates1.
          iDestruct (big_sepLｰsnoc₂ (ConsumerProducer η) with "Hlstates_right [HΦ]") as "Hlstates_right".
          { iSteps.
            rewrite /consumer۰au. iAuIntro.
            iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
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
          iIntros "!> {%- Hloser}".

          do 2 wp۰load.

          wp۰apply (inf_array٠xchg_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1) as [| | v].
          { iDestruct "Hslot" as "(:inv۰slot۰nothing)".
            iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iDestruct "Hslot" as "(:inv۰slot۰something)".

          iDestruct (lstates۰atｰlookup with "Hlstates_auth Hlstates_at") as %Hlstates2_lookup.
          iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at") as %?%lookup_lt_Some.
          iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
          { rewrite lookup_take_Some. naive_solver. }
          iDestruct "Hlstate" as "(:inv۰lstate۰left۰consumer suff=)".
          iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_") as %[= <-].
          iDestruct (saved_predｰagree v with "Hη Hη_") as "#Heq".
          iDestruct "HΨ" as "[HΦ | Hconsumers_at_]"; last first.
          { iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[]. }

          iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fnｰcomposeｰinsert _ _ _ Anything).
            iFrameSteps.
            rewrite fnｰlookupｰinsert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iIntros "!> {%}".

          wp۰pures.
          iRewrite "Heq". iSteps.

      - rewrite Nat.max_r in Hlstates1; first lia.
        destruct (lookup_lt_is_Some_2 lstates1 front1) as (lstate & Hlstates_lookup); first lia.
        iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
        { rewrite lookup_take_Some. naive_solver lia. }
        destruct lstate.
        all: try iDestruct "Hlstate" as %[].
        1,2: iMod (consumersｰupdate with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

        + iDestruct "Hlstate" as "(:inv۰lstate۰left۰producer)".
          iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at") as %Hhist1_lookup.
          erewrite drop_S, oflattenｰconsｰSome in Hvs1; last done.

          iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
          { iIntros (Hwinner).
            iDestruct (winnerｰexclusive with "Hwinner [Hid]") as %[]; first iSteps.
          }

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (modelｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁ //] [//]") as "HΦ".

          iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
          iIntros "!> {%- Hloser}".

          do 2 wp۰load.

          wp۰apply (inf_array٠xchg_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1) as [| | v_].
          { iDestruct "Hslot" as "(:inv۰slot۰nothing)".
            iDestruct (prophet_multi۰fullｰvalid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
          iDestruct (history۰atｰagree with "Hhistory_at Hhistory_at_") as %[= <-].
          iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fnｰcomposeｰinsert _ _ _ Anything).
            iFrameSteps.
            rewrite fnｰlookupｰinsert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iDestruct (history۰atｰlookup with "Hhistory_auth Hlstate") as %Hhist1_lookup.
          erewrite drop_S, oflattenｰconsｰNone in Hvs1; last done.
          iDestruct (lstates۰lbｰget with "Hlstates_auth") as "#Hlstates_lb"; first done.

          iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          do 2 wp۰load.

          wp۰apply (inf_array٠xchg_resolveｰspec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multiｰwpｰresolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1) as [| | v]; first last.
          { iDestruct "Hslot" as "(:inv۰slot۰something)".
            iDestruct (lstates۰lbｰagree with "Hlstates_lb Hlstates_lb_producer") as %[=].
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰atｰexclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iMod (consumers۰atｰdiscard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fnｰcomposeｰinsert _ _ _ Anything).
            iFrameSteps.
            rewrite fnｰlookupｰinsert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iDestruct "Hlstate" as "(:inv۰lstate۰left۰consumer)".
          iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hconsumers_lb") as %?. lia.

        + iDestruct (consumers۰lbｰvalid with "Hconsumers_auth Hlstate") as %?. lia.
    Qed.
  End inf_mpmc_queue_2۰G.

  #[global] Opaque inf_mpmc_queue_2۰inv.
  #[global] Opaque inf_mpmc_queue_2۰model.
End base.

Require zoo_saturn.inf_mpmc_queue_2__opaque.

Section inf_mpmc_queue_2۰G.
  Context `{inf_mpmc_queue_2۰G : InfMpmcQueue2G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition inf_mpmc_queue_2۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_mpmc_queue_2۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition inf_mpmc_queue_2۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.inf_mpmc_queue_2۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  #[global] Instance inf_mpmc_queue_2۰modelｰtimeless t vs :
    Timeless (inf_mpmc_queue_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_mpmc_queue_2۰invｰpersistent t ι :
    Persistent (inf_mpmc_queue_2۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_mpmc_queue_2۰modelｰexclusive t vs1 vs2 :
    inf_mpmc_queue_2۰model t vs1 -∗
    inf_mpmc_queue_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_mpmc_queue_2۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_mpmc_queue_2٠createｰspec ι :
    {{{
      True
    }}}
      inf_mpmc_queue_2٠create ()
    {{{
      t
    , RET t;
      inf_mpmc_queue_2۰inv t ι ∗
      inf_mpmc_queue_2۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.inf_mpmc_queue_2٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma inf_mpmc_queue_2٠sizeｰspec t ι :
    <<<
      inf_mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2۰model t vs
    >>>
      inf_mpmc_queue_2٠size t @ ↑ι
    <<<
      inf_mpmc_queue_2۰model t vs
    | sz,
      RET #sz;
      ⌜length vs ≤ sz⌝
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_mpmc_queue_2٠sizeｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_2٠is_emptyｰspec t ι :
    <<<
      inf_mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2۰model t vs
    >>>
      inf_mpmc_queue_2٠is_empty t @ ↑ι
    <<<
      inf_mpmc_queue_2۰model t vs
    | b,
      RET #b;
      ⌜if b then vs = [] else True⌝
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_mpmc_queue_2٠is_emptyｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_2٠pushｰspec t ι v :
    <<<
      inf_mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2۰model t vs
    >>>
      inf_mpmc_queue_2٠push t v @ ↑ι
    <<<
      inf_mpmc_queue_2۰model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_mpmc_queue_2٠pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_2٠popｰspec t ι :
    <<<
      inf_mpmc_queue_2۰inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2۰model t vs
    >>>
      inf_mpmc_queue_2٠pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = v :: vs'⌝ ∗
      inf_mpmc_queue_2۰model t vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.inf_mpmc_queue_2٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End inf_mpmc_queue_2۰G.

#[global] Opaque inf_mpmc_queue_2۰inv.
#[global] Opaque inf_mpmc_queue_2۰model.
