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
  | lstep𑁒producer𑁒producer :
      lstep Producer ProducerProducer
  | lstep𑁒producer𑁒consumer :
      lstep Consumer ProducerConsumer
  | lstep𑁒consumer𑁒producer η :
      lstep Producer (ConsumerProducer η)
  | lstep𑁒consumer𑁒consumer :
      lstep Consumer ConsumerConsumer.

#[local] Lemma lstep𑁒measure lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate۰measure lstate1 < lstate۰measure lstate2.
Proof.
  intros []; simpl; lia.
Qed.
#[local] Lemma lstep𑁒tc𑁒measure lstate1 lstate2 :
  tc lstep lstate1 lstate2 →
  lstate۰measure lstate1 < lstate۰measure lstate2.
Proof.
  intros Hlsteps.
  apply transitive𑁒tc; first apply _.
  eapply (tc_congruence lstate۰measure); last done.
  apply lstep𑁒measure.
Qed.
#[local] Lemma lstep𑁒rtc𑁒measure lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate۰measure lstate1 ≤ lstate۰measure lstate2.
Proof.
  intros [<- | Hlsteps%lstep𑁒tc𑁒measure]%rtc_tc; lia.
Qed.

#[local] Instance lsteps𑁒antisymm :
  AntiSymm (=) (rtc lstep).
Proof.
  intros lstate1 lstate2 Hlsteps1 Hlsteps2%lstep𑁒rtc𑁒measure.
  apply rtc_tc in Hlsteps1 as [<- | Hlsteps1%lstep𑁒tc𑁒measure]; first done.
  lia.
Qed.

#[local] Lemma lstate۰winner𑁒lb lstate :
  rtc lstep (lstate۰winner lstate) lstate.
Proof.
  destruct lstate; eauto using rtc, lstep.
Qed.
#[local] Lemma lstep𑁒winner lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate۰winner lstate1 = lstate۰winner lstate2.
Proof.
  intros Hlstep. invert Hlstep; done.
Qed.
#[local] Lemma lsteps𑁒winner lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate۰winner lstate1 = lstate۰winner lstate2.
Proof.
  intros Hlsteps.
  apply preorder𑁒rtc; [apply _.. |].
  eapply (rtc_congruence lstate۰winner); last done.
  apply lstep𑁒winner.
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
#[global] Instance subG𑁒inf_mpmc_queue_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
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

    #[global] Instance inf_mpmc_queue_2۰name𑁒eq_dec : EqDecision inf_mpmc_queue_2۰name :=
      ltac:(solve_decision).
    #[global] Instance inf_mpmc_queue_2۰name𑁒countable :
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

    #[global] Instance inf_mpmc_queue_2۰model𑁒timeless γ vs :
      Timeless (inf_mpmc_queue_2۰model γ vs).
    Proof.
      apply _.
    Qed.

    #[local] Instance lstates۰at𑁒persistent γ i lstate :
      Persistent (lstates۰at γ i lstate).
    Proof.
      apply _.
    Qed.
    #[local] Instance lstates۰lb𑁒persistent γ i lstate :
      Persistent (lstates۰lb γ i lstate).
    Proof.
      apply _.
    Qed.
    #[local] Instance producers۰at𑁒persistent γ i :
      Persistent (producers۰at γ i Discard).
    Proof.
      apply _.
    Qed.
    #[local] Instance consumers۰at𑁒persistent γ i :
      Persistent (consumers۰at γ i Discard).
    Proof.
      apply _.
    Qed.
    #[local] Instance consumers۰lb𑁒persistent γ i :
      Persistent (consumers۰lb γ i).
    Proof.
      apply _.
    Qed.
    #[local] Instance inv۰slot𑁒persistent γ i slot past :
      Persistent (inv۰slot γ i slot past).
    Proof.
      destruct slot; apply _.
    Qed.
    #[global] Instance inf_mpmc_queue_2۰inv𑁒persistent t γ ι :
      Persistent (inf_mpmc_queue_2۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma model𑁒alloc :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model [] ∗
        model₂' γ_model [].
    Proof.
      apply twins𑁒alloc'.
    Qed.
    #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma model𑁒agree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: twins𑁒agree𑁒L.
    Qed.
    #[local] Lemma model𑁒update {γ vs1 vs2} vs :
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      apply twins𑁒update.
    Qed.

    #[local] Lemma history𑁒alloc :
      ⊢ |==>
        ∃ γ_history,
        history۰auth' γ_history [].
    Proof.
      apply mono_list𑁒alloc.
    Qed.
    #[local] Lemma history۰at𑁒lookup γ hist i o :
      history۰auth γ hist -∗
      history۰at γ i o -∗
      ⌜hist !! i = Some o⌝.
    Proof.
      apply mono_list۰at𑁒valid.
    Qed.
    #[local] Lemma history۰at𑁒agree γ i o1 o2 :
      history۰at γ i o1 -∗
      history۰at γ i o2 -∗
      ⌜o1 = o2⌝.
    Proof.
      iIntros "Hat1 Hat2".
      iDestruct (mono_list۰at𑁒agree with "Hat1 Hat2") as %[= <-]. done.
    Qed.
    #[local] Lemma history۰at𑁒get {γ hist} i o :
      hist !! i = Some o →
      history۰auth γ hist ⊢
      history۰at γ i o.
    Proof.
      apply mono_list۰at𑁒get.
    Qed.
    #[local] Lemma history𑁒update {γ hist} o :
      history۰auth γ hist ⊢ |==>
        history۰auth γ (hist ++ [o]) ∗
        history۰at γ (length hist) o.
    Proof.
      iIntros "Hhistory_auth".
      iMod (mono_list𑁒update𑁒snoc o with "Hhistory_auth") as "Hhistory_auth".
      iDestruct (mono_list۰at𑁒get with "Hhistory_auth") as "#Hhistory_at".
      { rewrite list_lookup_middle //. }
      iSteps.
    Qed.

    #[local] Lemma lstates𑁒alloc :
      ⊢ |==>
        ∃ γ_lstates,
        lstates۰auth' γ_lstates [].
    Proof.
      iMod (mono_list𑁒alloc []) as "(%γ_lstates & $)".
      iSteps.
    Qed.
    #[local] Lemma lstates۰at𑁒lookup γ lstates i lstate :
      lstates۰auth γ lstates -∗
      lstates۰at γ i lstate -∗
      ⌜lstates !! i = Some lstate⌝.
    Proof.
      iIntros "(:lstates۰auth) (:lstates۰at)".
      iDestruct (mono_list۰at𑁒valid with "Hauth Hat") as %Hηs_lookup.
      iDestruct (big_sepL2_lookup_l with "Hηs") as "(%lstate_ & %Hlstates_lookup & Hη_auth_)"; first done.
      iDestruct (auth_mono۰auth𑁒agree𑁒L with "Hη_auth Hη_auth_") as %<-.
      iSteps.
    Qed.
    #[local] Lemma lstates۰lb𑁒get {γ lstates} i lstate :
      lstates !! i = Some lstate →
      lstates۰auth γ lstates -∗
      lstates۰lb γ i (lstate۰winner lstate).
    Proof.
      iIntros "%Hlstates_lookup (:lstates۰auth)".
      iDestruct (big_sepL2_lookup_r with "Hηs") as "(%η & %Hηs_lookup & Hη_auth)"; first done.
      iDestruct (auth_mono۰lb𑁒get with "Hη_auth") as "Hη_lb".
      iDestruct (auth_mono۰lb𑁒mono with "Hη_lb") as "Hη_lb".
      { apply lstate۰winner𑁒lb. }
      iDestruct (mono_list۰at𑁒get with "Hauth") as "#Hat"; first done.
      iSteps.
    Qed.
    #[local] Lemma lstates۰lb𑁒agree γ i lstate1 lstate2 :
      lstates۰lb γ i lstate1 -∗
      lstates۰lb γ i lstate2 -∗
      ⌜lstate۰winner lstate1 = lstate۰winner lstate2⌝.
    Proof.
      iIntros "(:lstates۰lb =1) (:lstates۰lb =2)".
      iDestruct (mono_list۰at𑁒agree with "Hat_1 Hat_2") as %<-.
      iDestruct (auth_mono۰lb𑁒agree with "Hη_lb_1 Hη_lb_2") as %(lstate & ->%lsteps𑁒winner & ->%lsteps𑁒winner).
      iSteps.
    Qed.
    #[local] Lemma lstates𑁒update {γ lstates} lstate :
      lstates۰auth γ lstates ⊢ |==>
        lstates۰auth γ (lstates ++ [lstate]) ∗
        lstates۰lb γ (length lstates) (lstate۰winner lstate) ∗
        lstates۰at γ (length lstates) lstate.
    Proof.
      iIntros "(:lstates۰auth)".
      iMod (auth_mono𑁒alloc _ lstate) as "(%η & Hη_auth)".
      iMod (auth_mono۰auth𑁒persist with "Hη_auth") as "#Hη_auth".
      iMod (mono_list𑁒update𑁒snoc η with "Hauth") as "Hauth".
      iDestruct (mono_list۰at𑁒get with "Hauth") as "#Hat".
      { apply list_lookup_middle. done. }
      iDestruct (auth_mono۰lb𑁒get with "Hη_auth") as "#Hη_lb".
      iDestruct (auth_mono۰lb𑁒mono _ (lstate۰winner lstate) with "Hη_lb") as "#Hη_lb_winner".
      { destruct lstate; eauto using rtc, lstep. }
      iDestruct (big_sepL2_length with "Hηs") as %->.
      iDestruct (big_sepL2𑁒snoc₂ with "Hηs Hη_auth") as "Hηs".
      iSteps.
    Qed.
    Opaque lstates۰auth'.
    Opaque lstates۰at.
    Opaque lstates۰lb.

    #[local] Lemma producers𑁒alloc :
      ⊢ |==>
        ∃ γ_producers,
        producers۰auth' γ_producers 0.
    Proof.
      iMod (mono_list𑁒alloc []) as "(%γ_producers & $)".
      iSteps.
    Qed.
    #[local] Lemma producers۰at𑁒exclusive γ i own :
      producers۰at γ i Own -∗
      producers۰at γ i own -∗
      False.
    Proof.
      iIntros "(:producers۰at =1) (:producers۰at =2)".
      iDestruct (mono_list۰at𑁒agree with "Hat_1 Hat_2") as %<-.
      destruct own.
      - iApply (oneshot۰pending𑁒exclusive with "Hη1 Hη2").
      - iApply (oneshot𑁒pending𑁒shot with "Hη1 Hη2").
    Qed.
    #[local] Lemma producers۰at𑁒discard γ i :
      producers۰at γ i Own ⊢ |==>
      producers۰at γ i Discard.
    Proof.
      iIntros "(:producers۰at)".
      iMod (oneshot𑁒update𑁒shot with "Hη") as "Hη".
      iSteps.
    Qed.
    #[local] Lemma producers𑁒update γ i :
      producers۰auth γ i ⊢ |==>
        producers۰auth γ ˖i ∗
        producers۰at γ i Own.
    Proof.
      iIntros "(:producers۰auth)".
      iMod oneshot𑁒alloc as "(%η & Hη_pending)".
      iMod (mono_list𑁒update𑁒snoc η with "Hauth") as "Hauth".
      iDestruct (mono_list۰at𑁒get with "Hauth") as "#Hat".
      { apply list_lookup_middle. done. }
      iSteps. simpl_length/=. iSteps.
    Qed.
    Opaque producers۰auth'.
    Opaque producers۰at.

    #[local] Lemma consumers𑁒alloc :
      ⊢ |==>
        ∃ γ_consumers,
        consumers۰auth' γ_consumers 0.
    Proof.
      iMod (mono_list𑁒alloc []) as "(%γ_consumers & $)".
      iSteps.
    Qed.
    #[local] Lemma consumers۰at𑁒exclusive γ i own :
      consumers۰at γ i Own -∗
      consumers۰at γ i own -∗
      False.
    Proof.
      iIntros "(:consumers۰at =1) (:consumers۰at =2)".
      iDestruct (mono_list۰at𑁒agree with "Hat_1 Hat_2") as %<-.
      destruct own.
      - iApply (oneshot۰pending𑁒exclusive with "Hη1 Hη2").
      - iApply (oneshot𑁒pending𑁒shot with "Hη1 Hη2").
    Qed.
    #[local] Lemma consumers۰at𑁒discard γ i :
      consumers۰at γ i Own ⊢ |==>
      consumers۰at γ i Discard.
    Proof.
      iIntros "(:consumers۰at)".
      iMod (oneshot𑁒update𑁒shot with "Hη") as "Hη".
      iSteps.
    Qed.
    #[local] Lemma consumers۰lb𑁒valid γ i j :
      consumers۰auth γ i -∗
      consumers۰lb γ j -∗
      ⌜j ≤ i⌝.
    Proof.
      iIntros "(:consumers۰auth =1) (:consumers۰lb =2)".
      iDestruct (mono_list۰lb𑁒valid with "Hauth1 Hlb2") as %?%prefix_length.
      iSteps.
    Qed.
    #[local] Lemma consumers۰lb𑁒le {γ i1} i2 :
      i2 ≤ i1 →
      consumers۰lb γ i1 ⊢
      consumers۰lb γ i2.
    Proof.
      iIntros "% (:consumers۰lb)".
      iDestruct (mono_list۰lb𑁒mono (take i2 ηs) with "Hlb") as "$".
      { apply prefix_take. }
      simpl_length. iSteps.
    Qed.
    #[local] Lemma consumers۰lb𑁒get γ i :
      consumers۰auth γ i ⊢
      consumers۰lb γ i.
    Proof.
      iIntros "(:consumers۰auth)".
      iDestruct (mono_list۰lb𑁒get with "Hauth") as "Hlb".
      iSteps.
    Qed.
    #[local] Lemma consumers۰lb𑁒get' {γ i} i' :
      i' ≤ i →
      consumers۰auth γ i ⊢
      consumers۰lb γ i'.
    Proof.
      iIntros "% Hauth".
      iDestruct (consumers۰lb𑁒get with "Hauth") as "Hlb".
      iDestruct (consumers۰lb𑁒le with "Hlb") as "Hlb"; first done.
      iSteps.
    Qed.
    #[local] Lemma consumers𑁒update γ i :
      consumers۰auth γ i ⊢ |==>
        consumers۰auth γ ˖i ∗
        consumers۰at γ i Own.
    Proof.
      iIntros "(:consumers۰auth)".
      iMod oneshot𑁒alloc as "(%η & Hη_pending)".
      iMod (mono_list𑁒update𑁒snoc η with "Hauth") as "Hauth".
      iDestruct (mono_list۰at𑁒get with "Hauth") as "#Hat".
      { apply list_lookup_middle. done. }
      iSteps. simpl_length/=. iSteps.
    Qed.
    Opaque consumers۰auth'.
    Opaque consumers۰at.
    Opaque consumers۰lb.

    #[local] Lemma winner𑁒exclusive γ i :
      winner γ i -∗
      winner γ i -∗
      False.
    Proof.
      iIntros "(:winner =1) (:winner =2)".
      iDestruct (prophet_multi۰full𑁒agree with "Hprophet_full_1 Hprophet_full_2") as %->. simplify.
      iApply (identifier۰model𑁒exclusive with "Hid1 Hid2").
    Qed.

    #[local] Lemma inv۰slot𑁒not𑁒nothing𑁒past {γ i slot past1} past2 :
      slot ≠ Nothing →
      inv۰slot γ i slot past1 ⊣⊢
      inv۰slot γ i slot past2.
    Proof.
      destruct slot; iSteps.
    Qed.

    Lemma inf_mpmc_queue_2۰model𑁒exclusive γ vs1 vs2 :
      inf_mpmc_queue_2۰model γ vs1 -∗
      inf_mpmc_queue_2۰model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁𑁒exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma inf_mpmc_queue_2٠create𑁒spec ι :
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
      wp۰apply (prophet_multi𑁒wp𑁒proph prophet_identifier with "[//]") as "%pid %γ_prophet %prophss Hprophet_model".
      wp۰apply (inf_array٠create𑁒spec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
      wp۰block t as "Hmeta" "(Ht_data & Ht_front & Ht_back & Ht_proph & _)".
      iMod (pointsto𑁒persist with "Ht_data") as "#Ht_data".
      iMod (pointsto𑁒persist with "Ht_proph") as "#Ht_proph".

      iMod model𑁒alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod history𑁒alloc as "(%γ_history & Hhistory_auth)".
      iMod lstates𑁒alloc as "(%γ_lstates & Hlstates_auth)".
      iMod producers𑁒alloc as "(%γ_producers & Hproducers_auth)".
      iMod consumers𑁒alloc as "(%γ_consumers & Hconsumers_auth)".

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

    Lemma inf_mpmc_queue_2٠size𑁒spec t γ ι :
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
      iDestruct (consumers۰lb𑁒get with "Hconsumers_auth") as "#Hconsumers_lb1".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (prophet_typed₁𑁒wp𑁒proph prophet_nat₁ with "[//]") as (pid proph) "Hproph".
      wp۰pures.

      wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰load.
      destruct_decide (proph = front1) as -> | Hproph.

      - destruct_decide (front2 = front1) as -> | ?.

        + iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΦ" with "Hmodel₁") as "HΦ".

          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {%- Hvs2 Hhist2}".

          wp۰pures.

          wp۰bind (_.{front})%E.
          iInv "Hinv" as "(:inv۰inner =3)".
          wp۰load.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {% -Hvs2 Hhist2}".

          wp۰apply+ (prophet_typed₁𑁒wp𑁒resolve with "Hproph"); [done.. |].
          iSteps. iPureIntro.
          rewrite Hvs2. simpl_length. lia.

        + iDestruct (consumers۰lb𑁒valid with "Hconsumers_auth Hconsumers_lb1") as %?.
          iDestruct (consumers۰lb𑁒get with "Hconsumers_auth") as "#Hconsumers_lb2".
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp۰pures.

          wp۰bind (_.{front})%E.
          iInv "Hinv" as "(:inv۰inner =3)".
          wp۰load.
          iDestruct (consumers۰lb𑁒valid with "Hconsumers_auth Hconsumers_lb2") as %?.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ (prophet_typed₁𑁒wp𑁒resolve with "Hproph"); [done.. |].
          iSteps.

      - iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp۰pures.

        wp۰bind (_.{front})%E.
        iInv "Hinv" as "(:inv۰inner =3)".
        wp۰load.
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp۰apply+ (prophet_typed₁𑁒wp𑁒resolve with "Hproph"); [done.. |].
        iSteps.
    Qed.

    Lemma inf_mpmc_queue_2٠is_empty𑁒spec t γ ι :
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

      awp۰apply (inf_mpmc_queue_2٠size𑁒spec with "Hinv").
      iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; iSteps. iPureIntro.
      case_bool_decide as Hlength; last done.
      apply nil_length_inv. lia.
    Qed.

    Lemma inf_mpmc_queue_2٠push𑁒spec t γ ι v :
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
      wp۰apply+ (wp𑁒id with "[//]") as (id) "Hid".
      wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰faa.
      iMod (producers𑁒update with "Hproducers_auth") as "(Hproducers_auth & Hproducers_at)".
      iDestruct (prophet_multi۰full𑁒get' _ back1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
      destruct_decide (front1 ≤ back1) as Hfirst | Hlast.

      - rewrite Nat.max_r // in Hlstates1.
        rewrite firstn_all2; first lia.

        destruct_decide (head prophs = Some id) as Hwinner | Hloser.

        + iMod (history𑁒update (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
          iMod (lstates𑁒update ProducerProducer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1.
          iDestruct (big_sepL𑁒snoc₂ ProducerProducer with "Hlstates_left [Hid]") as "Hlstates_left".
          { rewrite Hlstates1. iSteps. }

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (model𑁒update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

          iSplitR "Hproducers_at HΦ".
          { iFrame.
            rewrite firstn_all2. { simpl_length/=. lia. }
            rewrite (skipn_all2 (n := ˖back1)).
            { simpl_length/=. lia. }
            iFrameSteps; iPureIntro.
            - rewrite drop_app_le; first lia.
              rewrite oflatten𑁒snoc𑁒Some Hvs1 //.
            - simpl_length/=. lia.
            - simpl_length/=. lia.
          }
          iIntros "!> {%- Hwinner}".

          do 2 wp۰load.

          wp۰apply (inf_array٠cas_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b; last first.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - exfalso. done.
            - iDestruct "Hslot" as "(:inv۰slot۰anything)".
              + iDestruct (lstates۰lb𑁒agree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
              + iDestruct (producers۰at𑁒exclusive with "Hproducers_at Hproducers_at_") as %[].
            - iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
              iDestruct (producers۰at𑁒exclusive with "Hproducers_at Hproducers_at_") as %[].
          }
          iMod (producers۰at𑁒discard with "Hproducers_at") as "#Hproducers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fn𑁒compose𑁒insert _ _ _ (Something v)).
            iFrameSteps.
            rewrite fn𑁒lookup𑁒insert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iMod (history𑁒update None with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at)". rewrite Hhist1.
          iMod (lstates𑁒update ProducerConsumer with "Hlstates_auth") as "(Hlstates_auth & Hlstates_lb & _)".
          iDestruct (big_sepL𑁒snoc₂ ProducerConsumer with "Hlstates_left []") as "Hlstates_left".
          { rewrite Hlstates1 //. }
          iSplitR "HΦ".
          { iFrame.
            rewrite firstn_all2. { simpl_length/=. lia. }
            rewrite (skipn_all2 (n := ˖back1)).
            { simpl_length/=. lia. }
            iFrameSteps; iPureIntro.
            - rewrite drop_app_le; first lia.
              rewrite oflatten𑁒snoc𑁒None Hvs1 //.
            - simpl_length/=. lia.
            - simpl_length/=. lia.
          }
          iIntros "!> {%- Hloser}".

          do 2 wp۰load.

          wp۰apply (inf_array٠cas_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰full𑁒valid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
            - exfalso. done.
            - exfalso. done.
          }
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { iFrameSteps.
            rewrite fn𑁒lookup𑁒alter. case_decide; last done.
            subst. rewrite inv۰slot𑁒not𑁒nothing𑁒past //.
            intros Heq. rewrite Heq // in Hslots2.
          }
          iSteps.

      - rewrite drop_ge /= in Hvs1; first lia. subst vs1.
        rewrite Nat.max_l in Hlstates1; first lia.
        iDestruct (consumers۰lb𑁒get' ˖back1 with "Hconsumers_auth") as "#Hconsumers_lb"; first lia.
        destruct (lookup_lt_is_Some_2 lstates1 back1) as (lstate & Hlstates_lookup); first lia.
        iDestruct (lstates۰lb𑁒get with "Hlstates_auth") as "#Hlstates_lb"; first done.
        erewrite drop_S; last done.
        iDestruct "Hlstates_right" as "(Hlstate & Hlstates_right)".

        destruct lstate as [| | | | η |].
        all: try iDestruct "Hlstate" as %[].

        + iDestruct "Hlstate" as "(:inv۰lstate۰right)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (model𑁒update [v] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

          iMod "Hconsumer_au" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (model𑁒update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΨ" with "[$Hmodel₁ //]") as "HΨ".

          iMod (history𑁒update (Some v) with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_lb)". rewrite Hhist1.
          iDestruct (big_sepL𑁒snoc₂ (ConsumerProducer η) with "Hlstates_left [HΨ]") as "Hlstates_left".
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

          wp۰apply (inf_array٠cas_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b; last first.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰full𑁒valid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
            - iDestruct "Hslot" as "(:inv۰slot۰anything)".
              + iDestruct (lstates۰lb𑁒agree with "Hlstates_lb Hlstates_lb_consumer") as %[=].
              + iDestruct (producers۰at𑁒exclusive with "Hproducers_at Hproducers_at_") as %[].
            - iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
              iDestruct (producers۰at𑁒exclusive with "Hproducers_at Hproducers_at_") as %[].
          }
          iMod (producers۰at𑁒discard with "Hproducers_at") as "#Hproducers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fn𑁒compose𑁒insert _ _ _ (Something v)).
            iFrameSteps.
            rewrite fn𑁒lookup𑁒insert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
          { iIntros (Hwinner).
            iEval (rewrite /= Nat.add_0_r) in "Hlstate".
            iDestruct (winner𑁒exclusive with "Hlstate [Hid]") as %[]; first iSteps.
          }

          iMod (history𑁒update None with "Hhistory_auth") as "(Hhistory_auth & _)".
          iDestruct (big_sepL𑁒snoc₂ ConsumerConsumer with "Hlstates_left []") as "Hlstates_left".
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

          wp۰apply (inf_array٠cas_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e %b % % %Hslots2 Hdata_model".
          rewrite Nat2Z.id in Hslots2 |- *.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          destruct b.
          { iDestruct ("Hslots" $! back1) as "Hslot".
            destruct (slots2 back1).
            - iDestruct "Hslot" as "(:inv۰slot۰nothing)".
              iDestruct (prophet_multi۰full𑁒valid with "Hprophet_model Hprophet_full") as %Hprophs.
              exfalso.
              rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
            - exfalso. done.
            - exfalso. done.
          }
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { iFrameSteps.
            rewrite fn𑁒lookup𑁒alter. case_decide; last done.
            subst. rewrite inv۰slot𑁒not𑁒nothing𑁒past //.
            intros Heq. rewrite Heq // in Hslots2.
          }
          iSteps.
    Qed.

    Lemma inf_mpmc_queue_2٠pop𑁒spec t γ ι :
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
      wp۰apply+ (wp𑁒id with "[//]") as (id) "Hid".
      wp۰pures.

      wp۰bind (𝗳𝗮𝗮 _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰faa.
      iDestruct (prophet_multi۰full𑁒get' _ front1 with "Hprophet_model") as "(%prophs & #Hprophet_full)".
      destruct_decide (back1 ≤ front1) as Hfirst | Hlast.

      - rewrite drop_ge /= in Hvs1; first lia. subst vs1.
        rewrite Nat.max_l // in Hlstates1.

        iMod (consumers𑁒update with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

        destruct_decide (head prophs = Some id) as Hwinner | Hloser.

        + iMod (lstates𑁒update ConsumerConsumer with "Hlstates_auth") as "(Hlstates_auth & #Hlstates_lb & _)". rewrite Hlstates1.
          iDestruct (big_sepL𑁒snoc₂ ConsumerConsumer with "Hlstates_right [Hid]") as "Hlstates_right".
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

          wp۰apply (inf_array٠xchg_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1); first last.
          { iDestruct "Hslot" as "(:inv۰slot۰something)".
            iDestruct (lstates۰lb𑁒agree with "Hlstates_lb Hlstates_lb_producer") as %[=].
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰at𑁒exclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iMod (consumers۰at𑁒discard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fn𑁒compose𑁒insert _ _ _ Anything).
            iFrameSteps.
            rewrite fn𑁒lookup𑁒insert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iMod (saved_pred𑁒alloc Φ) as "(%η & #Hη)".
          iMod (lstates𑁒update (ConsumerProducer η) with "Hlstates_auth") as "(Hlstates_auth & _ & #Hlstates_at)". rewrite Hlstates1.
          iDestruct (big_sepL𑁒snoc₂ (ConsumerProducer η) with "Hlstates_right [HΦ]") as "Hlstates_right".
          { iSteps.
            rewrite /consumer۰au. iAuIntro.
            iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model)".
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

          wp۰apply (inf_array٠xchg_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1) as [| | v].
          { iDestruct "Hslot" as "(:inv۰slot۰nothing)".
            iDestruct (prophet_multi۰full𑁒valid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰at𑁒exclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iDestruct "Hslot" as "(:inv۰slot۰something)".

          iDestruct (lstates۰at𑁒lookup with "Hlstates_auth Hlstates_at") as %Hlstates2_lookup.
          iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at") as %?%lookup_lt_Some.
          iDestruct (big_sepL_lookup_acc with "Hlstates_left") as "(Hlstate & Hlstates_left)".
          { rewrite lookup_take_Some. naive_solver. }
          iDestruct "Hlstate" as "(:inv۰lstate۰left۰consumer suff=)".
          iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_") as %[= <-].
          iDestruct (saved_pred𑁒agree v with "Hη Hη_") as "#Heq".
          iDestruct "HΨ" as "[HΦ | Hconsumers_at_]"; last first.
          { iDestruct (consumers۰at𑁒exclusive with "Hconsumers_at Hconsumers_at_") as %[]. }

          iMod (consumers۰at𑁒discard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fn𑁒compose𑁒insert _ _ _ Anything).
            iFrameSteps.
            rewrite fn𑁒lookup𑁒insert. case_decide.
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
        1,2: iMod (consumers𑁒update with "Hconsumers_auth") as "(Hconsumers_auth & Hconsumers_at)".

        + iDestruct "Hlstate" as "(:inv۰lstate۰left۰producer)".
          iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at") as %Hhist1_lookup.
          erewrite drop_S, oflatten𑁒cons𑁒Some in Hvs1; last done.

          iAssert ⌜head prophs ≠ Some id⌝%I as %Hloser.
          { iIntros (Hwinner).
            iDestruct (winner𑁒exclusive with "Hwinner [Hid]") as %[]; first iSteps.
          }

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (model𑁒update with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁ //] [//]") as "HΦ".

          iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
          iIntros "!> {%- Hloser}".

          do 2 wp۰load.

          wp۰apply (inf_array٠xchg_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1) as [| | v_].
          { iDestruct "Hslot" as "(:inv۰slot۰nothing)".
            iDestruct (prophet_multi۰full𑁒valid with "Hprophet_model Hprophet_full") as %Hprophs.
            exfalso.
            rewrite fn_lookup_alter Hpast /= in Hprophs. naive_solver.
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰at𑁒exclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iDestruct "Hslot" as "(:inv۰slot۰something suff=)".
          iDestruct (history۰at𑁒agree with "Hhistory_at Hhistory_at_") as %[= <-].
          iMod (consumers۰at𑁒discard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fn𑁒compose𑁒insert _ _ _ Anything).
            iFrameSteps.
            rewrite fn𑁒lookup𑁒insert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iDestruct (history۰at𑁒lookup with "Hhistory_auth Hlstate") as %Hhist1_lookup.
          erewrite drop_S, oflatten𑁒cons𑁒None in Hvs1; last done.
          iDestruct (lstates۰lb𑁒get with "Hlstates_auth") as "#Hlstates_lb"; first done.

          iSplitR "Hconsumers_at HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          do 2 wp۰load.

          wp۰apply (inf_array٠xchg_resolve𑁒spec with "Hdata_inv"); first lia.
          iMod (inv_acc with "Hinv") as "((:inv۰inner =2) & Hclose1)"; first done.
          iStep. iIntros "%e % % Hdata_model".
          rewrite Nat2Z.id.
          wp۰apply (prophet_multi𑁒wp𑁒resolve' with "Hprophet_model"). 1: done.
          wp۰pures.
          iStep. iIntros "!> %prophs2 %Hprophss2 Hprophet_model".
          iDestruct (bi.forall_elim front1 with "Hslots") as "#-#Hslot".
          destruct (slots2 front1) as [| | v]; first last.
          { iDestruct "Hslot" as "(:inv۰slot۰something)".
            iDestruct (lstates۰lb𑁒agree with "Hlstates_lb Hlstates_lb_producer") as %[=].
          } {
            iDestruct "Hslot" as "(:inv۰slot۰anything suff=)".
            iDestruct (consumers۰at𑁒exclusive with "Hconsumers_at Hconsumers_at_") as %[].
          }
          iMod (consumers۰at𑁒discard with "Hconsumers_at") as "#Hconsumers_at".
          iMod ("Hclose1" with "[- HΦ]") as "_".
          { rewrite -(fn𑁒compose𑁒insert _ _ _ Anything).
            iFrameSteps.
            rewrite fn𑁒lookup𑁒insert. case_decide.
            - subst. iSteps.
            - rewrite fn_lookup_alter_ne //.
          }
          iSteps.

        + iDestruct "Hlstate" as "(:inv۰lstate۰left۰consumer)".
          iDestruct (consumers۰lb𑁒valid with "Hconsumers_auth Hconsumers_lb") as %?. lia.

        + iDestruct (consumers۰lb𑁒valid with "Hconsumers_auth Hlstate") as %?. lia.
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

  #[global] Instance inf_mpmc_queue_2۰model𑁒timeless t vs :
    Timeless (inf_mpmc_queue_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_mpmc_queue_2۰inv𑁒persistent t ι :
    Persistent (inf_mpmc_queue_2۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_mpmc_queue_2۰model𑁒exclusive t vs1 vs2 :
    inf_mpmc_queue_2۰model t vs1 -∗
    inf_mpmc_queue_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_mpmc_queue_2۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_mpmc_queue_2٠create𑁒spec ι :
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

    iApply wp𑁒fupd.
    wp۰apply (base.inf_mpmc_queue_2٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (meta𑁒set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma inf_mpmc_queue_2٠size𑁒spec t ι :
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

    awp۰apply (base.inf_mpmc_queue_2٠size𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_2٠is_empty𑁒spec t ι :
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

    awp۰apply (base.inf_mpmc_queue_2٠is_empty𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_2٠push𑁒spec t ι v :
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

    awp۰apply (base.inf_mpmc_queue_2٠push𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_2٠pop𑁒spec t ι :
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

    awp۰apply (base.inf_mpmc_queue_2٠pop𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End inf_mpmc_queue_2۰G.

#[global] Opaque inf_mpmc_queue_2۰inv.
#[global] Opaque inf_mpmc_queue_2۰model.
