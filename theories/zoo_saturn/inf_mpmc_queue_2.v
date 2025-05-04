From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.auth_nat_max
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
  optional
  inf_array.
From zoo_saturn Require Export
  base
  inf_mpmc_queue_2__code.
From zoo_saturn Require Import
  inf_mpmc_queue_2__types.
From zoo Require Import
  options.

Section oflatten.
  Definition oflatten `(l : list $ option A) :=
    omap id l.
End oflatten.

Implicit Types l : location.
Implicit Types front back : nat.
Implicit Types v t : val.
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
Implicit Types pasts prophss : nat → list global_prophet.(typed_prophet_type).

#[local] Program Definition local_prophet := {|
  typed_strong_prophet1_type :=
    nat ;
  typed_strong_prophet1_of_val v _ :=
    match v with
    | ValInt i =>
        Some (Z.to_nat i)
    | _ =>
        None
    end ;
  typed_strong_prophet1_to_val i :=
    (#i, ()%V) ;
|}.
Solve Obligations of local_prophet with
  try done.
Next Obligation.
  intros i v _ [= -> ->]. rewrite /= Nat2Z.id //.
Qed.

Inductive lstate :=
  | Producer
  | ProducerProducer
  | ProducerConsumer
  | Consumer
  | ConsumerProducer η
  | ConsumerConsumer.
#[local] Canonical lstate_O :=
  leibnizO lstate.
Implicit Types lstate : lstate.
Implicit Types lstates : list lstate.

Inductive lstep : lstate → lstate → Prop :=
  | lstep_producer_producer :
      lstep Producer ProducerProducer
  | lstep_producer_consumer :
      lstep Producer ProducerConsumer
  | lstep_consumer_producer η :
      lstep Consumer (ConsumerProducer η)
  | lstep_consumer_consumer :
      lstep Consumer ConsumerConsumer.

Class InfMpmcQueue2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_mpmc_queue_2_G_inf_array_G :: InfArrayG Σ ;
  #[local] inf_mpmc_queue_2_G_prophets_G :: WiseProphetsG Σ global_prophet ;
  #[local] inf_mpmc_queue_2_G_front_G :: AuthNatMaxG Σ ;
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
  auth_nat_max_Σ ;
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

Inductive ownership :=
  | Own
  | Discarded.

Section inf_mpmc_queue_2_G.
  Context `{inf_mpmc_queue_2_G : InfMpmcQueue2G Σ}.

  Implicit Types Ψ : val → iProp Σ.

  Record metadata := {
    metadata_data : val ;
    metadata_inv : namespace ;
    metadata_prophet : gname ;
    metadata_prophet_name : wise_prophets_name ;
    metadata_front : gname ;
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

  #[local] Definition front_auth' γ_front i :=
    auth_nat_max_auth γ_front (DfracOwn 1) i.
  #[local] Definition front_auth γ i :=
    front_auth' γ.(metadata_front) i.
  #[local] Definition front_lb γ i :=
    auth_nat_max_lb γ.(metadata_front) i.

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
  #[local] Definition history_at γ i v :=
    mono_list_at γ.(metadata_history) i (Some v).

  #[local] Definition lstates_auth' γ_lstates lstates : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_lstates (DfracOwn 1) ηs ∗
    [∗ list] η; lstate ∈ ηs; lstates,
      auth_mono_auth _ η (DfracOwn 1) lstate.
  #[local] Definition lstates_auth γ :=
    lstates_auth' γ.(metadata_lstates).
  #[local] Definition lstates_lb γ i lstate : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_lstates) i η ∗
    auth_mono_lb _ η lstate.

  #[local] Definition producers_auth' γ_producers i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_producers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition producers_auth γ :=
    producers_auth' γ.(metadata_producers).
  #[local] Definition producers_at γ i own : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_producers) i η ∗
    match own with
    | Own =>
        oneshot_pending η (DfracOwn 1) ()
    | Discarded =>
        oneshot_shot η ()
    end.

  #[local] Definition consumers_auth' γ_consumers i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_consumers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition consumers_auth γ :=
    consumers_auth' γ.(metadata_consumers).
  #[local] Definition consumers_at γ i own : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_consumers) i η ∗
    match own with
    | Own =>
        oneshot_pending η (DfracOwn 1) ()
    | Discarded =>
        oneshot_shot η ()
    end.

  #[local] Definition winner γ i : iProp Σ :=
    ∃ id prophs,
    wise_prophets_full global_prophet γ.(metadata_prophet_name) i prophs ∗
    ⌜head prophs = Some id⌝ ∗
    identifier_model' id.

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

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ slots front back vs hist lstates pasts prophss,
    inf_array_model γ.(metadata_data) slots ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    front_auth γ front ∗
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
      match lstate with
      | ProducerProducer =>
          winner γ i
      | ProducerConsumer =>
          True
      | ConsumerProducer η =>
          ∃ Ψ v,
          front_lb γ i ∗
          saved_pred η Ψ ∗
          history_at γ i v ∗
          Ψ v ∨ consumers_at γ i Discarded
      | ConsumerConsumer =>
          front_lb γ i
      | _ =>
          False
      end
    ) ∗
    ( [∗ list] k ↦ lstate ∈ drop back lstates,
      match lstate with
      | ConsumerProducer η =>
          ∃ Ψ,
          saved_pred η Ψ ∗
          consumer_au γ Ψ
      | ConsumerConsumer =>
          winner γ (back + k)
      | _ =>
          False
      end
    ) ∗
    ( ∀ i,
      match slots i with
      | Nothing =>
          ⌜pasts i = []⌝
      | Something v =>
          history_at γ i v ∗
          lstates_lb γ i Producer ∗
          producers_at γ i Discarded
      | Anything =>
          lstates_lb γ i Consumer ∗
          consumers_at γ i Discarded
      end
    ).
  Definition inf_mpmc_queue_2_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    inf_array_inv γ.(metadata_data) ∗
    inv ι (inv_inner l γ).

  Definition inf_mpmc_queue_2_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.

  #[global] Instance inf_mpmc_queue_2_model_timeless t vs :
    Timeless (inf_mpmc_queue_2_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance inf_mpmc_queue_2_inv_persistent t ι :
    Persistent (inf_mpmc_queue_2_inv t ι).
  Proof.
    apply _.
  Qed.

  Opaque lstates_auth'.
  Opaque lstates_lb.
  Opaque producers_auth'.
  Opaque producers_at.
  Opaque consumers_auth'.
  Opaque consumers_at.

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
  Admitted.

  Lemma inf_mpmc_queue_2_size_spec t ι :
    <<<
      inf_mpmc_queue_2_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2_model t vs
    >>>
      inf_mpmc_queue_2_size t @ ↑ι
    <<<
      inf_mpmc_queue_2_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
  Admitted.

  Lemma inf_mpmc_queue_2_is_empty_spec t ι :
    <<<
      inf_mpmc_queue_2_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_2_model t vs
    >>>
      inf_mpmc_queue_2_is_empty t @ ↑ι
    <<<
      inf_mpmc_queue_2_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

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
  Admitted.

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
  Admitted.
End inf_mpmc_queue_2_G.

#[global] Opaque inf_mpmc_queue_2_create.
#[global] Opaque inf_mpmc_queue_2_size.
#[global] Opaque inf_mpmc_queue_2_is_empty.
#[global] Opaque inf_mpmc_queue_2_push.
#[global] Opaque inf_mpmc_queue_2_pop.

#[global] Opaque inf_mpmc_queue_2_inv.
#[global] Opaque inf_mpmc_queue_2_model.
