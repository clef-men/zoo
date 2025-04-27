From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.auth_nat_max
  lib.auth_twins
  lib.saved_pred.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  xtchain
  domain.
From zoo_saturn Require Export
  base
  spmc_queue__code.
From zoo_saturn Require Import
  spmc_queue__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v t : val.
Implicit Types vs ws : list val.

Class SpmcQueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] spmc_queue_G_history_G :: MonoListG Σ location ;
  #[local] spmc_queue_G_front_G :: AuthNatMaxG Σ ;
  #[local] spmc_queue_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix ;
  #[local] spmc_queue_G_waiters_G :: ghost_mapG Σ gname nat ;
  #[local] spmc_queue_G_saved_pred_G :: SavedPredG Σ bool ;
}.

Definition spmc_queue_Σ := #[
  mono_list_Σ location ;
  auth_nat_max_Σ ;
  auth_twins_Σ (leibnizO (list val)) suffix ;
  ghost_mapΣ gname nat ;
  saved_pred_Σ bool
].
#[global] Instance subG_spmc_queue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG spmc_queue_Σ Σ →
  SpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Section spmc_queue_G.
  Context `{spmc_queue_G : SpmcQueueG Σ}.

  Implicit Types Ψ : bool → iProp Σ.

  Record metadata := {
    metadata_history : gname ;
    metadata_front : gname ;
    metadata_model : auth_twins_name ;
    metadata_waiters : gname ;
  }.
  Implicit Type γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn (1/2)) hist.
  #[local] Definition history_auth γ hist :=
    history_auth' γ.(metadata_history) hist.
  #[local] Definition history_last' γ_history node : iProp Σ :=
    ∃ hist,
    mono_list_auth γ_history (DfracOwn (1/2)) hist ∗
    ⌜last hist = Some node⌝.
  #[local] Instance : CustomIpatFormat "history_last" :=
    "(
      %hist{} &
      Hauth{_{}} &
      %Hlast
    )".
  #[local] Definition history_last γ :=
    history_last' γ.(metadata_history).
  #[local] Definition history_at γ i node :=
    mono_list_at γ.(metadata_history) i node.

  #[local] Definition front_auth' γ_front i :=
    auth_nat_max_auth γ_front (DfracOwn 1) i.
  #[local] Definition front_auth γ i :=
    front_auth' γ.(metadata_front) i.
  #[local] Definition front_lb γ i :=
    auth_nat_max_lb γ.(metadata_front) i.

  #[local] Definition model₁' γ_model vs :=
    auth_twins_twin1 _ γ_model vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    auth_twins_twin2 _ γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition producer' γ_model ws :=
    auth_twins_auth _ γ_model ws.
  #[local] Definition producer γ :=
    producer' γ.(metadata_model).

  #[local] Definition waiters_auth' γ_waiters waiters :=
    ghost_map_auth γ_waiters 1 waiters.
  #[local] Definition waiters_auth γ waiters :=
    waiters_auth' γ.(metadata_waiters) waiters.
  #[local] Definition waiters_at γ waiter i :=
    ghost_map_elem γ.(metadata_waiters) waiter (DfracOwn 1) i.

  #[local] Definition waiter_au γ ι Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      model₁ γ vs
    , COMM
      Ψ (bool_decide (vs = []))
    }>.
  #[local] Definition waiter_model γ ι past waiter i : iProp Σ :=
    ∃ Ψ,
    saved_pred waiter Ψ ∗
    if decide (i < length past) then
      Ψ false
    else
      waiter_au γ ι Ψ.

  #[local] Definition inv_inner l γ ι : iProp Σ :=
    ∃ hist past front nodes back vs waiters,
    ⌜hist = past ++ front :: nodes⌝ ∗
    ⌜back ∈ hist⌝ ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
    ([∗ list] node; v ∈ nodes; vs, node.[xtchain_data] ↦ v) ∗
    history_auth γ hist ∗
    front_auth γ (length past) ∗
    model₂ γ vs ∗
    waiters_auth γ waiters ∗
    ([∗ map] waiter ↦ i ∈ waiters, waiter_model γ ι past waiter i).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %hist{} &
      %past{} &
      %front{} &
      %nodes{} &
      %back{} &
      %vs{} &
      %waiters{} &
      >%Hhist{} &
      >%Hback{} &
      >Hl_front &
      >Hl_back &
      >Hhist &
      >Hnodes &
      >Hhistory_auth &
      >Hfront_auth &
      >Hmodel₂ &
      >Hwaiters_auth &
      Hwaiters
    )".
  Definition spmc_queue_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (inv_inner l γ ι).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition spmc_queue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      #Hmeta_ &
      Hmodel₁
    )".

  Definition spmc_queue_producer t ws : iProp Σ :=
    ∃ l γ back,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[back] ↦ #back ∗
    history_last γ back ∗
    producer γ ws.
  #[local] Instance : CustomIpatFormat "producer" :=
    "(
      %l{{}=_} &
      %γ{{}=_} &
      %Heq{} &
      #Hmeta_{} &
      Hmodel₁{}
    )".

  #[global] Instance spmc_queue_model_timeless t vs :
    Timeless (spmc_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_queue_producer_timeless t ws :
    Timeless (spmc_queue_producer t ws).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_queue_inv_persistent t ι :
    Persistent (spmc_queue_inv t ι).
  Proof.
    apply _.
  Qed.

  Opaque history_last'.

  Lemma spmc_queue_producer_valid t vs ws :
    spmc_queue_model t vs -∗
    spmc_queue_producer t ws -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
  Admitted.
  Lemma spmc_queue_producer_exclusive t ws1 ws2 :
    spmc_queue_producer t ws1 -∗
    spmc_queue_producer t ws2 -∗
    False.
  Proof.
  Admitted.

  Lemma spmc_queue_create_spec ι :
    {{{
      True
    }}}
      spmc_queue_create ()
    {{{ t,
      RET t;
      spmc_queue_inv t ι ∗
      spmc_queue_model t [] ∗
      spmc_queue_producer t []
    }}}.
  Proof.
  Admitted.

  Lemma spmc_queue_is_empty_spec t ι :
    <<<
      spmc_queue_inv t ι
    | ∀∀ vs,
      spmc_queue_model t vs
    >>>
      spmc_queue_is_empty t @ ↑ι
    <<<
      spmc_queue_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

  Lemma spmc_queue_push_spec t ι ws v :
    <<<
      spmc_queue_inv t ι ∗
      spmc_queue_producer t ws
    | ∀∀ vs,
      spmc_queue_model t vs
    >>>
      spmc_queue_push t v @ ↑ι
    <<<
      spmc_queue_model t (vs ++ [v])
    | RET ();
      spmc_queue_producer t (vs ++ [v])
    >>>.
  Proof.
  Admitted.

  Lemma spmc_queue_pop_spec t ι :
    <<<
      spmc_queue_inv t ι
    | ∀∀ vs,
      spmc_queue_model t vs
    >>>
      spmc_queue_pop t @ ↑ι
    <<<
      spmc_queue_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End spmc_queue_G.

#[global] Opaque spmc_queue_create.
#[global] Opaque spmc_queue_is_empty.
#[global] Opaque spmc_queue_push.
#[global] Opaque spmc_queue_pop.

#[global] Opaque spmc_queue_inv.
#[global] Opaque spmc_queue_model.
#[global] Opaque spmc_queue_producer.
