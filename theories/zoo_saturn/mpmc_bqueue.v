From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.auth_nat_max
  lib.twins
  lib.saved_pred.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  typed_prophet.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  xtchain.
From zoo_saturn Require Export
  base
  mpmc_bqueue__code.
From zoo_saturn Require Import
  mpmc_bqueue__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v t : val.
Implicit Types vs : list val.
Implicit Types waiter : gname.
Implicit Types waiters : gmap gname nat.

#[local] Program Definition prophet := {|
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
Solve Obligations of prophet with
  try done.
Next Obligation.
  intros i v _ [= -> ->]. rewrite /= Nat2Z.id //.
Qed.

Class MpmcBqueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_bqueue_G_history_G :: MonoListG Σ location ;
  #[local] mpmc_bqueue_G_front_G :: AuthNatMaxG Σ ;
  #[local] mpmc_bqueue_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] mpmc_bqueue_G_waiters_G :: ghost_mapG Σ gname nat ;
  #[local] mpmc_bqueue_G_saved_pred_G :: SavedPredG Σ bool ;
}.

Definition mpmc_bqueue_Σ := #[
  mono_list_Σ location ;
  auth_nat_max_Σ ;
  twins_Σ (leibnizO (list val)) ;
  ghost_mapΣ gname nat ;
  saved_pred_Σ bool
].
#[global] Instance subG_mpmc_bqueue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_bqueue_Σ Σ →
  MpmcBqueueG Σ.
Proof.
  solve_inG.
Qed.

Section mpmc_bqueue_G.
  Context `{mpmc_bqueue_G : MpmcBqueueG Σ}.

  Implicit Types Ψ : bool → iProp Σ.

  Record metadata := {
    metadata_capacity : nat ;
    metadata_history : gname ;
    metadata_front : gname ;
    metadata_model : gname ;
    metadata_waiters : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition history_auth' γ_history :=
    mono_list_auth γ_history (DfracOwn 1).
  #[local] Definition history_auth γ :=
    history_auth' γ.(metadata_history).
  #[local] Definition history_at γ :=
    mono_list_at γ.(metadata_history).

  #[local] Definition front_auth' γ_front :=
    auth_nat_max_auth γ_front (DfracOwn 1).
  #[local] Definition front_auth γ :=
    front_auth' γ.(metadata_front).
  #[local] Definition front_lb γ :=
    auth_nat_max_lb γ.(metadata_front).

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition waiters_auth' γ_waiters :=
    ghost_map_auth γ_waiters 1.
  #[local] Definition waiters_auth γ :=
    waiters_auth' γ.(metadata_waiters).
  #[local] Definition waiters_at γ waiter :=
    ghost_map_elem γ.(metadata_waiters) waiter (DfracOwn 1).

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
    xtchain (Header §Node 4) (DfracOwn 1) hist §Null ∗
    ( [∗ list] node; v ∈ nodes; vs,
      node.[data] ↦ v
    ) ∗
    ( [∗ list] i ↦ node ∈ hist,
      node.[index] ↦□ #i
    ) ∗
    ( [∗ list] i ↦ node ∈ hist,
      ∃ cap : nat,
      node.[estimated_capacity] ↦ #cap ∗
      ⌜i + cap ≤ length past + γ.(metadata_capacity)⌝
    ) ∗
    history_auth γ hist ∗
    front_auth γ (length past) ∗
    model₂ γ vs ∗
    waiters_auth γ waiters ∗
    ( [∗ map] waiter ↦ i ∈ waiters,
      waiter_model γ ι past waiter i
    ).
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
      >Hindices &
      >Hcapacities &
      >Hhistory_auth &
      >Hfront_auth &
      >Hmodel₂ &
      >Hwaiters_auth &
      Hwaiters
    )".
  Definition mpmc_bqueue_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜cap = γ.(metadata_capacity)⌝ ∗
    meta l nroot γ ∗
    l.[capacity] ↦□ #cap ∗
    inv ι (inv_inner l γ ι).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      #Hmeta &
      #Hl_capacity &
      #Hinv
    )".

  Definition mpmc_bqueue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜length vs ≤ γ.(metadata_capacity)⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      % &
      #Hmeta_ &
      Hmodel₁
    )".

  #[global] Instance mpmc_bqueue_model_timeless t vs :
    Timeless (mpmc_bqueue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_bqueue_inv_persistent t ι cap :
    Persistent (mpmc_bqueue_inv t ι cap).
  Proof.
    apply _.
  Qed.

  #[local] Lemma history_alloc front :
    ⊢ |==>
      ∃ γ_hist,
      history_auth' γ_hist [front].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma history_at_get {γ hist} i node :
    hist !! i = Some node →
    history_auth γ hist ⊢
    history_at γ i node.
  Proof.
    apply mono_list_at_get.
  Qed.
  #[local] Lemma history_agree γ hist i node :
    history_auth γ hist -∗
    history_at γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  #[local] Lemma history_update {γ hist} node :
    history_auth γ hist ⊢ |==>
    history_auth γ (hist ++ [node]).
  Proof.
    apply mono_list_update_snoc.
  Qed.

  #[local] Lemma front_alloc :
    ⊢ |==>
      ∃ γ_front,
      front_auth' γ_front 0.
  Proof.
    apply auth_nat_max_alloc.
  Qed.
  #[local] Lemma front_lb_get γ i :
    front_auth γ i ⊢
    front_lb γ i.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma front_lb_valid γ i1 i2 :
    front_auth γ i1 -∗
    front_lb γ i2 -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.
  #[local] Lemma front_update {γ i} i' :
    i ≤ i' →
    front_auth γ i ⊢ |==>
    front_auth γ i'.
  Proof.
    apply auth_nat_max_update.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twins_alloc'.
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
    apply twins_update'.
  Qed.

  #[local] Lemma waiters_alloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters_auth' γ_waiters ∅.
  Proof.
    iMod ghost_map_alloc as "(%γ_waiters & Hwaiters_auth & _)".
    iSteps.
  Qed.
  #[local] Lemma waiters_lookup γ waiters waiter i :
    waiters_auth γ waiters -∗
    waiters_at γ waiter i -∗
    ⌜waiters !! waiter = Some i⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma waiters_insert {γ waiters} waiter i :
    waiters !! waiter = None →
    waiters_auth γ waiters ⊢ |==>
      waiters_auth γ (<[waiter := i]> waiters) ∗
      waiters_at γ waiter i.
  Proof.
    iIntros "%Hlookup Hwaiters_auth".
    iApply (ghost_map_insert with "Hwaiters_auth"); first done.
  Qed.
  #[local] Lemma waiters_delete γ waiters waiter i :
    waiters_auth γ waiters -∗
    waiters_at γ waiter i ==∗
    waiters_auth γ (delete waiter waiters).
  Proof.
    apply ghost_map_delete.
  Qed.

  Lemma mpmc_bqueue_model_valid t ι cap vs :
    mpmc_bqueue_inv t ι cap -∗
    mpmc_bqueue_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(:inv) (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iSteps.
  Qed.

  Lemma mpmc_bqueue_create_spec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      mpmc_bqueue_create #cap
    {{{ t,
      RET t;
      mpmc_bqueue_inv t ι ₊cap ∗
      mpmc_bqueue_model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.

    wp_block front as "Hfront_header" "_" "(Hfront_next & Hfront_data & Hfront_index & Hfront_capacity & _)".
    iMod (pointsto_persist with "Hfront_index") as "#Hfront_index".
    wp_block l as "Hmeta" "(Hl_capacity & Hl_front & Hl_back & _)".
    iMod (pointsto_persist with "Hl_capacity") as "#Hcapacity".

    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod front_alloc as "(%γ_front & Hfront_auth)".
    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ := {|
      metadata_capacity := ₊cap ;
      metadata_history := γ_history ;
      metadata_front := γ_front ;
      metadata_model := γ_model ;
      metadata_waiters := γ_waiters ;
    |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. rewrite Z2Nat.id //. iStep 4.
    iApply inv_alloc.
    iExists [front], [], front, [], front, [], ∅. iFrameSteps.
    { rewrite elem_of_list_singleton //. }
    rewrite xtchain_singleton. iSteps.
    rewrite big_sepM_empty //.
  Qed.

  Lemma mpmc_bqueue_capacity_spec t ι cap :
    {{{
      mpmc_bqueue_inv t ι cap
    }}}
      mpmc_bqueue_capacity t
    {{{
      RET #cap;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma front_spec_strong au Ψ l γ ι :
    {{{
      inv ι (inv_inner l γ ι) ∗
      if negb au then True else
        waiter_au γ ι Ψ
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      history_at γ i front ∗
      front.[index] ↦□ #i ∗
      front_lb γ i ∗
      if negb au then True else
        ∃ waiter,
        saved_pred waiter Ψ ∗
        waiters_at γ waiter i
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    assert (hist !! length past = Some front) as Hhist_lookup.
    { rewrite Hhist list_lookup_middle //. }
    iDestruct (history_at_get _ front with "Hhistory_auth") as "#Hhistory_at"; first done.
    iDestruct (big_sepL_lookup with "Hindices") as "#Hfront_index"; first done.
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
    destruct au; last iSteps.
    iMod (saved_pred_alloc_cofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & #Hwaiter)".
    rewrite not_elem_of_dom in Hwaiter.
    iMod (waiters_insert _ (length past) with "Hwaiters_auth") as "(Hwaiter_auth & Hwaiters_at)"; first done.
    iDestruct (big_sepM_insert_2 _ _ waiter (length past) with "[HΨ] Hwaiters") as "Hwaiters".
    { iExists Ψ. rewrite decide_False; first lia. iSteps. }
    iSplitR "Hwaiters_at HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec l γ ι :
    {{{
      inv ι (inv_inner l γ ι)
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      history_at γ i front ∗
      front.[index] ↦□ #i ∗
      front_lb γ i
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (front_spec_strong false inhabitant with "[$Hinv]").
    iSteps.
  Qed.

  #[local] Lemma back_spec l γ ι :
    {{{
      inv ι (inv_inner l γ ι)
    }}}
      (#l).{back}
    {{{ back i,
      RET #back;
      history_at γ i back ∗
      back.[index] ↦□ #i
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    pose proof Hback as (i & Hlookup)%elem_of_list_lookup.
    iDestruct (history_at_get with "Hhistory_auth") as "#Hhistory_elem_back"; first done.
    iAssert (back.[index] ↦□ #i)%I as "#Hback_index".
    { rewrite big_sepL_lookup //. }
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma mpmc_bqueue_size_spec t ι cap :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_size t @ ↑ι
    <<<
      mpmc_bqueue_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_bqueue_is_empty_spec t ι cap :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_is_empty t @ ↑ι
    <<<
      mpmc_bqueue_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_bqueue_push_spec t ι cap v :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_push t v @ ↑ι
    <<<
      mpmc_bqueue_model t (if decide (length vs = cap) then vs else vs ++ [v])
    | RET #(bool_decide (length vs = cap));
      True
    >>>.
  Proof.
  Admitted.

  Lemma mpmc_bqueue_pop_spec t ι cap :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_pop t @ ↑ι
    <<<
      mpmc_bqueue_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.
End mpmc_bqueue_G.

#[global] Opaque mpmc_bqueue_create.
#[global] Opaque mpmc_bqueue_capacity.
#[global] Opaque mpmc_bqueue_size.
#[global] Opaque mpmc_bqueue_is_empty.
#[global] Opaque mpmc_bqueue_push.
#[global] Opaque mpmc_bqueue_pop.

#[global] Opaque mpmc_bqueue_inv.
#[global] Opaque mpmc_bqueue_model.
