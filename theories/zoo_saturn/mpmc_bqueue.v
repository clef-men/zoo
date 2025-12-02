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
  lib.twins
  lib.saved_pred.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  prophet_typed.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  domain
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
  prophet_typed_strong_1_type :=
    location ;
  prophet_typed_strong_1_of_val v _ :=
    match v with
    | ValLoc l =>
        Some l
    | _ =>
        None
    end ;
  prophet_typed_strong_1_to_val l :=
    (#l, ()%V) ;
|}.
Solve Obligations of prophet with
  try done.
Next Obligation.
  naive_solver.
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

  Record metadata := {
    metadata_inv : namespace ;
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

  #[local] Definition node_model γ node (i : nat) b : iProp Σ :=
    node ↦ₕ Header §Node 4 ∗
    node.[index] ↦□ #i ∗
    history_at γ i node ∗
    if b then front_lb γ i else True%I.
  #[local] Instance : CustomIpatFormat "node_model" :=
    " ( #H{}_header &
        #H{}_index &
        #Hhistory_at_{} &
        {{front}#Hfront_lb_{};_}
      )
    ".

  #[local] Definition waiter_au γ (Ψ : bool → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      model₁ γ vs
    , COMM
      Ψ (bool_decide (vs = []))
    }>.
  #[local] Definition waiter_model γ past waiter i : iProp Σ :=
    ∃ Ψ,
    saved_pred waiter Ψ ∗
    if decide (i < length past) then
      Ψ false
    else
      waiter_au γ Ψ.

  #[local] Definition inv_inner l γ : iProp Σ :=
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
      waiter_model γ past waiter i
    ).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    " ( %hist{} &
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
      )
    ".
  #[local] Definition inv' l γ :=
    inv γ.(metadata_inv) (inv_inner l γ).
  Definition mpmc_bqueue_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    ⌜cap = γ.(metadata_capacity)⌝ ∗
    meta l nroot γ ∗
    l.[capacity] ↦□ #cap ∗
    inv' l γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %l &
        %γ &
        -> &
        -> &
        -> &
        #Hmeta &
        #Hl_capacity &
        #Hinv
      )
    ".

  Definition mpmc_bqueue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜length vs ≤ γ.(metadata_capacity)⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    " ( %l{;_} &
        %γ{;_} &
        %Heq{} &
        % &
        #Hmeta_{} &
        Hmodel₁{_{}}
      )
    ".

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
      ∃ γ_history,
      history_auth' γ_history [front].
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
  #[local] Lemma history_at_agree γ i node1 node2 :
    history_at γ i node1 -∗
    history_at γ i node2 -∗
    ⌜node1 = node2⌝.
  Proof.
    apply mono_list_at_agree.
  Qed.
  #[local] Lemma history_at_lookup γ hist i node :
    history_auth γ hist -∗
    history_at γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  #[local] Lemma history_at_elem_of γ hist i node :
    history_auth γ hist -∗
    history_at γ i node -∗
    ⌜node ∈ hist⌝.
  Proof.
    iIntros "Hauth Hat".
    iDestruct (history_at_lookup with "Hauth Hat") as %?%list_elem_of_lookup_2.
    iSteps.
  Qed.
  #[local] Lemma history_update {γ hist} node :
    history_auth γ hist ⊢ |==>
      history_auth γ (hist ++ [node]) ∗
      history_at γ (length hist) node.
  Proof.
    iIntros "Hauth".
    iMod (mono_list_update_snoc with "Hauth") as "Hauth".
    iDestruct (history_at_get with "Hauth") as "#Hat".
    { rewrite lookup_snoc_Some. naive_solver. }
    iSteps.
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

  #[local] Lemma waiters_alloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters_auth' γ_waiters ∅.
  Proof.
    iMod ghost_map_alloc as "(%γ_waiters & Hwaiters_auth & _)".
    iSteps.
  Qed.
  #[local] Lemma waiters_insert {γ waiters} i Ψ :
    waiters_auth γ waiters ⊢ |==>
      ∃ waiter,
      waiters_auth γ (<[waiter := i]> waiters) ∗
      saved_pred waiter Ψ ∗
      waiters_at γ waiter i.
  Proof.
    iIntros "Hwaiters_auth".
    iMod (saved_pred_alloc_cofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & $)".
    rewrite not_elem_of_dom in Hwaiter.
    iApply (ghost_map_insert with "Hwaiters_auth"); first done.
  Qed.
  #[local] Lemma waiters_delete γ waiters waiter i :
    waiters_auth γ waiters -∗
    waiters_at γ waiter i ==∗
      ⌜waiters !! waiter = Some i⌝ ∗
      waiters_auth γ (delete waiter waiters).
  Proof.
    iIntros "Hwaiters_auth Hwaiters_at".
    iDestruct (ghost_map_lookup with "Hwaiters_auth Hwaiters_at") as %?.
    iMod (ghost_map_delete with "Hwaiters_auth Hwaiters_at") as "$".
    iSteps.
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
  Lemma mpmc_bqueue_model_exclusive t vs1 vs2 :
    mpmc_bqueue_model t vs1 -∗
    mpmc_bqueue_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
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
      metadata_inv := ι ;
      metadata_capacity := ₊cap ;
      metadata_history := γ_history ;
      metadata_front := γ_front ;
      metadata_model := γ_model ;
      metadata_waiters := γ_waiters ;
    |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. rewrite Z2Nat.id //. iStep 5.
    iApply inv_alloc.
    iExists [front], [], front, [], front, [], ∅. iFrameSteps.
    - rewrite list_elem_of_singleton //.
    - rewrite xtchain_singleton big_sepM_empty. iSteps.
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

  #[local] Lemma front_spec_strong Ψ l γ :
    {{{
      inv' l γ ∗
      if Ψ is Some Ψ then
        waiter_au γ Ψ
      else
        True
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      node_model γ front i true ∗
      if Ψ is Some Ψ then
        ∃ waiter,
        saved_pred waiter Ψ ∗
        waiters_at γ waiter i
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    assert (hist !! (length past) = Some front) as Hlookup.
    { rewrite Hhist list_lookup_middle //. }
    iDestruct (xtchain_lookup_header with "Hhist") as "#Hfront_header"; first done.
    iDestruct (big_sepL_lookup with "Hindices") as "#Hfront_index"; first done.
    iDestruct (history_at_get _ front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_front".
    destruct Ψ as [Ψ |]; last iSteps.
    iMod (waiters_insert (length past) Ψ with "Hwaiters_auth") as "(%waiter & Hwaiter_auth & #Hwaiter & Hwaiters_at)".
    iDestruct (big_sepM_insert_2 _ _ waiter (length past) with "[HΨ] Hwaiters") as "Hwaiters".
    { iExists Ψ. rewrite decide_False; first lia. iSteps. }
    iSplitR "Hwaiters_at HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  #[local] Lemma front_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      node_model γ front i true
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (front_spec_strong None with "[$Hinv]").
    iSteps.
  Qed.

  #[local] Lemma back_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{back}
    {{{ back i,
      RET #back;
      node_model γ back i false
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    pose proof Hback as (i & Hlookup)%list_elem_of_lookup.
    iDestruct (xtchain_lookup_header with "Hhist") as "#Hback_header"; first done.
    iDestruct (big_sepL_lookup with "Hindices") as "#Hback_index"; first done.
    iDestruct (history_at_get with "Hhistory_auth") as "#Hhistory_at_back"; first done.
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Inductive operation :=
    | Size (i_front : nat) (Ψ : val → iProp Σ)
    | IsEmpty waiter (Ψ : bool → iProp Σ)
    | Pop (Ψ : option val → iProp Σ)
    | Other.
  Implicit Types op : operation.
  Inductive operation' :=
    | Size'
    | IsEmpty'
    | Pop'
    | Other'.
  #[local] Instance operation'_eq_dec : EqDecision operation' :=
    ltac:(solve_decision).
  #[local] Coercion operation_to_operation' op :=
    match op with
    | Size _ _ =>
        Size'
    | IsEmpty _ _ =>
        IsEmpty'
    | Pop _ =>
        Pop'
    | Other =>
        Other'
    end.
  #[local] Definition size_au l γ Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      mpmc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      mpmc_bqueue_model #l vs
    , COMM
      True -∗ Ψ #(length vs)
    }>.
  #[local] Definition pop_au γ (Ψ : option val → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      model₁ γ (tail vs)
    , COMM
      True -∗ Ψ (head vs)
    }>.
  #[local] Lemma next_spec_aux (next : option location) op l γ i node :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      from_option (history_at γ (S i)) True next ∗
      match op with
      | Size i_front Ψ =>
          front_lb γ i_front ∗
          size_au l γ Ψ
      | IsEmpty waiter Ψ =>
          front_lb γ i ∗
          saved_pred waiter Ψ ∗
          waiters_at γ waiter i ∗
          £ 1
      | Pop Ψ =>
          front_lb γ i ∗
          pop_au γ Ψ
      | Other =>
          True
      end
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝ ∗
        from_option (const False) True next ∗
        match op with
        | Size i_front Ψ =>
              Ψ #(i - i_front)
            ∨ ∃ i_front',
              front_lb γ i_front' ∗
              ⌜i_front < i_front'⌝ ∗
              size_au l γ Ψ
        | IsEmpty waiter Ψ =>
            Ψ true
        | Pop Ψ =>
            Ψ None
        | _ =>
            True
        end
     ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        ⌜from_option (node' =.) True next⌝ ∗
        match op with
        | Size _ Ψ =>
            size_au l γ Ψ
        | IsEmpty waiter Ψ =>
            Ψ false
        | Pop Ψ =>
            pop_au γ Ψ
        | Other =>
            True
        end
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & #Hhistory_at_next & Hop) HΦ".

    iInv "Hinv" as "(:inv_inner)".
    iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
    iDestruct (xtchain_lookup_acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
    wp_load.
    iDestruct ("Hhist" with "Hnode") as "Hhist".
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (xtchain_lookup_header with "Hhist") as "#Hnode'_header"; first done.
      iDestruct (big_sepL_lookup with "Hindices") as "#Hnode'_index"; first done.
      iDestruct (history_at_get (S i) with "Hhistory_auth") as "#Hhistory_at_node'"; first done.

      iAssert ⌜from_option (node' =.) True next⌝%I as %?.
      { destruct next as [next |]; last done.
        iApply (history_at_agree with "Hhistory_at_node' Hhistory_at_next").
      }

      destruct op. 1,3,4: iSteps.
      iDestruct "Hop" as "(#Hfront_lb_node & #Hwaiter & Hwaiters_at & H£)".
      iMod (waiters_delete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
      iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
      iDestruct (saved_pred_agree false with "Hwaiter Hwaiter_") as "Heq".
      iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
      destruct_decide (i = length past) as -> | Hi.

      + rewrite decide_False; first lia.

        iMod "HΨ" as "(%vs_ & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".
        assert (nodes ≠ []) as Hnodes.
        { apply lookup_lt_Some in Hlookup'.
          rewrite Hhist length_app /= in Hlookup'.
          naive_solver lia.
        }
        iAssert ⌜vs ≠ []⌝%I as %Hvs.
        { destruct_decide (vs = []) as -> | ?; last done.
          iDestruct (big_sepL2_length with "Hnodes") as %->%nil_length_inv.
          iSteps.
        }
        rewrite bool_decide_eq_false_2 //.

        iSplitR "Heq HΨ HΦ". { iFrameSteps. }
        iSteps. iRewrite "Heq". iSteps.

      + iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi_.
        rewrite decide_True; first lia.
        iSplitR "Heq HΨ HΦ". { iFrameSteps. }
        iSteps. iRewrite "Heq". iSteps.

    - destruct next as [next |].
      { iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_next") as %?. congruence. }

      destruct op as [i_front | | |].

      + iDestruct "Hop" as "(#Hfront_lb_front & HΨ)".
        destruct_decide (length past = i_front).

        * iMod "HΨ" as "(%vs_ & (:model) & _ & HΨ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "[Hmodel₁] [//]") as "HΨ"; first iSteps.
          assert ((i - i_front)%Z = length nodes) as ->.
          { opose proof* length_lookup_last as Hlength; [done.. |].
            rewrite Hhist length_app /= in Hlength.
            lia.
          }
          iDestruct (big_sepL2_length with "Hnodes") as %->.

          iSplitR "HΨ HΦ". { iFrameSteps. }
          iSteps.

        * iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_front") as %?. iClear "Hfront_lb_front".
          iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_front".
          iSplitR "HΨ HΦ". { iFrameSteps. }
          iSteps.

      + iDestruct "Hop" as "(#Hfront_lb_node & #Hwaiter & Hwaiters_at & H£)".
        iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi.
        opose proof* length_lookup_last as Hlength; [done.. |].
        rewrite Hhist length_app /= in Hlength.
        assert (i = length past) as -> by lia.
        assert (length nodes = 0) as ->%nil_length_inv by lia.
        iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
        iMod (waiters_delete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
        iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
        iDestruct (saved_pred_agree true with "Hwaiter Hwaiter_") as "Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        rewrite decide_False; first lia.

        iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iSplitR "Heq HΨ HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        iApply "HΦ".
        iLeft. iRewrite "Heq". iSteps.

      + iDestruct "Hop" as "(#Hfront_lb_node & HΨ)".
        iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi.
        opose proof* length_lookup_last as Hlength; [done.. |].
        rewrite Hhist length_app /= in Hlength.
        assert (i = length past) as -> by lia.
        assert (length nodes = 0) as ->%nil_length_inv by lia.
        iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.

        iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iSplitR "HΨ HΦ". { iFrameSteps. }
        iSteps.

      + iSteps.
  Qed.
  #[local] Lemma next_spec {l γ i} node :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node) HΦ".
    wp_apply (next_spec_aux None Other); iSteps.
  Qed.
  #[local] Lemma next_spec' {l γ i} node next :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      history_at γ (S i) next
    }}}
      (#node).{next}
    {{{
      RET #next;
      node_model γ next (S i) false
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & #Hhistory_at_next) HΦ".
    wp_apply (next_spec_aux (Some next) Other); iSteps.
  Qed.
  #[local] Lemma next_spec_size {l γ i node} i_front Ψ :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      front_lb γ i_front ∗
      size_au l γ Ψ
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝ ∗
        ( Ψ #(i - i_front)
        ∨ ∃ i_front',
          front_lb γ i_front' ∗
          ⌜i_front < i_front'⌝ ∗
          size_au l γ Ψ
        )
     ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        size_au l γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & #Hfront_lb_front & HΨ) HΦ".
    wp_apply (next_spec_aux None (Size _ _) with "[$]").
    iSteps.
  Qed.
  #[local] Lemma next_spec_is_empty {l γ i node} waiter Ψ :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      front_lb γ i ∗
      saved_pred waiter Ψ ∗
      waiters_at γ waiter i ∗
      £ 1
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝ ∗
        Ψ true
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & #Hfront_lb_node & #Hwaiter & Hwaiters_at & H£) HΦ".
    wp_apply (next_spec_aux None (IsEmpty _ _) with "[$]").
    iSteps.
  Qed.
  #[local] Lemma next_spec_pop {l γ i node} Ψ :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      front_lb γ i ∗
      pop_au γ Ψ
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝ ∗
        Ψ None
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        pop_au γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & #Hfront_lb_node & HΨ) HΦ".
    wp_apply (next_spec_aux None (Pop _) with "[$]").
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
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_apply (front_spec with "Hinv") as (front1 i_front1) "(:node_model =front1 front=)".
    wp_match.
    wp_smart_apply (prophet_typed_strong_1_wp_proph prophet with "[//]") as (pid proph) "Hproph".
    wp_smart_apply (back_spec with "Hinv") as (back2 i_back2) "(:node_model =back2)".
    wp_match. wp_pures.
    destruct_decide (proph = front1) as -> | Hproph.

    - wp_apply (next_spec_size with "[$]") as (res) "[(-> & HΦ) | (%node & -> & (:node_model =node) & HΦ)]".

      + wp_pures.

        wp_bind (Resolve _ _ _).
        iInv "Hinv" as "(:inv_inner =3)".
        wp_apply (prophet_typed_strong_1_wp_resolve with "Hproph"); first done.
        wp_load.
        iStep. iIntros "<-".
        iDestruct "HΦ" as "[HΦ | (%i_front2 & #Hfront_lb_front2 & % & HΦ)]"; last first.
        { assert (hist3 !! (length past3) = Some front1) as Hlookup.
          { rewrite Hhist3 list_lookup_middle //. }
          iDestruct (big_sepL_lookup with "Hindices") as "#Hfront1_index_"; first done.
          iDestruct (pointsto_agree with "Hfront1_index Hfront1_index_") as %[= ?%(inj _)].
          iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_front2") as %?.
          lia.
        }
        iSteps.

      + wp_match. wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =3)".
        wp_apply (wp_cas_nobranch' with "Hl_back") as (b) "% Hl_back".
        iSplitR "HΦ".
        { iDestruct (history_at_elem_of with "Hhistory_auth Hhistory_at_node") as %Hnode.
          destruct b; iFrameSteps.
        }
        iSteps.

    - wp_apply (next_spec with "[$]") as (res) "[-> | (%node & -> & (:node_model =node))]".

      + wp_pures.

        wp_bind (Resolve _ _ _).
        iInv "Hinv" as "(:inv_inner =3)".
        wp_apply (prophet_typed_strong_1_wp_resolve with "Hproph"); first done.
        iSteps.

      + wp_match. wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =3)".
        wp_apply (wp_cas_nobranch' with "Hl_back") as (b) "% Hl_back".
        iSplitR "HΦ".
        { iDestruct (history_at_elem_of with "Hhistory_auth Hhistory_at_node") as %Hnode.
          destruct b; iFrameSteps.
        }
        iSteps.
  Qed.

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
    iIntros "%Φ (:inv) HΦ".

    wp_rec credit:"H£".
    wp_smart_apply (front_spec_strong (Some $ λ b, Φ #b) with "[$Hinv HΦ]") as (node i) "((:node_model =node front=) & %waiter & #Hwaiter & Hwaiters_at)".
    { rewrite /= /waiter_au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hmodel₁"; iSteps.
    }
    wp_match.
    wp_smart_apply (next_spec_is_empty with "[$]"); iSteps.
  Qed.

  #[local] Lemma mpmc_bqueue_fix_back_spec {l γ} i {back} j new_back :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i back ∗
      node_model γ new_back j false
    }}}
      mpmc_bqueue_fix_back #l #back #new_back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_back & (:node_model =new_back)) HΦ".

    iLöb as "HLöb" forall (i back) "Hhistory_at_back".

    wp_rec. wp_match.

    wp_bind (_ and _)%E.
    wp_apply (wp_wand itype_bool) as (res) "(%b & ->)".
    { wp_smart_apply (next_spec new_back with "[$]") as (res) "[-> | (%new_back' & -> & (:node_model =new_back'))]"; last iSteps.
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =1)".
      wp_cas as _ | [= ->]; first iSteps.
      iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_new_back") as %Hnew_back%list_elem_of_lookup_2.
      iSteps.
    }

    destruct b; last iSteps.
    wp_smart_apply domain_yield_spec.
    wp_smart_apply (back_spec with "Hinv") as (back' i') "(:node_model =back')".
    iApply ("HLöb" with "HΦ Hhistory_at_back'").
  Qed.

  #[local] Lemma mpmc_bqueue_push_1_push_2_spec l γ new_back v :
    ⊢ (
      ∀ back i_back i_front (cap : Z),
      <<<
        meta l nroot γ ∗
        l.[capacity] ↦□ #γ.(metadata_capacity) ∗
        inv' l γ ∗
        node_model γ back i_back false ∗
        front_lb γ i_front ∗
        ⌜0 ≤ cap⌝%Z ∗
        ⌜i_back + cap ≤ i_front + γ.(metadata_capacity)⌝%Z ∗
        new_back ↦ₕ Header §Node 4 ∗
        new_back.[next] ↦ §Null ∗
        new_back.[data] ↦ v ∗
        new_back.[index] ↦- ∗
        new_back.[estimated_capacity] ↦-
      | ∀∀ vs,
        ⌜length vs ≤ γ.(metadata_capacity)⌝ ∗
        model₁ γ vs
      >>>
        mpmc_bqueue_push_1 #l #back #cap #new_back @ ↑γ.(metadata_inv)
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < γ.(metadata_capacity))⌝ ∗
        model₁ γ (if b then vs ++ [v] else vs)
      | RET #b;
        True
      >>>
    ) ∧ (
      ∀ back i_back,
      <<<
        meta l nroot γ ∗
        l.[capacity] ↦□ #γ.(metadata_capacity) ∗
        inv' l γ ∗
        node_model γ back i_back false ∗
        new_back ↦ₕ Header §Node 4 ∗
        new_back.[next] ↦ §Null ∗
        new_back.[data] ↦ v ∗
        new_back.[index] ↦- ∗
        new_back.[estimated_capacity] ↦-
      | ∀∀ vs,
        ⌜length vs ≤ γ.(metadata_capacity)⌝ ∗
        model₁ γ vs
      >>>
        mpmc_bqueue_push_2 #l #back #new_back @ ↑γ.(metadata_inv)
      <<<
        ∃∃ b,
        ⌜b = bool_decide (length vs < γ.(metadata_capacity))⌝ ∗
        model₁ γ (if b then vs ++ [v] else vs)
      | RET #b;
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHpush_1 & IHpush_2)".
    iSplit.

    { iIntros "%back %i_back %i_front %cap %Φ (#Hmeta & #Hl_capacity & #Hinv & (:node_model =back) & #Hfront_lb_front & % & % & #Hnew_back_header & Hnew_back_next & Hnew_back_data & (% & Hnew_back_index) & (% & Hnew_back_estimated_capacity)) HΦ".

      wp_rec. do 2 wp_match. wp_pures.
      case_bool_decide; wp_pures.

      - wp_bind (_.{front})%E.
        iInv "Hinv" as "(:inv_inner =1)".
        wp_load.
        assert (hist1 !! (length past1) = Some front1) as Hlookup.
        { rewrite Hhist1 list_lookup_middle //. }
        iDestruct (xtchain_lookup_header with "Hhist") as "#Hfront1_header"; first done.
        iDestruct (big_sepL_lookup with "Hindices") as "#Hfront1_index"; first done.

        destruct_decide (i_back < length past1 + γ.(metadata_capacity)) as Hnotfull | Hfull.

        + iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_front1".
          iSplitR "Hnew_back_next Hnew_back_data Hnew_back_index Hnew_back_estimated_capacity HΦ". { iFrameSteps. }
          remember (length past1) as i_front1.
          iModIntro. clear- Hnotfull.

          wp_match. do 3 wp_load. wp_pures.
          rewrite bool_decide_eq_false_2; first lia.
          wp_pures.

          wp_bind (_ <-{estimated_capacity} _)%E.
          iInv "Hinv" as "(:inv_inner =2)".
          iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_back") as %Hlookup.
          iDestruct (big_sepL_lookup_acc with "Hcapacities") as "((%cap2 & Hback_estimated_capacity & _) & Hcapacities)"; first done.
          wp_store.
          iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_front1") as %?.
          iDestruct ("Hcapacities" with "[Hback_estimated_capacity]") as "Hcapacities"; first iSteps.
          iSplitR "Hnew_back_next Hnew_back_data Hnew_back_index Hnew_back_estimated_capacity HΦ". { iFrameSteps. }
          iSteps.

        + iMod "HΦ" as "(%vs & (%Hvs & Hmodel₁) & _ & HΦ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
          iAssert ⌜
            length vs = γ.(metadata_capacity) ∧
            (⁺γ.(metadata_capacity) - (⁺i_back - ⁺(length past1)) = 0)%Z
          ⌝%I as "(-> & %Hif)".
          { iDestruct (big_sepL2_length with "Hnodes") as %?.
            iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_back") as %?%lookup_lt_Some.
            iPureIntro.
            apply (f_equal length) in Hhist1. simpl_length/= in Hhist1.
            lia.
          }
          rewrite bool_decide_eq_false_2; first lia.
          iMod ("HΦ" $! false with "[$Hmodel₁ //] [//]") as "HΦ".

          iSplitR "Hnew_back_next Hnew_back_data Hnew_back_index Hnew_back_estimated_capacity HΦ". { iFrameSteps. }
          iModIntro. clear- Hif.

          wp_match. do 3 wp_load. wp_pures.
          iEval (rewrite bool_decide_eq_true_2 //).
          iSteps.

      - wp_load. do 2 wp_store. wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =1)".
        iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_back") as %Hlookup_back.
        iDestruct (xtchain_lookup with "Hhist") as "(Hhist1 & _ & Hback & Hhist2)"; first done.
        destruct (hist1 !! (S i_back)) as [next |] eqn:Hlookup_next; simpl.

        + wp_cas as _ | [=].
          iDestruct (history_at_get (S i_back) with "Hhistory_auth") as "#Hhistory_at_next"; first done.
          iDestruct (xtchain_lookup_2 with "Hhist1 Hback_header Hback Hhist2") as "Hhist"; [done | rewrite Hlookup_next // |].
          iSplitR "Hnew_back_next Hnew_back_data Hnew_back_index Hnew_back_estimated_capacity HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          iDestruct "Hhistory_at_next" as "-#Hhistory_at_next".
          wp_smart_apply (next_spec' back next with "[$]") as "(:node_model =next)".
          iSteps.

        + wp_cas as ? | _; first done.
          opose proof* length_lookup_last as Hlength; [done.. |].
          iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_front") as %?.

          iMod "HΦ" as "(%vs & (_ & Hmodel₁) & _ & HΦ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
          iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iDestruct (big_sepL2_length with "Hnodes") as %<-.
          assert (length nodes1 < γ.(metadata_capacity)).
          { rewrite Hhist1 length_app /= in Hlength. lia. }
          iEval (rewrite bool_decide_eq_true_2 //) in "HΦ".
          iMod ("HΦ" $! true with "[$Hmodel₁ //] [//]") as "HΦ".

          iDestruct (xtchain_lookup_2 with "Hhist1 Hback_header Hback []") as "Hhist"; [done | rewrite Hlookup_next // | ..].
          { rewrite -Hlength // drop_all -xtchain_nil //. }
          iDestruct (xtchain_snoc_2 with "Hhist Hnew_back_header Hnew_back_next") as "Hhist".
          iDestruct (big_sepL2_snoc_2 with "Hnodes Hnew_back_data") as "Hnodes".
          iMod (pointsto_persist with "Hnew_back_index") as "#Hnew_back_index".
          iDestruct (big_sepL_snoc_2 new_back with "Hindices []") as "Hindices".
          { rewrite Hlength Nat2Z.inj_succ //. }
          iDestruct (big_sepL_snoc_2 new_back with "Hcapacities [Hnew_back_estimated_capacity]") as "Hcapacities"; first iSteps.
          iMod (history_update new_back with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at_new_back)". rewrite Hlength.
          iSplitR "HΦ".
          { iFrameSteps; iPureIntro.
            - rewrite Hhist1 -assoc //.
            - set_solver.
          }
          iIntros "!> {%}".

          wp_smart_apply mpmc_bqueue_fix_back_spec.
          { iFrame "#". iSteps. }
          iSteps.
    }

    { iClear "IHpush_2".

      iIntros "%back %i_back %Φ (#Hmeta & #Hl_capacity & #Hinv & (:node_model =back) & #Hnew_back_header & Hnew_back_next & Hnext_back_data & Hnew_back_index & Hnew_back_estimated_capacity) HΦ".

      wp_rec. wp_match. wp_pures.

      wp_bind (_.{estimated_capacity})%E.
      wp_apply (wp_frame_wand with "[- HΦ]"); first iAccu.
      iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_back") as %Hhist1_lookup.
      iDestruct (big_sepL_lookup_acc with "Hcapacities") as "((%cap & Hback_estimated_capacity & %Hcap) & Hcapacities)"; first done.
      wp_load.
      iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb".
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
    }
  Qed.
  #[local] Lemma mpmc_bqueue_push_2_spec l γ back i_back new_back v :
    <<<
      meta l nroot γ ∗
      l.[capacity] ↦□ #γ.(metadata_capacity) ∗
      inv' l γ ∗
      node_model γ back i_back false ∗
      new_back ↦ₕ Header §Node 4 ∗
      new_back.[next] ↦ §Null ∗
      new_back.[data] ↦ v ∗
      new_back.[index] ↦- ∗
      new_back.[estimated_capacity] ↦-
    | ∀∀ vs,
      ⌜length vs ≤ γ.(metadata_capacity)⌝ ∗
      model₁ γ vs
    >>>
      mpmc_bqueue_push_2 #l #back #new_back @ ↑γ.(metadata_inv)
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < γ.(metadata_capacity))⌝ ∗
      model₁ γ (if b then vs ++ [v] else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iDestruct mpmc_bqueue_push_1_push_2_spec as "(_ & H)".
    iApply "H".
  Qed.
  Lemma mpmc_bqueue_push_spec t ι cap v :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_push t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (length vs < cap)⌝ ∗
      mpmc_bqueue_model t (if b then vs ++ [v] else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & Hnew_back_index & Hnew_back_estimated_capacity & _)".
    wp_smart_apply (back_spec with "Hinv") as (back i_back) "(:node_model =back)".

    awp_apply (mpmc_bqueue_push_2_spec with "[$]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    rewrite /atomic_acc /=.
    iStep. iSplitR; first iSteps. iIntros "!> %b (-> & $)". iSteps. iPureIntro.
    case_bool_decide; simpl_length/=; lia.
  Qed.

  #[local] Lemma mpmc_bqueue_pop_spec_aux l γ :
    <<<
      meta l nroot γ ∗
      inv' l γ
    | ∀∀ vs,
      model₁ γ vs
    >>>
      mpmc_bqueue_pop #l @ ↑γ.(metadata_inv)
    <<<
      model₁ γ (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (front_spec with "Hinv") as (front i) "(:node_model =front front=)".
    wp_match.
    wp_smart_apply (next_spec_pop Φ with "[$]") as (res) "[(-> & HΦ) | (%new_front & -> & (:node_model =new_front) & HΦ)]"; first iSteps.
    wp_match. wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_new_front") as %Hlookup.
    iDestruct (xtchain_lookup_acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
    wp_cas as _ | [= <-]; first iSteps.
    iDestruct ("Hhist" with "Hnode") as "Hhist".
    iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_front") as %Hlookup_old.
    iAssert ⌜length past1 = i⌝%I as %Hpast_length.
    { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
      iPureIntro. eapply NoDup_lookup; try done.
      rewrite Hhist1 list_lookup_middle //.
    }
    rewrite Hhist1 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup; first lia.
    rewrite Nat.add_1_r Hpast_length Nat.sub_diag in Hlookup.
    destruct nodes1 as [| node nodes1]; first done. injection Hlookup as ->.
    rewrite (assoc _ _ [_]) in Hhist1.
    iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hfront_data & Hnodes)".
    set past := past1 ++ [front].
    iMod (front_update (length past) with "Hfront_auth") as "Hfront_auth".
    { rewrite /past. simpl_length. lia. }
    iDestruct (big_sepM_impl_thread_fupd _ (waiter_model γ past)%I with "Hwaiters Hmodel₂ [#]") as ">(Hwaiters & Hmodel₂)".
    { iIntros "!> %waiter %j %Hlookup (%P & #Hwaiter & HP) Hmodel₂".
      destruct (Nat.lt_trichotomy j (length past1)) as [Hj | [-> | Hj]].
      - rewrite decide_True //.
        rewrite /waiter_model. setoid_rewrite decide_True; last first.
        { rewrite /past. simpl_length. lia. }
        iSteps.
      - rewrite decide_False; first lia.
        rewrite /waiter_model. setoid_rewrite decide_True; last first.
        { rewrite /past. simpl_length/=. lia. }
        iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iSteps.
      - rewrite decide_False; first lia.
        rewrite /waiter_model. setoid_rewrite decide_False; last first.
        { rewrite /past. simpl_length/=. lia. }
        iSteps.
    }

    iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁") as "HΦ".

    iSplitR "Hfront_data HΦ".
    { iFrameSteps.
      iApply (big_sepL_impl with "Hcapacities").
      iSteps. rewrite /past length_app /=. iSteps.
    }
    iSteps.
  Qed.
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
    iIntros "%Φ (:inv) HΦ".

    wp_apply (mpmc_bqueue_pop_spec_aux with "[$]").
    iAuIntro.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iAaccIntro with "Hmodel₁"; first iSteps.
    iStepFrameSteps. iPureIntro.
    etrans; last done. apply length_tail.
  Qed.
End mpmc_bqueue_G.

From zoo_saturn Require
  mpmc_bqueue__opaque.

#[global] Opaque mpmc_bqueue_inv.
#[global] Opaque mpmc_bqueue_model.
