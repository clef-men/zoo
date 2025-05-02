From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  relations
  countable.
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
    metadata_inv : namespace ;
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

  #[local] Definition producer' γ_model ws :=
    auth_twins_auth _ γ_model ws.
  #[local] Definition producer γ :=
    producer' γ.(metadata_model).

  #[local] Definition model₁' γ_model vs :=
    auth_twins_twin1 _ γ_model vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    auth_twins_twin2 _ γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition waiters_auth' γ_waiters waiters :=
    ghost_map_auth γ_waiters 1 waiters.
  #[local] Definition waiters_auth γ waiters :=
    waiters_auth' γ.(metadata_waiters) waiters.
  #[local] Definition waiters_at γ waiter i :=
    ghost_map_elem γ.(metadata_waiters) waiter (DfracOwn 1) i.

  #[local] Definition node_model γ node i b : iProp Σ :=
    node ↦ₕ Header §Node 2 ∗
    history_at γ i node ∗
    if b then front_lb γ i else True%I.
  #[local] Instance : CustomIpatFormat "node_model" :=
    "(
      #H{}_header &
      #Hhistory_at_{} &
      {{front}#Hfront_lb_{}=_}
    )".

  #[local] Definition waiter_au γ Ψ : iProp Σ :=
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
    ∃ hist past front nodes vs waiters,
    ⌜hist = past ++ front :: nodes⌝ ∗
    l.[front] ↦ #front ∗
    xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
    ([∗ list] node; v ∈ nodes; vs, node.[xtchain_data] ↦ v) ∗
    history_auth γ hist ∗
    front_auth γ (length past) ∗
    model₂ γ vs ∗
    waiters_auth γ waiters ∗
    ([∗ map] waiter ↦ i ∈ waiters, waiter_model γ past waiter i).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %hist{} &
      %past{} &
      %front{} &
      %nodes{} &
      %vs{} &
      %waiters{} &
      >%Hhist{} &
      >Hl_front &
      >Hhist &
      >Hnodes &
      >Hhistory_auth &
      >Hfront_auth &
      >Hmodel₂ &
      >Hwaiters_auth &
      Hwaiters
    )".
  #[local] Definition inv' l γ :=
    inv γ.(metadata_inv) (inv_inner l γ).
  Definition spmc_queue_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜ι = γ.(metadata_inv)⌝ ∗
    meta l nroot γ ∗
    inv' l γ.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition spmc_queue_producer t ws : iProp Σ :=
    ∃ l γ back,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[back] ↦ #back ∗
    back ↦ₕ Header §Node 2 ∗
    history_last γ back ∗
    producer γ ws.
  #[local] Instance : CustomIpatFormat "producer" :=
    "(
      %l_{} &
      %γ_{} &
      %back{} &
      %Heq{} &
      #Hmeta_{} &
      Hl_back{_{}} &
      #Hback{}_header &
      Hhistory_last{_{}} &
      Hproducer{_{}}
    )".

  Definition spmc_queue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_{} &
      %γ_{} &
      %Heq{} &
      #Hmeta_{} &
      Hmodel₁
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

  #[local] Lemma history_alloc front :
    ⊢ |==>
      ∃ γ_history,
      history_auth' γ_history [front] ∗
      history_last' γ_history front.
  Proof.
    iMod mono_list_alloc as "(%γ_history & $ & $)".
    iSteps.
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
  #[local] Lemma history_auth_last γ hist node :
    history_auth γ hist -∗
    history_last γ node -∗
    ⌜last hist = Some node⌝.
  Proof.
    iIntros "Hauth_1 (:history_last =2)".
    iDestruct (mono_list_auth_agree with "Hauth_1 Hauth_2") as %<-.
    iSteps.
  Qed.
  #[local] Lemma history_update {γ hist node} node' :
    history_auth γ hist -∗
    history_last γ node ==∗
      history_auth γ (hist ++ [node']) ∗
      history_last γ node'.
  Proof.
    iIntros "Hauth_1 (:history_last =2)".
    rewrite /history_auth /history_auth'.
    iDestruct (mono_list_auth_combine with "Hauth_1 Hauth_2") as "(<- & Hauth)". rewrite dfrac_op_own Qp.half_half.
    iMod (mono_list_update_snoc with "Hauth") as "($ & $)".
    rewrite last_snoc //.
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

  #[local] Lemma producer_valid_1 γ ws vs :
    producer γ ws -∗
    model₁ γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    rewrite -preorder_rtc.
    apply: auth_twins_valid_1.
  Qed.
  #[local] Lemma producer_exclusive γ ws1 ws2 :
    producer γ ws1 -∗
    producer γ ws2 -∗
    False.
  Proof.
    apply: auth_twins_auth_exclusive.
  Qed.

  #[local] Lemma model_producer_alloc :
    ⊢ |==>
      ∃ γ_model,
      producer' γ_model [] ∗
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply auth_twins_alloc.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: auth_twins_agree_L.
  Qed.
  #[local] Lemma model_push {γ ws vs1 vs2} v :
    producer γ ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      producer γ (vs1 ++ [v]) ∗
      model₁ γ (vs1 ++ [v]) ∗
      model₂ γ (vs1 ++ [v]).
  Proof.
    apply auth_twins_update_auth.
  Qed.
  #[local] Lemma model_pop γ v vs1 vs2 :
    model₁ γ (v :: vs1) -∗
    model₂ γ vs2 ==∗
      model₁ γ vs1 ∗
      model₂ γ vs1.
  Proof.
    apply: auth_twins_update_twins_L.
    rewrite preorder_rtc. solve_suffix.
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

  Opaque history_last'.

  Lemma spmc_queue_producer_valid t vs ws :
    spmc_queue_producer t ws -∗
    spmc_queue_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (producer_valid_1 with "Hproducer_1 Hmodel₁").
  Qed.
  Lemma spmc_queue_producer_exclusive t ws1 ws2 :
    spmc_queue_producer t ws1 -∗
    spmc_queue_producer t ws2 -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (producer_exclusive with "Hproducer_1 Hproducer_2").
  Qed.

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
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_block front as "#Hfront_header" "_" "(Hfront_next & _)".
    wp_block l as "Hmeta" "(Hl_front & Hl_back & _)".

    iMod history_alloc as "(%γ_history & Hhistory_auth & Hhistory_last)".
    iMod front_alloc as "(%γ_front & Hfront_auth)".
    iMod model_producer_alloc as "(%γ_model & Hproducer & Hmodel₁ & Hmodel₂)".
    iMod waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ := {|
      metadata_inv := ι ;
      metadata_history := γ_history ;
      metadata_front := γ_front ;
      metadata_model := γ_model ;
      metadata_waiters := γ_waiters ;
    |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hl_back Hhistory_last Hproducer"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc.
    iExists [front], [], front, [], [], ∅. iFrameSteps.
    rewrite xtchain_singleton big_sepM_empty. iSteps.
  Qed.

  #[local] Lemma front_spec_strong au Ψ l γ :
    {{{
      inv' l γ ∗
      if negb au then True else
        waiter_au γ Ψ
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      node_model γ front i true ∗
      if negb au then True else
        ∃ waiter,
        saved_pred waiter Ψ ∗
        waiters_at γ waiter i
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    assert (hist !! (length past) = Some front) as Hlookup.
    { rewrite Hhist list_lookup_middle //. }
    iDestruct (xtchain_lookup_header with "Hhist") as "#Hfront_header"; first done.
    iDestruct (history_at_get _ front with "Hhistory_auth") as "#Hhistory_at"; first done.
    iDestruct (front_lb_get with "Hfront_auth") as "#Hfront_lb_front".
    destruct au; last iSteps.
    iMod (saved_pred_alloc_cofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & #Hwaiter)".
    rewrite not_elem_of_dom in Hwaiter.
    iMod (waiters_insert _ (length past) with "Hwaiters_auth") as "(Hwaiter_auth & Hwaiters_at)"; first done.
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
    wp_apply (front_spec_strong false inhabitant with "[$Hinv]").
    iSteps.
  Qed.

  Inductive op :=
    | IsEmpty
    | Pop
    | Other.
  #[local] Instance op_eq_dec : EqDecision op :=
    ltac:(solve_decision).
  #[local] Lemma xtchain_next_spec_strong op TB waiter Ψ_is_empty β x Ψ_pop l γ i node :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      ( if decide (op = Other) then True else
          front_lb γ i
      ) ∗
      match op with
      | IsEmpty =>
          saved_pred waiter Ψ_is_empty ∗
          waiters_at γ waiter i ∗
          £ 1
      | Pop =>
          atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑γ.(metadata_inv)) ∅ (tele_app $ spmc_queue_model #l) β Ψ_pop ∗
          (spmc_queue_model #l [] -∗ β [tele_arg []] x)
      | Other =>
          True
      end
    }}}
      (#node).{xtchain_next}
    {{{ res,
      RET res;
      ( ⌜res = ()%V⌝ ∗
        match op with
        | IsEmpty =>
            Ψ_is_empty true
        | Pop =>
            Ψ_pop [tele_arg []] x
        | Other =>
            True
        end
      ) ∨ (
        ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        match op with
        | IsEmpty =>
            Ψ_is_empty false
        | Pop =>
            atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑γ.(metadata_inv)) ∅ (tele_app $ spmc_queue_model #l) β Ψ_pop
        | Other =>
            True
        end
      )
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & Hop) HΦ".

    iInv "Hinv" as "(:inv_inner)".
    iDestruct (history_agree with "Hhistory_auth Hhistory_at_node") as %Hlookup.
    iDestruct (xtchain_lookup_acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
    wp_load.
    iDestruct ("Hhist" with "Hnode") as "Hhist".
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (xtchain_lookup_header with "Hhist") as "#Hnode'_header"; first done.
      iDestruct (history_at_get (S i) with "Hhistory_auth") as "#Hhistory_at_node'"; first done.
      destruct op; [| iSteps..].
      iDestruct "Hop" as "(#Hfront_lb_node & #Hwaiter & Hwaiters_at & H£)".
      iDestruct (waiters_lookup with "Hwaiters_auth Hwaiters_at") as %Hwaiters_lookup.
      iMod (waiters_delete with "Hwaiters_auth Hwaiters_at") as "Hwaiters_auth".
      iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ & _Hwaiter & HΨ) & Hwaiters)"; first done.
      iDestruct (saved_pred_agree false with "Hwaiter _Hwaiter") as "HΨ_is_empty".
      iMod (lc_fupd_elim_later with "H£ HΨ_is_empty") as "HΨ_is_empty".
      destruct (decide (i = length past)) as [-> | Hi].

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
        { destruct (decide (vs = [])) as [-> |]; last done.
          iDestruct (big_sepL2_length with "Hnodes") as %->%nil_length_inv.
          iSteps.
        }
        rewrite bool_decide_eq_false_2 //.

        iSplitR "HΨ_is_empty HΨ HΦ". { iFrameSteps. }
        iSteps. iRewrite "HΨ_is_empty". iSteps.

      + iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi_.
        rewrite decide_True; first lia.
        iSplitR "HΨ_is_empty HΨ HΦ". { iFrameSteps. }
        iSteps. iRewrite "HΨ_is_empty". iSteps.

    - destruct (decide (op = Other)) as [-> | Hop]; first iSteps.
      iDestruct "Hop" as "(#Hfront_lb_node & Hop)".
      iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi.
      opose proof* length_lookup_last as Hlength; [done.. |].
      rewrite Hhist length_app /= in Hlength.
      assert (i = length past) as -> by lia.
      assert (length nodes = 0) as ->%nil_length_inv by lia.
      iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
      destruct op; last done.

      + iDestruct "Hop" as "(#Hwaiter & Hwaiters_at & H£)".
        iDestruct (waiters_lookup with "Hwaiters_auth Hwaiters_at") as %Hwaiters_lookup.
        iMod (waiters_delete with "Hwaiters_auth Hwaiters_at") as "Hwaiters_auth".
        iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ & _Hwaiter & HΨ) & Hwaiters)"; first done.
        iDestruct (saved_pred_agree true with "Hwaiter _Hwaiter") as "HΨ_is_empty".
        iMod (lc_fupd_elim_later with "H£ HΨ_is_empty") as "HΨ_is_empty".
        rewrite decide_False; first lia.

        iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iSplitR "HΨ_is_empty HΨ HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        iApply "HΦ".
        iLeft. iRewrite "HΨ_is_empty". iSteps.

      + iDestruct "Hop" as "(HΨ & Hβ)".

        iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iDestruct ("Hβ" with "[Hmodel₁]") as "Hβ"; first iSteps.
        iMod ("HΨ" with "Hβ") as "HΨ".

        iSplitR "HΨ HΦ". { iFrameSteps. }
        iSteps.
  Qed.
  #[local] Lemma xtchain_next_spec l γ i node :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node
    }}}
      (#node).{xtchain_next}
    {{{ res,
      RET res;
        ⌜res = ()%V⌝
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node) HΦ".
    wp_apply (xtchain_next_spec_strong Other TeleO inhabitant inhabitant inhabitant inhabitant inhabitant); iSteps.
  Qed.

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
    iIntros "%Φ (:inv) HΦ".

    wp_rec credit:"H£".
    wp_smart_apply (front_spec_strong true (λ b, Φ #b) with "[$Hinv HΦ]") as (node i) "((:node_model =node front=) & %waiter & #Hwaiter & Hwaiters_at)".
    { rewrite /= /waiter_au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iAaccIntro with "Hmodel₁"; iSteps.
    }
    wp_match.
    wp_smart_apply (xtchain_next_spec_strong IsEmpty [tele_pair bool] _ _ inhabitant [tele_arg true] inhabitant with "[$]") as (res) "[(-> & HΦ) | (%node' & -> & _ & HΦ)]"; iSteps.
  Qed.

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
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec.
    wp_block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
    wp_match. wp_load. wp_match.

    wp_bind (_ <-{next} _)%E.
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (history_auth_last with "Hhistory_auth Hhistory_last") as %?.
    wp_apply (xtchain_set_next_spec_last' new_back with "[$]") as "Hhist"; first done.
    iMod (history_update new_back with "Hhistory_auth Hhistory_last") as "(Hhistory_auth & Hhistory_last)".
    iDestruct (big_sepL2_snoc_2 with "Hnodes Hnew_back_data") as "Hnodes".

    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_push v with "Hproducer Hmodel₁ Hmodel₂") as "(Hproducer & Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_back Hhistory_last Hproducer HΦ".
    { iFrameSteps. list_simplifier. done. }
    iSteps.
  Qed.

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
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (front_spec with "Hinv") as (front i) "(#Hfront_header & #Hhistory_at_front & #Hfront_lb_front)".
    wp_match.
    wp_smart_apply (xtchain_next_spec_strong Pop _ inhabitant inhabitant _ [tele_arg] with "[$HΦ]") as (res) "[(-> & HΦ) | (%new_front & -> & (:node_model =new_front) & HΦ)]"; [iSteps.. |].
    wp_match. wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (history_agree with "Hhistory_auth Hhistory_at_new_front") as %Hlookup.
    iDestruct (xtchain_lookup_acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
    wp_cas as _ | [= <-]; first iSteps.
    iDestruct ("Hhist" with "Hnode") as "Hhist".
    iDestruct (history_agree with "Hhistory_auth Hhistory_at_front") as %Hlookup_old.
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

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_pop with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hfront_data HΦ". { iFrameSteps. }
    iSteps.
  Qed.
End spmc_queue_G.

#[global] Opaque spmc_queue_create.
#[global] Opaque spmc_queue_is_empty.
#[global] Opaque spmc_queue_push.
#[global] Opaque spmc_queue_pop.

#[global] Opaque spmc_queue_inv.
#[global] Opaque spmc_queue_producer.
#[global] Opaque spmc_queue_model.
