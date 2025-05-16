From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.auth_nat_max
  lib.twins
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
  mpmc_queue_1__code.
From zoo_saturn Require Import
  mpmc_queue_1__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v t : val.
Implicit Types vs : list val.
Implicit Types waiter : gname.
Implicit Types waiters : gmap gname nat.

Class MpmcQueue1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_queue_1_G_history_G :: MonoListG Σ location ;
  #[local] mpmc_queue_1_G_front_G :: AuthNatMaxG Σ ;
  #[local] mpmc_queue_1_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] mpmc_queue_1_G_waiters_G :: ghost_mapG Σ gname nat ;
  #[local] mpmc_queue_1_G_saved_pred_G :: SavedPredG Σ bool ;
}.

Definition mpmc_queue_1_Σ := #[
  mono_list_Σ location ;
  auth_nat_max_Σ ;
  twins_Σ (leibnizO (list val)) ;
  ghost_mapΣ gname nat ;
  saved_pred_Σ bool
].
#[global] Instance subG_mpmc_queue_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_queue_1_Σ Σ →
  MpmcQueue1G Σ.
Proof.
  solve_inG.
Qed.

Section mpmc_queue_1_G.
  Context `{mpmc_queue_1_G : MpmcQueue1G Σ}.

  Record metadata := {
    metadata_inv : namespace ;
    metadata_history : gname ;
    metadata_front : gname ;
    metadata_model : gname ;
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
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition history_auth γ hist :=
    history_auth' γ.(metadata_history) hist.
  #[local] Definition history_at γ i node :=
    mono_list_at γ.(metadata_history) i node.

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
    xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
    ([∗ list] node; v ∈ nodes; vs, node.[data] ↦ v) ∗
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
  #[local] Definition inv' l γ :=
    inv γ.(metadata_inv) (inv_inner l γ).
  Definition mpmc_queue_1_inv t ι : iProp Σ :=
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

  Definition mpmc_queue_1_model t vs : iProp Σ :=
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

  #[global] Instance mpmc_queue_1_model_timeless t vs :
    Timeless (mpmc_queue_1_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_1_inv_persistent t ι :
    Persistent (mpmc_queue_1_inv t ι).
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
  #[local] Lemma history_at_lookup γ hist i node :
    history_auth γ hist -∗
    history_at γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list_at_valid.
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

  Lemma mpmc_queue_1_create_spec ι :
    {{{
      True
    }}}
      mpmc_queue_1_create ()
    {{{ t,
      RET t;
      mpmc_queue_1_inv t ι ∗
      mpmc_queue_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_block front as "#Hfront_header" "_" "(Hfront_next & _)".
    wp_block l as "Hmeta" "(Hl_front & Hl_back & _)".

    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod front_alloc as "(%γ_front & Hfront_auth)".
    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
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
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc.
    iExists [front], [], front, [], front, [], ∅. iFrameSteps.
    - rewrite elem_of_list_singleton //.
    - rewrite xtchain_singleton big_sepM_empty. iSteps.
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
    pose proof Hback as (i & Hlookup)%elem_of_list_lookup.
    iDestruct (xtchain_lookup_header with "Hhist") as "#Hback_header"; first done.
    iDestruct (history_at_get with "Hhistory_auth") as "#Hhistory_at_back"; first done.
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Inductive operation :=
    | IsEmpty waiter (Ψ : bool → iProp Σ)
    | Pop (Ψ : option val → iProp Σ)
    | Other.
  Implicit Types op : operation.
  Inductive operation' :=
    | IsEmpty'
    | Pop'
    | Other'.
  #[local] Instance operation'_eq_dec : EqDecision operation' :=
    ltac:(solve_decision).
  #[local] Coercion operation_to_operation' op :=
    match op with
    | IsEmpty _ _ =>
        IsEmpty'
    | Pop _ =>
        Pop'
    | Other =>
        Other'
    end.
  #[local] Definition pop_au l γ Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      mpmc_queue_1_model #l vs
    }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
      mpmc_queue_1_model #l (tail vs)
    , COMM
      True -∗ Ψ (head vs)
    }>.
  #[local] Lemma next_spec_aux op l γ i node :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      ( if decide (op = Other' :> operation') then True else
          front_lb γ i
      ) ∗
      match op with
      | IsEmpty waiter Ψ =>
          saved_pred waiter Ψ ∗
          waiters_at γ waiter i ∗
          £ 1
      | Pop Ψ =>
          pop_au l γ Ψ
      | Other =>
          True
      end
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝ ∗
        match op with
        | IsEmpty waiter Ψ =>
            Ψ true
        | Pop Ψ =>
            Ψ None
        | Other =>
            True
        end
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        match op with
        | IsEmpty waiter Ψ =>
            Ψ false
        | Pop Ψ =>
            pop_au l γ Ψ
        | Other =>
            True
        end
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & Hop) HΦ".

    iInv "Hinv" as "(:inv_inner)".
    iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
    iDestruct (xtchain_lookup_acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
    wp_load.
    iDestruct ("Hhist" with "Hnode") as "Hhist".
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (xtchain_lookup_header with "Hhist") as "#Hnode'_header"; first done.
      iDestruct (history_at_get (S i) with "Hhistory_auth") as "#Hhistory_at_node'"; first done.
      destruct op; [| iSteps..].
      iDestruct "Hop" as "(#Hfront_lb_node & #Hwaiter & Hwaiters_at & H£)".
      iMod (waiters_delete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
      iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
      iDestruct (saved_pred_agree false with "Hwaiter Hwaiter_") as "Heq".
      iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
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

        iSplitR "Heq HΨ HΦ". { iFrameSteps. }
        iSteps. iRewrite "Heq". iSteps.

      + iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi_.
        rewrite decide_True; first lia.
        iSplitR "Heq HΨ HΦ". { iFrameSteps. }
        iSteps. iRewrite "Heq". iSteps.

    - destruct (decide (op = Other' :> operation')).
      { destruct op; try done. iSteps. }
      iDestruct "Hop" as "(#Hfront_lb_node & Hop)".
      iDestruct (front_lb_valid with "Hfront_auth Hfront_lb_node") as %Hi.
      opose proof* length_lookup_last as Hlength; [done.. |].
      rewrite Hhist length_app /= in Hlength.
      assert (i = length past) as -> by lia.
      assert (length nodes = 0) as ->%nil_length_inv by lia.
      iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
      destruct op; last done.

      + iDestruct "Hop" as "(#Hwaiter & Hwaiters_at & H£)".
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

      + iMod "Hop" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "[Hmodel₁] [//]") as "HΨ"; first iSteps.

        iSplitR "HΨ HΦ". { iFrameSteps. }
        iSteps.
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
    wp_apply (next_spec_aux Other); iSteps.
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
    wp_apply (next_spec_aux (IsEmpty _ _) with "[$]").
    iSteps.
  Qed.
  #[local] Lemma next_spec_pop {l γ i node} Ψ :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      front_lb γ i ∗
      pop_au l γ Ψ
    }}}
      (#node).{next}
    {{{ res,
      RET res;
        ⌜res = §Null%V⌝ ∗
        Ψ None
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) false ∗
        pop_au l γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node & #Hfront_lb_node & Hau) HΦ".
    wp_apply (next_spec_aux (Pop _) with "[$]").
    iSteps.
  Qed.

  Lemma mpmc_queue_1_is_empty_spec t ι :
    <<<
      mpmc_queue_1_inv t ι
    | ∀∀ vs,
      mpmc_queue_1_model t vs
    >>>
      mpmc_queue_1_is_empty t @ ↑ι
    <<<
      mpmc_queue_1_model t vs
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
  Lemma mpmc_queue_1_is_empty_spec' t ι :
    {{{
      mpmc_queue_1_inv t ι
    }}}
      mpmc_queue_1_is_empty t
    {{{ b,
      RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_apply (front_spec with "Hinv") as (front i) "(:node_model =front front=)".
    wp_match.
    wp_apply (next_spec with "[$]") as (res) "[-> | (%node & -> & _)]"; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_1_push_0_spec l γ i node new_back v :
    <<<
      meta l nroot γ ∗
      inv' l γ ∗
      node_model γ node i false ∗
      new_back ↦ₕ Header §Node 2 ∗
      new_back.[next] ↦ §Null ∗
      new_back.[data] ↦ v
    | ∀∀ vs,
      mpmc_queue_1_model #l vs
    >>>
      mpmc_queue_1_push_0 #node #new_back @ ↑γ.(metadata_inv)
    <<<
      mpmc_queue_1_model #l (vs ++ [v])
    | RET ();
      ∃ j,
      history_at γ j new_back
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & (:node_model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

    iLöb as "HLöb" forall (i node) "Hnode_header Hhistory_at_node".

    wp_rec. wp_match.
    wp_smart_apply (next_spec with "[$]") as (res) "[-> | (%node' & -> & (:node_model =node'))]"; last iSteps.
    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
    iDestruct (xtchain_lookup with "Hhist") as "(Hhist1 & _ & Hnode & Hhist2)"; first done.
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - wp_cas as _ | [=].
      iDestruct (xtchain_lookup_2 with "Hhist1 Hnode_header Hnode Hhist2") as "Hhist"; [done | rewrite Hlookup' // |].
      iSplitR "Hnew_back_next Hnew_back_data HΦ". { iFrameSteps. }
      iSteps.

    - wp_cas as ? | _; first done.
      iDestruct (xtchain_lookup_2 with "Hhist1 Hnode_header Hnode []") as "Hhist"; [done | rewrite Hlookup' // | ..].
      { rewrite -(length_lookup_last hist i) // drop_all.
        iApply xtchain_nil.
      }
      iDestruct (big_sepL2_snoc_2 with "Hnodes Hnew_back_data") as "Hnodes".
      iDestruct (xtchain_snoc_2 with "Hhist Hnew_back_header Hnew_back_next") as "Hhist".
      iMod (history_update new_back with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at_new_back)".

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; [iSteps.. |].

      iSplitR "HΦ".
      { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
        iSteps; iPureIntro.
        - rewrite Hhist -assoc //.
        - set_solver.
      }
      iSteps.
  Qed.

  #[local] Lemma mpmc_queue_1_fix_back_spec l γ i back j new_back :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i back ∗
      node_model γ new_back j false
    }}}
      mpmc_queue_1_fix_back #l #back #new_back
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
      iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_new_back") as %Hnew_back%elem_of_list_lookup_2.
      iSteps.
    }

    destruct b; last iSteps.
    wp_smart_apply domain_yield_spec.
    wp_smart_apply (back_spec with "Hinv") as (back' i') "(:node_model =back')".
    iApply ("HLöb" with "HΦ Hhistory_at_back'").
  Qed.

  Lemma mpmc_queue_1_push_spec t ι v :
    <<<
      mpmc_queue_1_inv t ι
    | ∀∀ vs,
      mpmc_queue_1_model t vs
    >>>
      mpmc_queue_1_push t v @ ↑ι
    <<<
      mpmc_queue_1_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
    wp_match.
    wp_smart_apply (back_spec with "Hinv") as (back i) "(:node_model =back)".
    wp_smart_apply (mpmc_queue_1_push_0_spec with "[$]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
    wp_smart_apply (mpmc_queue_1_fix_back_spec with "[] HΦ"); first iSteps.
  Qed.

  Lemma mpmc_queue_1_pop_spec t ι :
    <<<
      mpmc_queue_1_inv t ι
    | ∀∀ vs,
      mpmc_queue_1_model t vs
    >>>
      mpmc_queue_1_pop t @ ↑ι
    <<<
      mpmc_queue_1_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (front_spec with "Hinv") as (front i) "(:node_model =front front=)".
    wp_match.
    wp_smart_apply (next_spec_pop Φ with "[$HΦ]") as (res) "[(-> & HΦ) | (%new_front & -> & (:node_model =new_front) & HΦ)]"; [iSteps.. |].
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

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hfront_data HΦ". { iFrameSteps. }
    iSteps.
  Qed.
End mpmc_queue_1_G.

#[global] Opaque mpmc_queue_1_create.
#[global] Opaque mpmc_queue_1_is_empty.
#[global] Opaque mpmc_queue_1_push.
#[global] Opaque mpmc_queue_1_pop.

#[global] Opaque mpmc_queue_1_inv.
#[global] Opaque mpmc_queue_1_model.
