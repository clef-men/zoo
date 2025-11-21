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
Implicit Types front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v : val.
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

Module base.
  Section mpmc_queue_1_G.
    Context `{mpmc_queue_1_G : MpmcQueue1G Σ}.

    Implicit Types t : location.

    Record mpmc_queue_1_name := {
      mpmc_queue_1_name_inv : namespace ;
      mpmc_queue_1_name_history : gname ;
      mpmc_queue_1_name_front : gname ;
      mpmc_queue_1_name_model : gname ;
      mpmc_queue_1_name_waiters : gname ;
    }.
    Implicit Type γ : mpmc_queue_1_name.

    #[global] Instance mpmc_queue_1_name_eq_dec : EqDecision mpmc_queue_1_name :=
      ltac:(solve_decision).
    #[global] Instance mpmc_queue_1_name_countable :
      Countable mpmc_queue_1_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition history_auth' γ_history hist :=
      mono_list_auth γ_history (DfracOwn 1) hist.
    #[local] Definition history_auth γ hist :=
      history_auth' γ.(mpmc_queue_1_name_history) hist.
    #[local] Definition history_at γ i node :=
      mono_list_at γ.(mpmc_queue_1_name_history) i node.

    #[local] Definition front_auth' γ_front i :=
      auth_nat_max_auth γ_front (DfracOwn 1) i.
    #[local] Definition front_auth γ i :=
      front_auth' γ.(mpmc_queue_1_name_front) i.
    #[local] Definition front_lb γ i :=
      auth_nat_max_lb γ.(mpmc_queue_1_name_front) i.

    #[local] Definition model₁' γ_model vs :=
      twins_twin1 γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ vs :=
      model₁' γ.(mpmc_queue_1_name_model) vs.
    #[local] Definition model₂' γ_model vs :=
      twins_twin2 γ_model vs.
    #[local] Definition model₂ γ vs :=
      model₂' γ.(mpmc_queue_1_name_model) vs.

    #[local] Definition waiters_auth' γ_waiters waiters :=
      ghost_map_auth γ_waiters 1 waiters.
    #[local] Definition waiters_auth γ waiters :=
      waiters_auth' γ.(mpmc_queue_1_name_waiters) waiters.
    #[local] Definition waiters_at γ waiter i :=
      ghost_map_elem γ.(mpmc_queue_1_name_waiters) waiter (DfracOwn 1) i.

    #[local] Definition node_model γ node i b : iProp Σ :=
      node ↦ₕ Header §Node 2 ∗
      history_at γ i node ∗
      if b then front_lb γ i else True%I.
    #[local] Instance : CustomIpatFormat "node_model" :=
      " ( #H{}_header &
          #Hhistory_at_{} &
          {{front}#Hfront_lb_{};_}
        )
      ".

    #[local] Definition waiter_au γ (Ψ : bool → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(mpmc_queue_1_name_inv), ∅ <{
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

    #[local] Definition inv_inner t γ : iProp Σ :=
      ∃ hist past front nodes back vs waiters,
      ⌜hist = past ++ front :: nodes⌝ ∗
      ⌜back ∈ hist⌝ ∗
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
      ([∗ list] node; v ∈ nodes; vs, node.[data] ↦ v) ∗
      history_auth γ hist ∗
      front_auth γ (length past) ∗
      model₂ γ vs ∗
      waiters_auth γ waiters ∗
      ([∗ map] waiter ↦ i ∈ waiters, waiter_model γ past waiter i).
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
          >Ht_front &
          >Ht_back &
          >Hhist &
          >Hnodes &
          >Hhistory_auth &
          >Hfront_auth &
          >Hmodel₂ &
          >Hwaiters_auth &
          Hwaiters
        )
      ".
    #[local] Definition inv' t γ :=
      inv γ.(mpmc_queue_1_name_inv) (inv_inner t γ).
    Definition mpmc_queue_1_inv t γ ι : iProp Σ :=
      ⌜ι = γ.(mpmc_queue_1_name_inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpatFormat "inv" :=
      " ( -> &
          #Hinv
        )
      ".

    Definition mpmc_queue_1_model :=
      model₁.
    #[local] Instance : CustomIpatFormat "model" :=
      " Hmodel₁{_{}}
      ".

    #[global] Instance mpmc_queue_1_model_timeless γ vs :
      Timeless (mpmc_queue_1_model γ vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpmc_queue_1_inv_persistent t γ ι :
      Persistent (mpmc_queue_1_inv t γ ι).
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

    Lemma mpmc_queue_1_model_exclusive γ vs1 vs2 :
      mpmc_queue_1_model γ vs1 -∗
      mpmc_queue_1_model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma mpmc_queue_1_create_spec ι :
      {{{
        True
      }}}
        mpmc_queue_1_create ()
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        mpmc_queue_1_inv t γ ι ∗
        mpmc_queue_1_model γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_block front as "#Hfront_header" "_" "(Hfront_next & _)".
      wp_block t as "Hmeta" "(Ht_front & Ht_back & _)".

      iMod history_alloc as "(%γ_history & Hhistory_auth)".
      iMod front_alloc as "(%γ_front & Hfront_auth)".
      iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ := {|
        mpmc_queue_1_name_inv := ι ;
        mpmc_queue_1_name_history := γ_history ;
        mpmc_queue_1_name_front := γ_front ;
        mpmc_queue_1_name_model := γ_model ;
        mpmc_queue_1_name_waiters := γ_waiters ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameStep.
      iApply inv_alloc.
      iExists [front], [], front, [], front, [], ∅. iFrameSteps.
      - rewrite list_elem_of_singleton //.
      - rewrite xtchain_singleton big_sepM_empty. iSteps.
    Qed.

    #[local] Lemma front_spec_strong Ψ t γ :
      {{{
        inv' t γ ∗
        if Ψ is Some Ψ then
          waiter_au γ Ψ
        else
          True
      }}}
        (#t).{front}
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
    #[local] Lemma front_spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{front}
      {{{ front i,
        RET #front;
        node_model γ front i true
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".
      wp_apply (front_spec_strong None with "[$Hinv]").
      iSteps.
    Qed.

    #[local] Lemma back_spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{back}
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
    #[local] Definition pop_au γ (Ψ : option val → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(mpmc_queue_1_name_inv), ∅ <{
        model₁ γ (tail vs)
      , COMM
        Ψ (head vs)
      }>.
    #[local] Lemma next_spec_aux op t γ i node :
      {{{
        inv' t γ ∗
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
            pop_au γ Ψ
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
              pop_au γ Ψ
          | Other =>
              True
          end
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & Hop) HΦ".

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

      - destruct_decide (op = Other' :> operation').
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

        + iMod "Hop" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "HΨ HΦ". { iFrameSteps. }
          iSteps.
    Qed.
    #[local] Lemma next_spec {t γ i} node :
      {{{
        inv' t γ ∗
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
      iIntros "%Φ (#Hinv & #Hhistory_at_node) HΦ".
      wp_apply (next_spec_aux Other); iSteps.
    Qed.
    #[local] Lemma next_spec_is_empty {t γ i node} waiter Ψ :
      {{{
        inv' t γ ∗
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
      iIntros "%Φ (#Hinv & #Hhistory_at_node & #Hfront_lb_node & #Hwaiter & Hwaiters_at & H£) HΦ".
      wp_apply (next_spec_aux (IsEmpty _ _) with "[$]").
      iSteps.
    Qed.
    #[local] Lemma next_spec_pop {t γ i node} Ψ :
      {{{
        inv' t γ ∗
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
      iIntros "%Φ (#Hinv & #Hhistory_at_node & #Hfront_lb_node & Hau) HΦ".
      wp_apply (next_spec_aux (Pop _) with "[$]").
      iSteps.
    Qed.

    Lemma mpmc_queue_1_is_empty_spec t γ ι :
      <<<
        mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        mpmc_queue_1_model γ vs
      >>>
        mpmc_queue_1_is_empty #t @ ↑ι
      <<<
        mpmc_queue_1_model γ vs
      | RET #(bool_decide (vs = []%list));
        £ 1
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "(H£1 & H£2)"; first done.
      iDestruct (atomic_update_frame_l with "[H£1 $HΦ]") as "HΦ"; first iAccu.

      wp_smart_apply (front_spec_strong (Some $ λ b, Φ #b) with "[$Hinv HΦ]")
      as (node i) "((:node_model =node front=) & %waiter & #Hwaiter & Hwaiters_at)".
      { rewrite /= /waiter_au. iAuIntro.
        iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; iSteps.
      }
      wp_match.
      wp_smart_apply (next_spec_is_empty with "[$]"); iSteps.
    Qed.
    Lemma mpmc_queue_1_is_empty_spec' t γ ι :
      {{{
        mpmc_queue_1_inv t γ ι
      }}}
        mpmc_queue_1_is_empty #t
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

    #[local] Lemma mpmc_queue_1_push_0_spec t γ i node new_back v :
      <<<
        inv' t γ ∗
        node_model γ node i false ∗
        new_back ↦ₕ Header §Node 2 ∗
        new_back.[next] ↦ §Null ∗
        new_back.[data] ↦ v
      | ∀∀ vs,
        mpmc_queue_1_model γ vs
      >>>
        mpmc_queue_1_push_0 #node #new_back @ ↑γ.(mpmc_queue_1_name_inv)
      <<<
        mpmc_queue_1_model γ (vs ++ [v])
      | RET ();
        ∃ j,
        history_at γ j new_back
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & (:node_model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

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

        iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁") as "HΦ".

        iSplitR "HΦ".
        { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
          iSteps; iPureIntro.
          - rewrite Hhist -assoc //.
          - set_solver.
        }
        iSteps.
    Qed.

    #[local] Lemma mpmc_queue_1_fix_back_spec t γ i back j new_back :
      {{{
        inv' t γ ∗
        history_at γ i back ∗
        node_model γ new_back j false
      }}}
        mpmc_queue_1_fix_back #t #back #new_back
      {{{
        RET ();
        True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_back & (:node_model =new_back)) HΦ".

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

    Lemma mpmc_queue_1_push_spec t γ ι v :
      <<<
        mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        mpmc_queue_1_model γ vs
      >>>
        mpmc_queue_1_push #t v @ ↑ι
      <<<
        mpmc_queue_1_model γ (vs ++ [v])
      | RET ();
        £ 1
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec credit:"H£".
      iDestruct (atomic_update_frame_l with "[H£ $HΦ]") as "HΦ"; first iAccu.
      wp_block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
      wp_match.
      wp_smart_apply (back_spec with "Hinv") as (back i) "(:node_model =back)".
      wp_smart_apply (mpmc_queue_1_push_0_spec with "[$]").
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
      wp_smart_apply (mpmc_queue_1_fix_back_spec with "[]"); first iSteps.
      iSteps.
    Qed.

    Lemma mpmc_queue_1_pop_spec t γ ι :
      <<<
        mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        mpmc_queue_1_model γ vs
      >>>
        mpmc_queue_1_pop #t @ ↑ι
      <<<
        mpmc_queue_1_model γ (tail vs)
      | RET head vs;
        £ 1
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp_rec credit:"H£".
      wp_smart_apply (front_spec with "Hinv") as (front i) "(:node_model =front front=)".
      wp_match.
      wp_smart_apply (next_spec_pop (λ o, _ -∗ Φ o)%I with "[$]") as (res) "[(-> & HΦ) | (%new_front & -> & (:node_model =new_front) & HΦ)]"; first iSteps.
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

      iSplitR "Hfront_data H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
  End mpmc_queue_1_G.

  #[global] Opaque mpmc_queue_1_inv.
  #[global] Opaque mpmc_queue_1_model.
End base.

From zoo_saturn Require
  mpmc_queue_1__opaque.

Section mpmc_queue_1_G.
  Context `{mpmc_queue_1_G : MpmcQueue1G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition mpmc_queue_1_inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_queue_1_inv 𝑡 γ ι.
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition mpmc_queue_1_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_queue_1_model γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        Hmeta{_{}} &
        Hmodel{_{}}
      )
    ".

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

  Lemma mpmc_queue_1_model_exclusive t vs1 vs2 :
    mpmc_queue_1_model t vs1 -∗
    mpmc_queue_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpmc_queue_1_model_exclusive with "Hmodel_1 Hmodel_2").
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

    iApply wp_fupd.
    wp_apply (base.mpmc_queue_1_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (meta_set γ with "Hmeta"); first done.
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
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.mpmc_queue_1_is_empty_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
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

    wp_apply (base.mpmc_queue_1_is_empty_spec' with "[$] HΦ").
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
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.mpmc_queue_1_push_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
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
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.mpmc_queue_1_pop_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End mpmc_queue_1_G.

#[global] Opaque mpmc_queue_1_inv.
#[global] Opaque mpmc_queue_1_model.

Section mpmc_queue_1_G.
  Context `{mpmc_queue_1_G : MpmcQueue1G Σ}.
  Context τ `{!iType (iProp Σ) τ}.

  #[local] Definition itype_inner t : iProp Σ :=
    ∃ vs,
    mpmc_queue_1_model t vs ∗
    [∗ list] v ∈ vs, τ v.
  #[local] Instance : CustomIpatFormat "itype_inner" :=
    " ( %vs &
        >Hmodel &
        #Hvs
      )
    ".
  Definition itype_mpmc_queue_1 t : iProp Σ :=
    mpmc_queue_1_inv t (nroot.@"1") ∗
    inv (nroot.@"2") (itype_inner t).
  #[local] Instance : CustomIpatFormat "itype" :=
    " ( #Hinv1 &
        #Hinv2
      )
    ".

  #[global] Instance itype_mpmc_queue_1_itype :
    iType _ itype_mpmc_queue_1.
  Proof.
    split. apply _.
  Qed.

  Lemma mpmc_queue_1_create_type :
    {{{
      True
    }}}
      mpmc_queue_1_create ()
    {{{ t,
      RET t;
      itype_mpmc_queue_1 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (mpmc_queue_1_create_spec with "[//]") as (t) "(#Hinv & Hmodel)".
    rewrite /itype_mpmc_queue_1 /itype_inner. iSteps.
  Qed.

  Lemma mpmc_queue_1_is_empty_type t :
    {{{
      itype_mpmc_queue_1 t
    }}}
      mpmc_queue_1_is_empty t
    {{{ b,
      RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:itype) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_queue_1_is_empty_spec with "Hinv1").
    iInv "Hinv2" as "(:itype_inner)".
    iAaccIntro with "Hmodel"; first iSteps. iSteps as "_ H£".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_queue_1_push_type t v :
    {{{
      itype_mpmc_queue_1 t ∗
      τ v
    }}}
      mpmc_queue_1_push t v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((:itype) & #Hv) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_queue_1_push_spec with "Hinv1").
    iInv "Hinv2" as "(:itype_inner)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "$ !>".
    iSplitR.
    { iModIntro.
      iApply (big_sepL_snoc_2 with "Hvs Hv").
    }
    iIntros "H£".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_queue_1_pop_type t :
    {{{
      itype_mpmc_queue_1 t
    }}}
      mpmc_queue_1_pop t
    {{{ o,
      RET o;
      itype_option τ o
    }}}.
  Proof.
    iIntros "%Φ (:itype) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_queue_1_pop_spec with "Hinv1").
    iInv "Hinv2" as "(:itype_inner)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "$ !>".
    iSplitR.
    { iModIntro.
      destruct vs as [| v vs]; first iSteps.
      iDestruct (big_sepL_cons_1 with "Hvs") as "(_ & $)".
    }
    iIntros "H£".
    iDestruct "Hvs" as "-#Hvs".
    iMod (lc_fupd_elim_later with "H£ [-]") as "H"; first (iModIntro; iAccu). iDestruct "H" as "(Hvs & HΦ)".
    destruct vs; iSteps.
  Qed.
End mpmc_queue_1_G.

#[global] Opaque itype_mpmc_queue_1.
