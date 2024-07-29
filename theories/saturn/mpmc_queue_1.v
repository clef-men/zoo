(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/122
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.auth_nat_max
  lib.twins
  lib.saved_pred.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  option
  xchain.
From zoo.saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v t : val.
Implicit Types vs : list val.

#[local] Notation "'xchain_data'" := (
  in_type "xchain" 1
)(in custom zoo_field
).

#[local] Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_field
).

Definition mpmc_queue_create : val :=
  fun: <> =>
    let: "front" := { (), () } in
    { "front", "front" }.

Definition mpmc_queue_is_empty : val :=
  fun: "t" =>
    "t".{front}.{xchain_next} = ().

#[local] Definition mpmc_queue_do_push : val :=
  rec: "mpmc_queue_do_push" "node" "new_back" =>
    let: "node'" := "node".{xchain_next} in
    if: "node'" = () then (
      ifnot: CAS "node".[xchain_next] () "new_back" then (
        Yield ;;
        "mpmc_queue_do_push" "node" "new_back"
      )
    ) else (
      "mpmc_queue_do_push" "node'" "new_back"
    ).
#[local] Definition mpmc_queue_fix_back : val :=
  rec: "mpmc_queue_fix_back" "t" "back" "new_back" =>
    if: "new_back".{xchain_next} = () and ~ CAS "t".[back] "back" "new_back" then (
      Yield ;;
      "mpmc_queue_fix_back" "t" "t".{back} "new_back"
    ).
Definition mpmc_queue_push : val :=
  fun: "t" "v" =>
    let: "new_back" := { (), "v" } in
    let: "back" := "t".{back} in
    mpmc_queue_do_push "back" "new_back" ;;
    mpmc_queue_fix_back "t" "back" "new_back".

Definition mpmc_queue_pop : val :=
  rec: "mpmc_queue_pop" "t" =>
    let: "old_front" := "t".{front} in
    let: "front" := "old_front".{xchain_next} in
    if: "front" = () then (
      §None
    ) else if: CAS "t".[front] "old_front" "front" then (
        let: "v" := "front".{xchain_data} in
        "front" <-{xchain_data} () ;;
        ‘Some( "v" )
    ) else (
      Yield ;;
      "mpmc_queue_pop" "t"
    ).

Class MpmcQueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_queue_G_history_G :: MonoListG Σ location ;
  #[local] mpmc_queue_G_front_G :: AuthNatMaxG Σ ;
  #[local] mpmc_queue_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] mpmc_queue_G_waiters_G :: ghost_mapG Σ gname nat ;
  #[local] mpmc_queue_G_saved_pred_G :: SavedPredG Σ bool ;
}.

Definition mpmc_queue_Σ := #[
  mono_list_Σ location ;
  auth_nat_max_Σ ;
  twins_Σ (leibnizO (list val)) ;
  ghost_mapΣ gname nat ;
  saved_pred_Σ bool
].
#[global] Instance subG_mpmc_queue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_queue_Σ Σ →
  MpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Section mpmc_queue_G.
  Context `{mpmc_queue_G : MpmcQueueG Σ}.

  Record mpmc_queue_meta := {
    mpmc_queue_meta_history : gname ;
    mpmc_queue_meta_front : gname ;
    mpmc_queue_meta_model : gname ;
    mpmc_queue_meta_waiters : gname ;
  }.

  #[local] Instance mpmc_queue_meta_eq_dec : EqDecision mpmc_queue_meta :=
    ltac:(solve_decision).
  #[local] Instance mpmc_queue_meta_countable :
    Countable mpmc_queue_meta.
  Proof.
    pose encode γ := (
      γ.(mpmc_queue_meta_history),
      γ.(mpmc_queue_meta_front),
      γ.(mpmc_queue_meta_model),
      γ.(mpmc_queue_meta_waiters)
    ).
    pose decode := λ '(γ_history, γ_front, γ_model, γ_waiters), {|
      mpmc_queue_meta_history := γ_history ;
      mpmc_queue_meta_front := γ_front ;
      mpmc_queue_meta_model := γ_model ;
      mpmc_queue_meta_waiters := γ_waiters ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpmc_queue_history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition mpmc_queue_history_auth γ hist :=
    mpmc_queue_history_auth' γ.(mpmc_queue_meta_history) hist.
  #[local] Definition mpmc_queue_history_elem γ i node :=
    mono_list_elem γ.(mpmc_queue_meta_history) i node.

  #[local] Definition mpmc_queue_front_auth' γ_front i :=
    auth_nat_max_auth γ_front (DfracOwn 1) i.
  #[local] Definition mpmc_queue_front_auth γ i :=
    mpmc_queue_front_auth' γ.(mpmc_queue_meta_front) i.
  #[local] Definition mpmc_queue_front_lb γ i :=
    auth_nat_max_lb γ.(mpmc_queue_meta_front) i.

  #[local] Definition mpmc_queue_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition mpmc_queue_model₁ γ vs :=
    mpmc_queue_model₁' γ.(mpmc_queue_meta_model) vs.
  #[local] Definition mpmc_queue_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition mpmc_queue_model₂ γ vs :=
    mpmc_queue_model₂' γ.(mpmc_queue_meta_model) vs.

  #[local] Definition mpmc_queue_waiters_auth' γ_waiters waiters :=
    ghost_map_auth γ_waiters 1 waiters.
  #[local] Definition mpmc_queue_waiters_auth γ waiters :=
    mpmc_queue_waiters_auth' γ.(mpmc_queue_meta_waiters) waiters.
  #[local] Definition mpmc_queue_waiters_frag γ waiter i :=
    ghost_map_elem γ.(mpmc_queue_meta_waiters) waiter (DfracOwn 1) i.

  #[local] Definition mpmc_queue_waiter_au γ ι (Ψ : bool → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ vs,
      mpmc_queue_model₁ γ vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      mpmc_queue_model₁ γ vs
    , COMM
      Ψ (bool_decide (vs = []))
    }>.
  #[local] Definition mpmc_queue_waiter γ ι past waiter i : iProp Σ :=
    ∃ Ψ,
    saved_pred waiter Ψ ∗
    if decide (i < length past) then
      Ψ false
    else
      mpmc_queue_waiter_au γ ι Ψ.

  #[local] Definition mpmc_queue_inv_inner l γ ι : iProp Σ :=
    ∃ hist past front nodes back vs waiters,
    ⌜hist = past ++ front :: nodes⌝ ∗
    ⌜back ∈ hist⌝ ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    xchain_model hist () ∗
    ([∗ list] node; v ∈ nodes; vs, node.[xchain_data] ↦ v) ∗
    mpmc_queue_history_auth γ hist ∗
    mpmc_queue_front_auth γ (length past) ∗
    mpmc_queue_model₂ γ vs ∗
    mpmc_queue_waiters_auth γ waiters ∗
    [∗ map] waiter ↦ i ∈ waiters,
      mpmc_queue_waiter γ ι past waiter i.
  Definition mpmc_queue_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (mpmc_queue_inv_inner l γ ι).

  Definition mpmc_queue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    mpmc_queue_model₁ γ vs.

  #[global] Instance mpmc_queue_model_timeless t vs :
    Timeless (mpmc_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_queue_inv_persistent t ι :
    Persistent (mpmc_queue_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma mpmc_queue_history_alloc front :
    ⊢ |==>
      ∃ γ_hist,
      mpmc_queue_history_auth' γ_hist [front].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma mpmc_queue_history_elem_get {γ hist} i node :
    hist !! i = Some node →
    mpmc_queue_history_auth γ hist ⊢
    mpmc_queue_history_elem γ i node.
  Proof.
    setoid_rewrite mono_list_lb_get. apply mono_list_elem_get.
  Qed.
  #[local] Lemma mpmc_queue_history_agree γ hist i node :
    mpmc_queue_history_auth γ hist -∗
    mpmc_queue_history_elem γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list_lookup.
  Qed.
  #[local] Lemma mpmc_queue_history_update {γ hist} node :
    mpmc_queue_history_auth γ hist ⊢ |==>
    mpmc_queue_history_auth γ (hist ++ [node]).
  Proof.
    apply mono_list_update_app.
  Qed.

  #[local] Lemma mpmc_queue_front_alloc :
    ⊢ |==>
      ∃ γ_front,
      mpmc_queue_front_auth' γ_front 0.
  Proof.
    apply auth_nat_max_alloc.
  Qed.
  #[local] Lemma mpmc_queue_front_lb_get γ i :
    mpmc_queue_front_auth γ i ⊢
    mpmc_queue_front_lb γ i.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma mpmc_queue_front_lb_valid γ i1 i2 :
    mpmc_queue_front_auth γ i1 -∗
    mpmc_queue_front_lb γ i2 -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.
  #[local] Lemma mpmc_queue_front_update {γ i} i' :
    i ≤ i' →
    mpmc_queue_front_auth γ i ⊢ |==>
    mpmc_queue_front_auth γ i'.
  Proof.
    apply auth_nat_max_update.
  Qed.

  #[local] Lemma mpmc_queue_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      mpmc_queue_model₁' γ_model [] ∗
      mpmc_queue_model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpmc_queue_model_agree γ model1 model2 :
    mpmc_queue_model₁ γ model1 -∗
    mpmc_queue_model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpmc_queue_model_update {γ vs1 vs2} vs :
    mpmc_queue_model₁ γ vs1 -∗
    mpmc_queue_model₂ γ vs2 ==∗
      mpmc_queue_model₁ γ vs ∗
      mpmc_queue_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  #[local] Lemma mpmc_queue_waiters_alloc :
    ⊢ |==>
      ∃ γ_waiters,
      mpmc_queue_waiters_auth' γ_waiters ∅.
  Proof.
    iMod ghost_map_alloc as "(%γ_waiters & Hwaiters_auth & _)".
    iSteps.
  Qed.
  #[local] Lemma mpmc_queue_waiters_lookup γ waiters waiter i :
    mpmc_queue_waiters_auth γ waiters -∗
    mpmc_queue_waiters_frag γ waiter i -∗
    ⌜waiters !! waiter = Some i⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma mpmc_queue_waiters_insert {γ waiters} waiter i :
    waiters !! waiter = None →
    mpmc_queue_waiters_auth γ waiters ⊢ |==>
      mpmc_queue_waiters_auth γ (<[waiter := i]> waiters) ∗
      mpmc_queue_waiters_frag γ waiter i.
  Proof.
    iIntros "%Hlookup Hwaiters_auth".
    iApply (ghost_map_insert with "Hwaiters_auth"); first done.
  Qed.
  #[local] Lemma mpmc_queue_waiters_delete γ waiters waiter i :
    mpmc_queue_waiters_auth γ waiters -∗
    mpmc_queue_waiters_frag γ waiter i ==∗
      mpmc_queue_waiters_auth γ (delete waiter waiters).
  Proof.
    apply ghost_map_delete.
  Qed.

  Lemma mpmc_queue_create_spec ι :
    {{{ True }}}
      mpmc_queue_create ()
    {{{ t,
      RET t;
      mpmc_queue_inv t ι ∗
      mpmc_queue_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_block front as "(Hfront_next & _)".
    wp_block l as "Hmeta" "(Hl_front & Hl_back & _)".

    iMod mpmc_queue_history_alloc as "(%γ_history & Hhistory_auth)".
    iMod mpmc_queue_front_alloc as "(%γ_front & Hfront_auth)".
    iMod mpmc_queue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod mpmc_queue_waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ := {|
      mpmc_queue_meta_history := γ_history ;
      mpmc_queue_meta_front := γ_front ;
      mpmc_queue_meta_model := γ_model ;
      mpmc_queue_meta_waiters := γ_waiters ;
    |}.

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc.
    iExists [front], [], front, [], front, [], ∅. iFrame. iSteps.
    - rewrite elem_of_list_singleton //.
    - rewrite big_sepM_empty //.
  Qed.

  #[local] Lemma mpmc_queue_front_spec_strong au Ψ l γ ι :
    {{{
      inv ι (mpmc_queue_inv_inner l γ ι) ∗
      if negb au then True else
        mpmc_queue_waiter_au γ ι Ψ
    }}}
      !#l.[front]
    {{{ front i,
      RET #front;
      mpmc_queue_history_elem γ i front ∗
      mpmc_queue_front_lb γ i ∗
      if negb au then True else
        ∃ waiter,
        saved_pred waiter Ψ ∗
        mpmc_queue_waiters_frag γ waiter i
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    wp_load.
    iDestruct (mpmc_queue_history_elem_get _ front with "Hhistory_auth") as "#Hhistory_elem".
    { rewrite Hhist list_lookup_middle //. }
    iDestruct (mpmc_queue_front_lb_get with "Hfront_auth") as "#Hfront_lb".
    destruct au.

    - iMod (saved_pred_alloc_cofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & #Hwaiter)".
      rewrite not_elem_of_dom in Hwaiter.
      iMod (mpmc_queue_waiters_insert _ (length past) with "Hwaiters_auth") as "(Hwaiter_auth & Hwaiters_frag)"; first done.
      iDestruct (big_sepM_insert_2 _ _ waiter (length past) with "[HΨ] Hwaiters") as "Hwaiters".
      { iExists Ψ. rewrite decide_False; first lia. iSteps. }
      iSplitR "Hwaiters_frag HΦ". { repeat iExists _. iSteps. }
      iSteps.

    - iSplitR "HΦ". { repeat iExists _. iSteps. }
      iSteps.
  Qed.
  #[local] Lemma mpmc_queue_front_spec l γ ι :
    {{{
      inv ι (mpmc_queue_inv_inner l γ ι)
    }}}
      !#l.[front]
    {{{ front i,
      RET #front;
      mpmc_queue_history_elem γ i front ∗
      mpmc_queue_front_lb γ i
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (mpmc_queue_front_spec_strong false inhabitant with "[$Hinv]").
    iSteps.
  Qed.

  #[local] Lemma mpmc_queue_back_spec l γ ι :
    {{{
      inv ι (mpmc_queue_inv_inner l γ ι)
    }}}
      !#l.[back]
    {{{ back i,
      RET #back;
      mpmc_queue_history_elem γ i back
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    wp_load.
    pose proof Hback as (i & Hlookup)%elem_of_list_lookup.
    iDestruct (mpmc_queue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_back"; first done.
    iSplitR "HΦ". { repeat iExists _. iSteps. }
    iSteps.
  Qed.

  Inductive mpmc_queue_op :=
    | MpmcQueueIsEmpty
    | MpmcQueuePop
    | MpmcQueueOther.
  #[local] Instance mpmc_queue_op_eq_dec : EqDecision mpmc_queue_op :=
    ltac:(solve_decision).

  #[local] Lemma mpmc_queue_xchain_next_spec_strong op TB waiter Ψ_is_empty β x Ψ_pop l γ ι i node :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_queue_inv_inner l γ ι) ∗
      mpmc_queue_history_elem γ i node ∗
      if decide (op = MpmcQueueOther) then True else
        mpmc_queue_front_lb γ i ∗
        if decide (op = MpmcQueueIsEmpty) then
          saved_pred waiter Ψ_is_empty ∗
          mpmc_queue_waiters_frag γ waiter i ∗
          £ 1
        else
          atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑ι) ∅ (tele_app $ mpmc_queue_model #l) β Ψ_pop ∗
          ( mpmc_queue_model #l [] -∗
            β [tele_arg []] x
          )
    }}}
      !#node.[xchain_next]
    {{{ res,
      RET res;
      ( ⌜res = ()%V⌝ ∗
        match op with
        | MpmcQueueIsEmpty =>
            Ψ_is_empty true
        | MpmcQueuePop =>
            Ψ_pop [tele_arg []] x
        | MpmcQueueOther =>
            True
        end
      ) ∨ (
        ∃ node',
        ⌜res = #node'⌝ ∗
        mpmc_queue_history_elem γ (S i) node' ∗
        match op with
        | MpmcQueueIsEmpty =>
            Ψ_is_empty false
        | MpmcQueuePop =>
            atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑ι) ∅ (tele_app $ mpmc_queue_model #l) β Ψ_pop
        | MpmcQueueOther =>
            True
        end
      )
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem & Hop) HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    iDestruct (mpmc_queue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup with "Hhist") as "(Hnode & Hhist)"; first done.
    wp_load.
    iDestruct ("Hhist" with "Hnode ") as "Hhist".
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (mpmc_queue_history_elem_get (S i) with "Hhistory_auth") as "#Hhistory_elem'"; first done.
      destruct op.

      + iDestruct "Hop" as "(#Hfront_lb & #Hwaiter & Hwaiters_frag & H£)".
        iDestruct (mpmc_queue_waiters_lookup with "Hwaiters_auth Hwaiters_frag") as %Hwaiters_lookup.
        iMod (mpmc_queue_waiters_delete with "Hwaiters_auth Hwaiters_frag") as "Hwaiters_auth".
        iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ & _Hwaiter & HΨ) & Hwaiters)"; first done.
        iDestruct (saved_pred_agree false with "Hwaiter _Hwaiter") as "HΨ_is_empty".
        iMod (lc_fupd_elim_later with "H£ HΨ_is_empty") as "HΨ_is_empty".
        destruct (decide (i = length past)) as [-> | Hi].

        * rewrite decide_False; first lia.
          iMod "HΨ" as "(%_vs & Hmodel₁ & _ & HΨ)".
          iDestruct (mpmc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".
          assert (nodes ≠ []) as Hnodes.
          { apply lookup_lt_Some in Hlookup'.
            rewrite Hhist app_length /= in Hlookup'.
            naive_solver lia.
          }
          iAssert ⌜vs ≠ []⌝%I as %Hvs.
          { destruct (decide (vs = [])) as [-> |]; last done.
            iDestruct (big_sepL2_length with "Hnodes") as %->%nil_length_inv.
            iSteps.
          }
          rewrite bool_decide_eq_false_2 //.
          iSplitR "HΨ_is_empty HΨ HΦ". { repeat iExists _. iFrame. iSteps. }
          iSteps. iRewrite "HΨ_is_empty". iSteps.

        * iDestruct (mpmc_queue_front_lb_valid with "Hfront_auth Hfront_lb") as %Hi_.
          rewrite decide_True; first lia.
          iSplitR "HΨ_is_empty HΨ HΦ". { repeat iExists _. iFrame. iSteps. }
          iSteps. iRewrite "HΨ_is_empty". iSteps.

      + iSplitR "Hop HΦ". { repeat iExists _. iSteps. }
        iSteps.

      + iSplitR "Hop HΦ". { repeat iExists _. iSteps. }
        iSteps.

    - destruct (decide (op = MpmcQueueOther)) as [-> | Hop].

      + iSplitR "HΦ". { repeat iExists _. iSteps. }
        iSteps.

      + iDestruct "Hop" as "(#Hfront_lb & Hop)".
        iDestruct (mpmc_queue_front_lb_valid with "Hfront_auth Hfront_lb") as %Hi.
        opose proof* lookup_last_length as Hlength; [done.. |].
        rewrite Hhist app_length /= in Hlength.
        assert (i = length past) as -> by lia.
        assert (length nodes = 0) as ->%nil_length_inv by lia.
        iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
        destruct op; last done.

        * iDestruct "Hop" as "(#Hwaiter & Hwaiters_frag & H£)".
          iDestruct (mpmc_queue_waiters_lookup with "Hwaiters_auth Hwaiters_frag") as %Hwaiters_lookup.
          iMod (mpmc_queue_waiters_delete with "Hwaiters_auth Hwaiters_frag") as "Hwaiters_auth".
          iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ & _Hwaiter & HΨ) & Hwaiters)"; first done.
          iDestruct (saved_pred_agree true with "Hwaiter _Hwaiter") as "HΨ_is_empty".
          iMod (lc_fupd_elim_later with "H£ HΨ_is_empty") as "HΨ_is_empty".
          rewrite decide_False; first lia.
          iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (mpmc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".
          iSplitR "HΨ_is_empty HΨ HΦ". { repeat iExists _. iFrame. iSteps. }
          iModIntro. clear.

          iApply "HΦ".
          iLeft. iRewrite "HΨ_is_empty". iSteps.

        * iDestruct "Hop" as "(HΨ & Hβ)".
          iMod "HΨ" as "(%vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΨ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (mpmc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iDestruct ("Hβ" with "[Hmodel₁]") as "Hβ"; first iSteps.
          iMod ("HΨ" with "Hβ") as "HΨ".
          iSplitR "HΨ HΦ". { repeat iExists _. iFrame. iSteps. }
          iSteps.
  Qed.
  #[local] Lemma mpmc_queue_xchain_next_spec l γ ι i node :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_queue_inv_inner l γ ι) ∗
      mpmc_queue_history_elem γ i node
    }}}
      !#node.[xchain_next]
    {{{ res,
      RET res;
        ⌜res = ()%V⌝
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        mpmc_queue_history_elem γ (S i) node'
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem) HΦ".
    wp_apply (mpmc_queue_xchain_next_spec_strong MpmcQueueOther TeleO inhabitant inhabitant inhabitant inhabitant inhabitant with "[$]").
    iSteps.
  Qed.

  Lemma mpmc_queue_is_empty_spec t ι :
    <<<
      mpmc_queue_inv t ι
    | ∀∀ vs,
      mpmc_queue_model t vs
    >>>
      mpmc_queue_is_empty t @ ↑ι
    <<<
      mpmc_queue_model t vs
    | RET #(bool_decide (vs = [])); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec credit:"H£".
    wp_smart_apply (mpmc_queue_front_spec_strong true (λ b, Φ #b) with "[$Hinv HΦ]") as (node i) "(#Hhistory_elem & #Hfront_lb & %waiter & #Hwaiter & Hwaiters_frag)".
    { rewrite /= /mpmc_queue_waiter_au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iAaccIntro with "Hmodel₁"; iSteps.
    }
    wp_smart_apply (mpmc_queue_xchain_next_spec_strong MpmcQueueIsEmpty [tele_pair bool] _ _ inhabitant [tele_arg true] inhabitant with "[$Hmeta $Hinv $Hhistory_elem $Hfront_lb $Hwaiter $Hwaiters_frag $H£]") as (res) "[(-> & HΦ) | (%node' & -> & #Hhistory_elem' & HΦ)]"; iSteps.
  Qed.

  #[local] Lemma mpmc_queue_do_push_spec l γ ι i node new_back v :
    <<<
      meta l nroot γ ∗
      inv ι (mpmc_queue_inv_inner l γ ι) ∗
      mpmc_queue_history_elem γ i node ∗
      new_back.[xchain_next] ↦ () ∗
      new_back.[xchain_data] ↦ v
    | ∀∀ vs,
      mpmc_queue_model #l vs
    >>>
      mpmc_queue_do_push #node #new_back @ ↑ι
    <<<
      mpmc_queue_model #l (vs ++ [v])
    | RET ();
      ∃ j,
      mpmc_queue_history_elem γ j new_back
    >>>.
  Proof.
    iIntros "!> %Φ (#Hmeta & #Hinv & #Hhistory_elem & Hnew_back_next & Hnew_back_data) HΦ".

    iLöb as "HLöb" forall (i node) "Hhistory_elem".

    wp_rec.
    wp_smart_apply (mpmc_queue_xchain_next_spec with "[$Hmeta $Hinv $Hhistory_elem]") as (res) "[-> | (%node' & -> & #Hhistory_elem')]"; last iSteps.
    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    iDestruct (mpmc_queue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup' with "Hhist") as "(Hhist1 & Hnode & Hhist2)"; first done.
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - wp_cas as _ | [=].
      iDestruct (xchain_model_lookup'_2 with "Hhist1 Hnode Hhist2") as "Hhist"; [done | rewrite Hlookup' // |].
      iSplitR "Hnew_back_next Hnew_back_data HΦ". { repeat iExists _. iSteps. }
      iSteps.

    - wp_cas as Hcas | _; first done.
      iDestruct (xchain_model_lookup'_2 with "Hhist1 Hnode []") as "Hhist"; [done | rewrite Hlookup' // | ..].
      { rewrite -(lookup_last_length hist i) // drop_all //. }
      iDestruct (big_sepL2_snoc with "[$Hnodes $Hnew_back_data]") as "Hnodes".
      iDestruct (xchain_model_snoc_2 with "Hhist Hnew_back_next") as "Hhist".
      iMod (mpmc_queue_history_update new_back with "Hhistory_auth") as "Hhistory_auth".
      iDestruct (mpmc_queue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_new_back".
      { rewrite lookup_snoc_Some. naive_solver. }
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (mpmc_queue_model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; [iSteps.. |].
      iSplitR "HΦ".
      { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
        iSteps; iPureIntro.
        - rewrite Hhist -assoc //.
        - rewrite elem_of_app. naive_solver.
      }
      iSteps.
  Qed.

  #[local] Lemma mpmc_queue_fix_back_spec l γ ι i back j new_back :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_queue_inv_inner l γ ι) ∗
      mpmc_queue_history_elem γ i back ∗
      mpmc_queue_history_elem γ j new_back
    }}}
      mpmc_queue_fix_back #l #back #new_back
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem_back & #Hhistory_elem_new_back) HΦ".

    iLöb as "HLöb" forall (i back) "Hhistory_elem_back".

    wp_rec. wp_pures.
    wp_bind (_ and _)%E.
    wp_apply (wp_wand _ _ (λ res, ∃ b, ⌜res = #b⌝)%I) as (res) "(%b & ->)".
    { wp_smart_apply (mpmc_queue_xchain_next_spec with "[$Hmeta $Hinv $Hhistory_elem_new_back]") as (res) "[-> | (%new_back' & -> & #Hhistory_elem_new_back')]"; last iSteps.
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%hist & %past & %front & %nodes & %back' & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
      wp_cas as _ | [= ->].
      2: iDestruct (mpmc_queue_history_agree with "Hhistory_auth Hhistory_elem_new_back") as %Hnew_back%elem_of_list_lookup_2.
      all: iSplitL; first (repeat iExists _; iSteps).
      all: iSteps.
    }
    destruct b; last iSteps.
    wp_smart_apply (mpmc_queue_back_spec with "Hinv") as (back' i') "#Hhistory_elem_back'".
    iApply ("HLöb" with "HΦ Hhistory_elem_back'").
  Qed.

  Lemma mpmc_queue_push_spec t ι v :
    <<<
      mpmc_queue_inv t ι
    | ∀∀ vs,
      mpmc_queue_model t vs
    >>>
      mpmc_queue_push t v @ ↑ι
    <<<
      mpmc_queue_model t (vs ++ [v])
    | RET (); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec.
    wp_block new_back as "(Hnew_back_next & Hnew_back_data & _)".
    wp_smart_apply (mpmc_queue_back_spec with "Hinv") as (back i) "#Hhistory_elem_back".
    wp_smart_apply (mpmc_queue_do_push_spec with "[$Hmeta $Hinv $Hhistory_elem_back $Hnew_back_next $Hnew_back_data]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_elem_new_back)".
    wp_smart_apply (mpmc_queue_fix_back_spec with "[$Hmeta $Hinv Hhistory_elem_back Hhistory_elem_new_back] HΦ").
    iSteps.
  Qed.

  Lemma mpmc_queue_pop_spec t ι :
    <<<
      mpmc_queue_inv t ι
    | ∀∀ vs,
      mpmc_queue_model t vs
    >>>
      mpmc_queue_pop t @ ↑ι
    <<<
      mpmc_queue_model t (tail vs)
    | RET head vs; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (mpmc_queue_front_spec with "Hinv") as (old_front i) "(#Hhistory_elem_old & #Hfront_lb_old)".
    wp_smart_apply (mpmc_queue_xchain_next_spec_strong MpmcQueuePop _ inhabitant inhabitant _ [tele_arg] with "[$Hmeta $Hinv $Hhistory_elem_old $Hfront_lb_old $HΦ]") as (res) "[(-> & HΦ) | (%front & -> & #Hhistory_elem & HΦ)]"; [iSteps.. |].
    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%hist & %past & %front' & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    iDestruct (mpmc_queue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup with "Hhist") as "(Hnode & Hhist)"; first done.
    wp_cas as _ | [= ->].
    all: iDestruct ("Hhist" with "Hnode ") as "Hhist".

    - iSplitR "HΦ". { repeat iExists _. iSteps. }
      iSteps.

    - iDestruct (mpmc_queue_history_agree with "Hhistory_auth Hhistory_elem_old") as %Hlookup_old.
      iAssert ⌜length past = i⌝%I as %Hpast_length.
      { iDestruct (xchain_model_NoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist list_lookup_middle //.
      }
      rewrite Hhist (assoc _ _ [_]) lookup_app_r app_length /= in Hlookup; first lia.
      rewrite Nat.add_1_r Hpast_length Nat.sub_diag in Hlookup.
      destruct nodes as [| node nodes]; first done. injection Hlookup as ->.
      rewrite (assoc _ _ [_]) in Hhist.
      iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hfront_data & Hnodes)".
      set past' := past ++ [old_front].
      iMod (mpmc_queue_front_update (length past') with "Hfront_auth") as "Hfront_auth".
      { rewrite app_length. lia. }
      iDestruct (big_sepM_impl_thread_fupd _ (mpmc_queue_waiter γ ι past')%I with "Hwaiters Hmodel₂ [#]") as ">(Hwaiters & Hmodel₂)".
      { iIntros "!> %waiter %j %Hlookup (%P & #Hwaiter & HP) Hmodel₂".
        destruct (Nat.lt_trichotomy j (length past)) as [Hj | [-> | Hj]].
        - rewrite decide_True //.
          rewrite /mpmc_queue_waiter. setoid_rewrite decide_True; last first.
          { rewrite app_length /=. lia. }
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /mpmc_queue_waiter. setoid_rewrite decide_True; last first.
          { rewrite app_length /=. lia. }
          iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
          iDestruct (mpmc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /mpmc_queue_waiter. setoid_rewrite decide_False; last first.
          { rewrite app_length /=. lia. }
          iSteps.
      }
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (mpmc_queue_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "Hfront_data HΦ". { repeat iExists _. iSteps. }
      iSteps.
  Qed.
End mpmc_queue_G.

#[global] Opaque mpmc_queue_create.
#[global] Opaque mpmc_queue_is_empty.
#[global] Opaque mpmc_queue_push.
#[global] Opaque mpmc_queue_pop.

#[global] Opaque mpmc_queue_inv.
#[global] Opaque mpmc_queue_model.
