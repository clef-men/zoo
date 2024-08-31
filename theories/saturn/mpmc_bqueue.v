(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/83
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

#[local] Notation "'xchain_index'" := (
  in_type "node" 2
)(in custom zoo_field
).
#[local] Notation "'xchain_capacity'" := (
  in_type "node" 3
)(in custom zoo_field
).

#[local] Notation "'capacity'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'front'" := (
  in_type "t" 1
)(in custom zoo_field
).
#[local] Notation "'back'" := (
  in_type "t" 2
)(in custom zoo_field
).

Definition mpmc_bqueue_create : val :=
  fun: "cap" =>
    let: "front" := { (), (), #0, "cap" } in
    { "cap", "front", "front" }.

Definition mpmc_bqueue_capacity : val :=
  fun: "t" =>
    "t".{capacity}.

Definition mpmc_bqueue_is_empty : val :=
  fun: "t" =>
    "t".{front}.{xchain_next} = ().

#[local] Definition mpmc_bqueue_fix_back : val :=
  rec: "mpmc_bqueue_fix_back" "t" "back" "new_back" =>
    if: "new_back".{xchain_next} = () and ~ CAS "t".[back] "back" "new_back" then
      "mpmc_bqueue_fix_back" "t" "t".{back} "new_back".
#[local] Definition mpmc_bqueue_do_push : val :=
  rec: "mpmc_bqueue_do_push" "t" "node" "new_back" "cap" =>
    if: "cap" = #0 then (
      let: "cap" := "t".{capacity} - ("node".{xchain_index} - "t".{front}.{xchain_index}) in
      if: "cap" ≤ #0 then (
        #false
      ) else (
        "node" <-{xchain_capacity} "cap" ;;
        "mpmc_bqueue_do_push" "t" "node" "new_back" "cap"
      )
    ) else (
      "new_back" <-{xchain_capacity} "cap" - #1 ;;
      "new_back" <-{xchain_index} #1 + "node".{xchain_index} ;;
      let: "node'" := "node".{xchain_next} in
      if: "node'" = () then (
        if: CAS "node".[xchain_next] () "new_back" then (
          mpmc_bqueue_fix_back "t" "node" "new_back" ;;
          #true
        ) else (
          Yield ;;
          let: "node'" := "node".{xchain_next} in
          "mpmc_bqueue_do_push" "t" "node'" "new_back" "node'".{xchain_capacity}
        )
      ) else (
          "mpmc_bqueue_do_push" "t" "node'" "new_back" "node'".{xchain_capacity}
      )
    ).
Definition mpmc_bqueue_push : val :=
  fun: "t" "v" =>
    let: "new_back" := { (), "v", #0, #0 } in
    let: "back" := "t".{back} in
    mpmc_bqueue_do_push "t" "back" "new_back" "back".{xchain_capacity}.

Definition mpmc_bqueue_pop : val :=
  rec: "mpmc_bqueue_pop" "t" =>
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
      "mpmc_bqueue_pop" "t"
    ).

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

  Record mpmc_bqueue_meta := {
    mpmc_bqueue_meta_capacity : nat ;
    mpmc_bqueue_meta_history : gname ;
    mpmc_bqueue_meta_front : gname ;
    mpmc_bqueue_meta_model : gname ;
    mpmc_bqueue_meta_waiters : gname ;
  }.

  #[local] Instance mpmc_bqueue_meta_eq_dec : EqDecision mpmc_bqueue_meta :=
    ltac:(solve_decision).
  #[local] Instance mpmc_bqueue_meta_countable :
    Countable mpmc_bqueue_meta.
  Proof.
    pose encode γ := (
      γ.(mpmc_bqueue_meta_capacity),
      γ.(mpmc_bqueue_meta_history),
      γ.(mpmc_bqueue_meta_front),
      γ.(mpmc_bqueue_meta_model),
      γ.(mpmc_bqueue_meta_waiters)
    ).
    pose decode := λ '(cap, γ_history, γ_front, γ_model, γ_waiters), {|
      mpmc_bqueue_meta_capacity := cap ;
      mpmc_bqueue_meta_history := γ_history ;
      mpmc_bqueue_meta_front := γ_front ;
      mpmc_bqueue_meta_model := γ_model ;
      mpmc_bqueue_meta_waiters := γ_waiters ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpmc_bqueue_history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition mpmc_bqueue_history_auth γ hist :=
    mpmc_bqueue_history_auth' γ.(mpmc_bqueue_meta_history) hist.
  #[local] Definition mpmc_bqueue_history_elem γ i node :=
    mono_list_elem γ.(mpmc_bqueue_meta_history) i node.

  #[local] Definition mpmc_bqueue_front_auth' γ_front i :=
    auth_nat_max_auth γ_front (DfracOwn 1) i.
  #[local] Definition mpmc_bqueue_front_auth γ i :=
    mpmc_bqueue_front_auth' γ.(mpmc_bqueue_meta_front) i.
  #[local] Definition mpmc_bqueue_front_lb γ i :=
    auth_nat_max_lb γ.(mpmc_bqueue_meta_front) i.

  #[local] Definition mpmc_bqueue_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition mpmc_bqueue_model₁ γ vs :=
    mpmc_bqueue_model₁' γ.(mpmc_bqueue_meta_model) vs.
  #[local] Definition mpmc_bqueue_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition mpmc_bqueue_model₂ γ vs :=
    mpmc_bqueue_model₂' γ.(mpmc_bqueue_meta_model) vs.

  #[local] Definition mpmc_bqueue_waiters_auth' γ_waiters waiters :=
    ghost_map_auth γ_waiters 1 waiters.
  #[local] Definition mpmc_bqueue_waiters_auth γ waiters :=
    mpmc_bqueue_waiters_auth' γ.(mpmc_bqueue_meta_waiters) waiters.
  #[local] Definition mpmc_bqueue_waiters_frag γ waiter i :=
    ghost_map_elem γ.(mpmc_bqueue_meta_waiters) waiter (DfracOwn 1) i.

  #[local] Definition mpmc_bqueue_waiter_au γ ι (Ψ : bool → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ vs,
      mpmc_bqueue_model₁ γ vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      mpmc_bqueue_model₁ γ vs
    , COMM
      Ψ (bool_decide (vs = []))
    }>.
  #[local] Definition mpmc_bqueue_waiter γ ι past waiter i : iProp Σ :=
    ∃ Ψ,
    saved_pred waiter Ψ ∗
    if decide (i < length past) then
      Ψ false
    else
      mpmc_bqueue_waiter_au γ ι Ψ.

  #[local] Definition mpmc_bqueue_inv_inner l γ ι : iProp Σ :=
    ∃ hist past front nodes back vs waiters,
    ⌜hist = past ++ front :: nodes⌝ ∗
    ⌜back ∈ hist⌝ ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    xchain_model hist () ∗
    ( [∗ list] node; v ∈ nodes; vs,
      node.[xchain_data] ↦ v
    ) ∗
    ( [∗ list] i ↦ node ∈ hist,
      ∃ (cap : nat),
      node.[xchain_index] ↦□ #i ∗
      node.[xchain_capacity] ↦ #cap ∗
      ⌜i + cap ≤ length past + γ.(mpmc_bqueue_meta_capacity)⌝
    ) ∗
    mpmc_bqueue_history_auth γ hist ∗
    mpmc_bqueue_front_auth γ (length past) ∗
    mpmc_bqueue_model₂ γ vs ∗
    mpmc_bqueue_waiters_auth γ waiters ∗
    ( [∗ map] waiter ↦ i ∈ waiters,
      mpmc_bqueue_waiter γ ι past waiter i
    ).
  Definition mpmc_bqueue_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜cap = γ.(mpmc_bqueue_meta_capacity)⌝ ∗
    meta l nroot γ ∗
    l.[capacity] ↦□ #cap ∗
    inv ι (mpmc_bqueue_inv_inner l γ ι).

  Definition mpmc_bqueue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜length vs ≤ γ.(mpmc_bqueue_meta_capacity)⌝ ∗
    meta l nroot γ ∗
    mpmc_bqueue_model₁ γ vs.

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

  #[local] Lemma mpmc_bqueue_history_alloc front :
    ⊢ |==>
      ∃ γ_hist,
      mpmc_bqueue_history_auth' γ_hist [front].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma mpmc_bqueue_history_elem_get {γ hist} i node :
    hist !! i = Some node →
    mpmc_bqueue_history_auth γ hist ⊢
    mpmc_bqueue_history_elem γ i node.
  Proof.
    setoid_rewrite mono_list_lb_get. apply mono_list_elem_get.
  Qed.
  #[local] Lemma mpmc_bqueue_history_agree γ hist i node :
    mpmc_bqueue_history_auth γ hist -∗
    mpmc_bqueue_history_elem γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list_lookup.
  Qed.
  #[local] Lemma mpmc_bqueue_history_update {γ hist} node :
    mpmc_bqueue_history_auth γ hist ⊢ |==>
    mpmc_bqueue_history_auth γ (hist ++ [node]).
  Proof.
    apply mono_list_update_app.
  Qed.

  #[local] Lemma mpmc_bqueue_front_alloc :
    ⊢ |==>
      ∃ γ_front,
      mpmc_bqueue_front_auth' γ_front 0.
  Proof.
    apply auth_nat_max_alloc.
  Qed.
  #[local] Lemma mpmc_bqueue_front_lb_get γ i :
    mpmc_bqueue_front_auth γ i ⊢
    mpmc_bqueue_front_lb γ i.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma mpmc_bqueue_front_lb_valid γ i1 i2 :
    mpmc_bqueue_front_auth γ i1 -∗
    mpmc_bqueue_front_lb γ i2 -∗
    ⌜i2 ≤ i1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.
  #[local] Lemma mpmc_bqueue_front_update {γ i} i' :
    i ≤ i' →
    mpmc_bqueue_front_auth γ i ⊢ |==>
    mpmc_bqueue_front_auth γ i'.
  Proof.
    apply auth_nat_max_update.
  Qed.

  #[local] Lemma mpmc_bqueue_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      mpmc_bqueue_model₁' γ_model [] ∗
      mpmc_bqueue_model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpmc_bqueue_model_agree γ model1 model2 :
    mpmc_bqueue_model₁ γ model1 -∗
    mpmc_bqueue_model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpmc_bqueue_model_update {γ vs1 vs2} vs :
    mpmc_bqueue_model₁ γ vs1 -∗
    mpmc_bqueue_model₂ γ vs2 ==∗
      mpmc_bqueue_model₁ γ vs ∗
      mpmc_bqueue_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  #[local] Lemma mpmc_bqueue_waiters_alloc :
    ⊢ |==>
      ∃ γ_waiters,
      mpmc_bqueue_waiters_auth' γ_waiters ∅.
  Proof.
    iMod ghost_map_alloc as "(%γ_waiters & Hwaiters_auth & _)".
    iSteps.
  Qed.
  #[local] Lemma mpmc_bqueue_waiters_lookup γ waiters waiter i :
    mpmc_bqueue_waiters_auth γ waiters -∗
    mpmc_bqueue_waiters_frag γ waiter i -∗
    ⌜waiters !! waiter = Some i⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma mpmc_bqueue_waiters_insert {γ waiters} waiter i :
    waiters !! waiter = None →
    mpmc_bqueue_waiters_auth γ waiters ⊢ |==>
      mpmc_bqueue_waiters_auth γ (<[waiter := i]> waiters) ∗
      mpmc_bqueue_waiters_frag γ waiter i.
  Proof.
    iIntros "%Hlookup Hwaiters_auth".
    iApply (ghost_map_insert with "Hwaiters_auth"); first done.
  Qed.
  #[local] Lemma mpmc_bqueue_waiters_delete γ waiters waiter i :
    mpmc_bqueue_waiters_auth γ waiters -∗
    mpmc_bqueue_waiters_frag γ waiter i ==∗
      mpmc_bqueue_waiters_auth γ (delete waiter waiters).
  Proof.
    apply ghost_map_delete.
  Qed.

  Lemma mpmc_bqueue_model_valid t ι cap vs :
    mpmc_bqueue_inv t ι cap -∗
    mpmc_bqueue_model t vs -∗
    ⌜length vs ≤ cap⌝.
  Proof.
    iIntros "(%l & %γ & -> & -> & #Hmeta & #Hl_capacity & #Hinv) (%_l & %_γ & %Heq & %Hvs & #_Hmeta & Hmodel₁)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iSteps.
  Qed.

  Lemma mpmc_bqueue_create_spec ι cap :
    (0 ≤ cap)%Z →
    {{{ True }}}
      mpmc_bqueue_create #cap
    {{{ t,
      RET t;
      mpmc_bqueue_inv t ι (Z.to_nat cap) ∗
      mpmc_bqueue_model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.

    wp_block front as "(Hfront_next & Hfront_data & Hfront_index & Hfront_capacity & _)".
    iMod (pointsto_persist with "Hfront_index") as "#Hfront_index".
    wp_block l as "Hmeta" "(Hl_capacity & Hl_front & Hl_back & _)".
    iMod (pointsto_persist with "Hl_capacity") as "#Hcapacity".
    rewrite -{1 3}(Z2Nat.id cap) //.

    iMod mpmc_bqueue_history_alloc as "(%γ_history & Hhistory_auth)".
    iMod mpmc_bqueue_front_alloc as "(%γ_front & Hfront_auth)".
    iMod mpmc_bqueue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod mpmc_bqueue_waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ := {|
      mpmc_bqueue_meta_capacity := Z.to_nat cap ;
      mpmc_bqueue_meta_history := γ_history ;
      mpmc_bqueue_meta_front := γ_front ;
      mpmc_bqueue_meta_model := γ_model ;
      mpmc_bqueue_meta_waiters := γ_waiters ;
    |}.

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iExists l, γ. iStep 4. iApply inv_alloc.
    iExists [front], [], front, [], front, [], ∅. iFrame. iSteps.
    - rewrite elem_of_list_singleton //.
    - rewrite big_sepM_empty //.
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

  #[local] Lemma mpmc_bqueue_front_spec_strong au Ψ l γ ι :
    {{{
      inv ι (mpmc_bqueue_inv_inner l γ ι) ∗
      if negb au then True else
        mpmc_bqueue_waiter_au γ ι Ψ
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      mpmc_bqueue_history_elem γ i front ∗
      front.[xchain_index] ↦□ #i ∗
      mpmc_bqueue_front_lb γ i ∗
      if negb au then True else
        ∃ waiter,
        saved_pred waiter Ψ ∗
        mpmc_bqueue_waiters_frag γ waiter i
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    wp_load.
    assert (hist !! length past = Some front) as Hhist_lookup.
    { rewrite Hhist list_lookup_middle //. }
    iDestruct (mpmc_bqueue_history_elem_get _ front with "Hhistory_auth") as "#Hhistory_elem"; first done.
    iAssert (front.[xchain_index] ↦□ #(length past))%I as "#Hfront_index".
    { rewrite big_sepL_lookup //. iSteps. }
    iDestruct (mpmc_bqueue_front_lb_get with "Hfront_auth") as "#Hfront_lb".
    destruct au.

    - iMod (saved_pred_alloc_cofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & #Hwaiter)".
      rewrite not_elem_of_dom in Hwaiter.
      iMod (mpmc_bqueue_waiters_insert _ (length past) with "Hwaiters_auth") as "(Hwaiter_auth & Hwaiters_frag)"; first done.
      iDestruct (big_sepM_insert_2 _ _ waiter (length past) with "[HΨ] Hwaiters") as "Hwaiters".
      { iExists Ψ. rewrite decide_False; first lia. iSteps. }
      iSplitR "Hwaiters_frag HΦ". { repeat iExists _. iSteps. }
      iSteps.

    - iSplitR "HΦ". { repeat iExists _. iSteps. }
      iSteps.
  Qed.
  #[local] Lemma mpmc_bqueue_front_spec l γ ι :
    {{{
      inv ι (mpmc_bqueue_inv_inner l γ ι)
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      mpmc_bqueue_history_elem γ i front ∗
      front.[xchain_index] ↦□ #i ∗
      mpmc_bqueue_front_lb γ i
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (mpmc_bqueue_front_spec_strong false inhabitant with "[$Hinv]").
    iSteps.
  Qed.

  #[local] Lemma mpmc_bqueue_back_spec l γ ι :
    {{{
      inv ι (mpmc_bqueue_inv_inner l γ ι)
    }}}
      (#l).{back}
    {{{ back i,
      RET #back;
      mpmc_bqueue_history_elem γ i back ∗
      back.[xchain_index] ↦□ #i
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    wp_load.
    pose proof Hback as (i & Hlookup)%elem_of_list_lookup.
    iDestruct (mpmc_bqueue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_back"; first done.
    iAssert (back.[xchain_index] ↦□ #i)%I as "#Hback_index".
    { rewrite big_sepL_lookup //. iSteps. }
    iSplitR "HΦ". { repeat iExists _. iSteps. }
    iSteps.
  Qed.

  Inductive mpmc_bqueue_op :=
    | MpmcQueueIsEmpty
    | MpmcQueuePop
    | MpmcQueueOther.
  #[local] Instance mpmc_bqueue_op_eq_dec : EqDecision mpmc_bqueue_op :=
    ltac:(solve_decision).

  #[local] Lemma mpmc_bqueue_xchain_next_spec_strong op TB waiter Ψ_is_empty β x Ψ_pop l γ ι i node :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_bqueue_inv_inner l γ ι) ∗
      mpmc_bqueue_history_elem γ i node ∗
      if decide (op = MpmcQueueOther) then True else
        mpmc_bqueue_front_lb γ i ∗
        if decide (op = MpmcQueueIsEmpty) then
          saved_pred waiter Ψ_is_empty ∗
          mpmc_bqueue_waiters_frag γ waiter i ∗
          £ 1
        else
          atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑ι) ∅ (tele_app $ mpmc_bqueue_model #l) β Ψ_pop ∗
          ( mpmc_bqueue_model #l [] -∗
            β [tele_arg []] x
          )
    }}}
      (#node).{xchain_next}
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
        mpmc_bqueue_history_elem γ (S i) node' ∗
        node'.[xchain_index] ↦□ #(S i) ∗
        match op with
        | MpmcQueueIsEmpty =>
            Ψ_is_empty false
        | MpmcQueuePop =>
            atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑ι) ∅ (tele_app $ mpmc_bqueue_model #l) β Ψ_pop
        | MpmcQueueOther =>
            True
        end
      )
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem & Hop) HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    iDestruct (mpmc_bqueue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup_acc with "Hhist") as "(Hnode & Hhist)"; first done.
    wp_load.
    iDestruct ("Hhist" with "Hnode ") as "Hhist".
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (mpmc_bqueue_history_elem_get (S i) with "Hhistory_auth") as "#Hhistory_elem'"; first done.
      iAssert (node'.[xchain_index] ↦□ #(S i))%I as "#Hnode'_index".
      { rewrite big_sepL_lookup //. iSteps. }
      destruct op.

      + iDestruct "Hop" as "(#Hfront_lb & #Hwaiter & Hwaiters_frag & H£)".
        iDestruct (mpmc_bqueue_waiters_lookup with "Hwaiters_auth Hwaiters_frag") as %Hwaiters_lookup.
        iMod (mpmc_bqueue_waiters_delete with "Hwaiters_auth Hwaiters_frag") as "Hwaiters_auth".
        iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ & _Hwaiter & HΨ) & Hwaiters)"; first done.
        iDestruct (saved_pred_agree false with "Hwaiter _Hwaiter") as "HΨ_is_empty".
        iMod (lc_fupd_elim_later with "H£ HΨ_is_empty") as "HΨ_is_empty".
        destruct (decide (i = length past)) as [-> | Hi].

        * rewrite decide_False; first lia.
          iMod "HΨ" as "(%_vs & Hmodel₁ & _ & HΨ)".
          iDestruct (mpmc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
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

        * iDestruct (mpmc_bqueue_front_lb_valid with "Hfront_auth Hfront_lb") as %Hi_.
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
        iDestruct (mpmc_bqueue_front_lb_valid with "Hfront_auth Hfront_lb") as %Hi.
        opose proof* lookup_last_length as Hlength; [done.. |].
        rewrite Hhist app_length /= in Hlength.
        assert (i = length past) as -> by lia.
        assert (length nodes = 0) as ->%nil_length_inv by lia.
        iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
        destruct op; last done.

        * iDestruct "Hop" as "(#Hwaiter & Hwaiters_frag & H£)".
          iDestruct (mpmc_bqueue_waiters_lookup with "Hwaiters_auth Hwaiters_frag") as %Hwaiters_lookup.
          iMod (mpmc_bqueue_waiters_delete with "Hwaiters_auth Hwaiters_frag") as "Hwaiters_auth".
          iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ & _Hwaiter & HΨ) & Hwaiters)"; first done.
          iDestruct (saved_pred_agree true with "Hwaiter _Hwaiter") as "HΨ_is_empty".
          iMod (lc_fupd_elim_later with "H£ HΨ_is_empty") as "HΨ_is_empty".
          rewrite decide_False; first lia.
          iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (mpmc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".
          iSplitR "HΨ_is_empty HΨ HΦ". { repeat iExists _. iFrame. iSteps. }
          iModIntro. clear.

          iApply "HΦ".
          iLeft. iRewrite "HΨ_is_empty". iSteps.

        * iDestruct "Hop" as "(HΨ & Hβ)".
          iMod "HΨ" as "(%vs & (%_l & %_γ & %Heq & %Hvs & #_Hmeta & Hmodel₁) & _ & HΨ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (mpmc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iDestruct ("Hβ" with "[Hmodel₁]") as "Hβ"; first iSteps.
          iMod ("HΨ" with "Hβ") as "HΨ".
          iSplitR "HΨ HΦ". { repeat iExists _. iFrame. iSteps. }
          iSteps.
  Qed.
  #[local] Lemma mpmc_bqueue_xchain_next_spec l γ ι i node :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_bqueue_inv_inner l γ ι) ∗
      mpmc_bqueue_history_elem γ i node
    }}}
      (#node).{xchain_next}
    {{{ res,
      RET res;
        ⌜res = ()%V⌝
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        mpmc_bqueue_history_elem γ (S i) node' ∗
        node'.[xchain_index] ↦□ #(S i)
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem) HΦ".
    wp_apply (mpmc_bqueue_xchain_next_spec_strong MpmcQueueOther TeleO inhabitant inhabitant inhabitant inhabitant inhabitant with "[$]").
    iSteps.
  Qed.

  #[local] Lemma mpmc_bqueue_xchain_capacity l γ ι i node:
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_bqueue_inv_inner l γ ι) ∗
      mpmc_bqueue_history_elem γ i node
    }}}
      (#node).{xchain_capacity}
    {{{ cap j,
      RET #cap;
      ⌜i + cap ≤ j + γ.(mpmc_bqueue_meta_capacity)⌝ ∗
      mpmc_bqueue_front_lb γ j
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem) HΦ".
    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    iDestruct (mpmc_bqueue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (big_sepL_lookup_acc with "Hindexing") as "((%cap & Hnode_index & Hnode_capacity & >%) & Hindexing)"; first done.
    wp_load.
    iDestruct (mpmc_bqueue_front_lb_get with "Hfront_auth") as "#Hfront_lb".
    iDestruct ("Hindexing" with "[Hnode_index Hnode_capacity]") as "Hindexing"; first iSteps.
    iSplitR "HΦ". { repeat iExists _. iFrame. iSteps. }
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
    | RET #(bool_decide (vs = []));
      True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & -> & #Hmeta & #Hl_capacity & #Hinv) HΦ".

    wp_rec credit:"H£".
    wp_smart_apply (mpmc_bqueue_front_spec_strong true (λ b, Φ #b) with "[$Hinv HΦ]") as (node i) "(#Hhistory_elem & #Hfront_index & #Hfront_lb & %waiter & #Hwaiter & Hwaiters_frag)".
    { rewrite /= /mpmc_bqueue_waiter_au. iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (%_l & %_γ & %Heq & %Hvs & #_Hmeta & Hmodel₁)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iAaccIntro with "Hmodel₁"; iSteps.
    }
    wp_smart_apply (mpmc_bqueue_xchain_next_spec_strong MpmcQueueIsEmpty [tele_pair bool] _ _ inhabitant [tele_arg true] inhabitant with "[$Hmeta $Hinv $Hhistory_elem $Hfront_lb $Hwaiter $Hwaiters_frag $H£]") as (res) "[(-> & HΦ) | (%node' & -> & #Hhistory_elem' & HΦ)]"; iSteps.
  Qed.

  #[local] Lemma mpmc_bqueue_fix_back_spec l γ ι i back j new_back :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_bqueue_inv_inner l γ ι) ∗
      mpmc_bqueue_history_elem γ i back ∗
      mpmc_bqueue_history_elem γ j new_back
    }}}
      mpmc_bqueue_fix_back #l #back #new_back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem_back & #Hhistory_elem_new_back) HΦ".

    iLöb as "HLöb" forall (i back) "Hhistory_elem_back".

    wp_rec. wp_pures.
    wp_bind (_ and _)%E.
    wp_apply (wp_wand _ _ (λ res, ∃ b, ⌜res = #b⌝)%I) as (res) "(%b & ->)".
    { wp_smart_apply (mpmc_bqueue_xchain_next_spec with "[$Hmeta $Hinv $Hhistory_elem_new_back]") as (res) "[-> | (%new_back' & -> & #Hhistory_elem_new_back')]"; last iSteps.
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%hist & %past & %front & %nodes & %back' & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
      wp_cas as _ | [= ->].
      2: iDestruct (mpmc_bqueue_history_agree with "Hhistory_auth Hhistory_elem_new_back") as %Hnew_back%elem_of_list_lookup_2.
      all: iSplitL; first (repeat iExists _; iSteps).
      all: iSteps.
    }
    destruct b; last iSteps.
    wp_smart_apply (mpmc_bqueue_back_spec with "Hinv") as (back' i') "(#Hhistory_elem_back' & _)".
    iApply ("HLöb" with "HΦ Hhistory_elem_back'").
  Qed.

  #[local] Lemma mpmc_bqueue_do_push_spec l γ ι i node new_back (cap : nat) j v v_index :
    i + cap ≤ j + γ.(mpmc_bqueue_meta_capacity) →
    <<<
      meta l nroot γ ∗
      l.[capacity] ↦□ #γ.(mpmc_bqueue_meta_capacity) ∗
      inv ι (mpmc_bqueue_inv_inner l γ ι) ∗
      mpmc_bqueue_history_elem γ i node ∗
      node.[xchain_index] ↦□ #i ∗
      new_back.[xchain_next] ↦ () ∗
      new_back.[xchain_data] ↦ v ∗
      new_back.[xchain_index] ↦ v_index ∗
      new_back.[xchain_capacity] ↦ #cap ∗
      mpmc_bqueue_front_lb γ j
    | ∀∀ vs,
      mpmc_bqueue_model #l vs
    >>>
      mpmc_bqueue_do_push #l #node #new_back #cap @ ↑ι
    <<<
      ∃∃ b,
      if b then
        mpmc_bqueue_model #l (vs ++ [v])
      else
        mpmc_bqueue_model #l vs
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Hcap !> %Φ (#Hmeta & #Hl_capacity & #Hinv & #Hhistory_elem & #Hnode_index & Hnew_back_next & Hnew_back_data & Hnew_back_index & Hnew_back_capacity & #Hfront_lb) HΦ".

    iLöb as "HLöb" forall (i node cap Hcap) "Hhistory_elem Hnode_index".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - admit.

    - wp_store. wp_load. wp_store.
      wp_smart_apply (mpmc_bqueue_xchain_next_spec with "[$Hmeta $Hinv $Hhistory_elem]") as (res) "[-> | (%node' & -> & #Hhistory_elem')]".

      + wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
        iDestruct (mpmc_bqueue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
        iDestruct (xchain_model_lookup with "Hhist") as "(Hhist1 & Hnode & Hhist2)"; first done.
        destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

        * wp_cas as _ | [=].
          iDestruct (xchain_model_lookup_2 with "Hhist1 Hnode Hhist2") as "Hhist"; [done | rewrite Hlookup' // |].
          iSplitR "Hnew_back_next Hnew_back_data HΦ". { repeat iExists _. iSteps. }
          iSteps.

        * wp_cas as Hcas | _; first done.
          iDestruct (xchain_model_lookup_2 with "Hhist1 Hnode []") as "Hhist"; [done | rewrite Hlookup' // | ..].
          { rewrite -(lookup_last_length hist i) // drop_all //. }
          iDestruct (big_sepL2_snoc with "[$Hnodes $Hnew_back_data]") as "Hnodes".
          iDestruct (xchain_model_snoc_2 with "Hhist Hnew_back_next") as "Hhist".
          iMod (mpmc_bqueue_history_update new_back with "Hhistory_auth") as "Hhistory_auth".
          iDestruct (mpmc_bqueue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_new_back".
          { rewrite lookup_snoc_Some. naive_solver. }
          iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (mpmc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (mpmc_bqueue_model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; [iSteps.. |].
          iSplitR "HΦ".
          { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
            iSteps; iPureIntro.
            - rewrite Hhist -assoc //.
            - rewrite elem_of_app. naive_solver.
          }
          iSteps.
  Qed.

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
    iIntros "!> %Φ (%l & %γ & -> & -> & #Hmeta & #Hl_capacity & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (mpmc_bqueue_front_spec with "Hinv") as (old_front i) "(#Hhistory_elem_old & #Hfront_lb_old)".
    wp_smart_apply (mpmc_bqueue_xchain_next_spec_strong MpmcQueuePop _ inhabitant inhabitant _ [tele_arg] with "[$Hmeta $Hinv $Hhistory_elem_old $Hfront_lb_old $HΦ]") as (res) "[(-> & HΦ) | (%front & -> & #Hhistory_elem & HΦ)]"; [iSteps.. |].
    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%hist & %past & %front' & %nodes & %back & %vs & %waiters & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hindexing & >Hhistory_auth & Hfront_auth & Hmodel₂ & Hwaiters_auth & Hwaiters)".
    iDestruct (mpmc_bqueue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup_acc with "Hhist") as "(Hnode & Hhist)"; first done.
    wp_cas as _ | [= ->].
    all: iDestruct ("Hhist" with "Hnode ") as "Hhist".

    - iSplitR "HΦ". { repeat iExists _. iSteps. }
      iSteps.

    - iDestruct (mpmc_bqueue_history_agree with "Hhistory_auth Hhistory_elem_old") as %Hlookup_old.
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
      iMod (mpmc_bqueue_front_update (length past') with "Hfront_auth") as "Hfront_auth".
      { rewrite app_length. lia. }
      iDestruct (big_sepM_impl_thread_fupd _ (mpmc_bqueue_waiter γ ι past')%I with "Hwaiters Hmodel₂ [#]") as ">(Hwaiters & Hmodel₂)".
      { iIntros "!> %waiter %j %Hlookup (%P & #Hwaiter & HP) Hmodel₂".
        destruct (Nat.lt_trichotomy j (length past)) as [Hj | [-> | Hj]].
        - rewrite decide_True //.
          rewrite /mpmc_bqueue_waiter. setoid_rewrite decide_True; last first.
          { rewrite app_length /=. lia. }
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /mpmc_bqueue_waiter. setoid_rewrite decide_True; last first.
          { rewrite app_length /=. lia. }
          iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
          iDestruct (mpmc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /mpmc_bqueue_waiter. setoid_rewrite decide_False; last first.
          { rewrite app_length /=. lia. }
          iSteps.
      }
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_bqueue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (mpmc_bqueue_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "Hfront_data HΦ".
      { repeat iExists _. iFrame. iSteps.
        iApply (big_sepL_impl with "Hindexing").
        rewrite app_length. iSteps.
      }
      iSteps.
  Qed.
End mpmc_bqueue_G.

#[global] Opaque mpmc_bqueue_create.
#[global] Opaque mpmc_bqueue_capacity.
#[global] Opaque mpmc_bqueue_is_empty.
#[global] Opaque mpmc_bqueue_push.
#[global] Opaque mpmc_bqueue_pop.
