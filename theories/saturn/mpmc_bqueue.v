(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/83
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zoo Require Import
  prelude.
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
  rec: "mpmc_bqueue_do_push" "t" "back" "new_back" "cap" =>
    if: "cap" = #0 then (
      let: "cap" := "t".{capacity} - ("back".{xchain_index} - "t".{front}.{xchain_index}) in
      if: "cap" ≤ #0 then (
        #false
      ) else (
        "back" <-{xchain_capacity} "cap" ;;
        "mpmc_bqueue_do_push" "t" "back" "new_back" "cap"
      )
    ) else (
      "new_back" <-{xchain_capacity} "cap" - #1 ;;
      "new_back" <-{xchain_index} #1 + "back".{xchain_index} ;;
      if: CAS "back".[xchain_next] () "new_back" then (
        mpmc_bqueue_fix_back "t" "back" "new_back" ;;
        #true
      ) else (
        let: "back" := "back".{xchain_next} in
        "mpmc_bqueue_do_push" "t" "back" "new_back" "back".{xchain_capacity}
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
    ) else (
      if: CAS "t".[front] "old_front" "front" then (
        let: "v" := "front".{xchain_data} in
        "front" <-{xchain_data} () ;;
        ‘Some( "v" )
      ) else (
        Yield ;;
        "mpmc_bqueue_pop" "t"
      )
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
    ( [∗ list] i ↦ node ∈ past ++ front :: nodes,
      ∃ cap,
      ⌜i + cap ≤ length past + γ.(mpmc_bqueue_meta_capacity)⌝ ∗
      node.[xchain_index] ↦ #i ∗
      node.[xchain_capacity] ↦ #cap
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
    l.[capacity] ↦□ #cap ∗
    meta l nroot γ ∗
    inv ι (mpmc_bqueue_inv_inner l γ ι).

  Definition mpmc_bqueue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
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
    - iExists (Z.to_nat cap). iSteps. rewrite big_sepM_empty //.
  Qed.

  Lemma mpmc_bqueue_is_empty_spec t ι cap :
    <<<
      mpmc_bqueue_inv t ι cap
    | ∀∀ vs,
      mpmc_bqueue_model t vs
    >>>
      mpmc_bqueue_is_empty t
    <<<
      mpmc_bqueue_model t vs
    | RET #(bool_decide (vs = [])); True
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
    | RET #(bool_decide (length vs = cap)); True
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
    | RET head vs; True
    >>>.
  Proof.
  Admitted.
End mpmc_bqueue_G.

#[global] Opaque mpmc_bqueue_create.
#[global] Opaque mpmc_bqueue_capacity.
#[global] Opaque mpmc_bqueue_is_empty.
#[global] Opaque mpmc_bqueue_push.
#[global] Opaque mpmc_bqueue_pop.
