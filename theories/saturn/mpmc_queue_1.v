(* Based on:
   https://github.com/ocaml-multicore/saturn/pull/122
*)

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.twins.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  option
  node2_schain
  node2_chain.
From zoo.saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types l front node back new_back : location.
Implicit Types past nodes : list location.
Implicit Types v t : val.
Implicit Types vs : list val.

#[local] Notation "'front'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'back'" := (
  in_type "t" 1
)(in custom zoo_field
).

Definition mpmc_queue_create : val :=
  λ: <>,
    let: "front" := node2_create () () in
    { "front"; "front" }.

Definition mpmc_queue_is_empty : val :=
  λ: "t",
    "t".{front}.{node2_next} = ().

#[local] Definition mpmc_queue_do_push : val :=
  rec: "mpmc_queue_do_push" "node" "new_back" :=
    let: "node'" := "node".{node2_next} in
    if: "node'" = () then (
      ifnot: Cas "node".[node2_next] () "new_back" then (
        Yield ;;
        "mpmc_queue_do_push" "node'" "new_back"
      )
    ) else (
      "mpmc_queue_do_push" "node'" "new_back"
    ).
#[local] Definition mpmc_queue_fix_back : val :=
  rec: "mpmc_queue_fix_back" "t" "back" "new_back" :=
    if: "new_back".{node2_next} = () and ~ Cas "t".[back] "back" "new_back" then (
      Yield ;;
      "mpmc_queue_fix_back" "t" "t".{back} "new_back"
    ).
Definition mpmc_queue_push : val :=
  λ: "t" "v",
    let: "new_back" := node2_create "v" () in
    let: "back" := "t".{back} in
    mpmc_queue_do_push "back" "new_back" ;;
    mpmc_queue_fix_back "t" "back" "new_back".

Definition mpmc_queue_pop : val :=
  rec: "mpmc_queue_pop" "t" :=
    let: "old_front" := "t".{front} in
    let: "front" := "old_front".{node2_next} in
    if: "front" = () then (
      §None
    ) else (
      if: Cas "t".[front] "old_front" "front" then (
        let: "v" := "front".{node2_data} in
        "front" <-{node2_data} () ;;
        ‘Some{ "v" }
      ) else (
        Yield ;;
        "mpmc_queue_pop" "t"
      )
    ).

Class MpmcQueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_queue_G_history_G :: MonoListG Σ location ;
  #[local] mpmc_queue_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpmc_queue_Σ := #[
  mono_list_Σ location ;
  twins_Σ (leibnizO (list val))
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
    mpmc_queue_meta_model : gname ;
  }.

  #[local] Instance mpmc_queue_meta_eq_dec : EqDecision mpmc_queue_meta :=
    ltac:(solve_decision).
  #[local] Instance mpmc_queue_meta_countable :
    Countable mpmc_queue_meta.
  Proof.
    pose encode γ := (
      γ.(mpmc_queue_meta_history),
      γ.(mpmc_queue_meta_model)
    ).
    pose decode := λ '(γ_history, γ_model), {|
      mpmc_queue_meta_history := γ_history ;
      mpmc_queue_meta_model := γ_model ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpmc_queue_history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition mpmc_queue_history_auth γ hist :=
    mpmc_queue_history_auth' γ.(mpmc_queue_meta_history) hist.
  #[local] Definition mpmc_queue_history_elem γ i node :=
    mono_list_elem γ.(mpmc_queue_meta_history) i node.

  #[local] Definition mpmc_queue_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition mpmc_queue_model₁ γ vs :=
    mpmc_queue_model₁' γ.(mpmc_queue_meta_model) vs.
  #[local] Definition mpmc_queue_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition mpmc_queue_model₂ γ vs :=
    mpmc_queue_model₂' γ.(mpmc_queue_meta_model) vs.

  #[local] Definition mpmc_queue_inv_inner l γ : iProp Σ :=
    ∃ past front nodes back vs,
    ⌜back ∈ past ++ front :: nodes⌝ ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    node2_schain (past ++ [front]) (from_option #@{location} ()%V $ head nodes) ∗
    node2_chain nodes vs () ∗
    mpmc_queue_history_auth γ (past ++ front :: nodes) ∗
    mpmc_queue_model₂ γ vs.
  Definition mpmc_queue_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (mpmc_queue_inv_inner l γ).

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

    wp_apply (node2_create_spec with "[//]") as (front) "Hfront".
    wp_record l as "Hmeta" "(Hl_front & Hl_back & _)".

    iMod mpmc_queue_history_alloc as "(%γ_history & Hhistory_auth)".
    iMod mpmc_queue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      mpmc_queue_meta_history := γ_history ;
      mpmc_queue_meta_model := γ_model ;
    |}.

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists [], front, [], front, []. iFrame. iSteps.
    - rewrite elem_of_list_singleton //.
    - iApply node2_chain_nil.
  Qed.

  Lemma mpmc_queue_is_empty_spec t ι :
    <<<
      mpmc_queue_inv t ι
    | ∀∀ vs,
      mpmc_queue_model t vs
    >>>
      mpmc_queue_is_empty t
    <<<
      mpmc_queue_model t vs
    | RET #(bool_decide (vs = [])); True
    >>>.
  Proof.
  Admitted.

  #[local] Lemma mpmc_queue_node2_next_spec l ι γ i node :
    {{{
      inv ι (mpmc_queue_inv_inner l γ) ∗
      mpmc_queue_history_elem γ i node
    }}}
      !#node.[node2_next]
    {{{ res,
      RET res;
        ⌜res = ()%V⌝
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        mpmc_queue_history_elem γ (S i) node'
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hhistory_elem) HΦ".

    iInv "Hinv" as "(%past & %front & %nodes & %back & %vs & >%Hback & Hl_front & Hl_back & >Hpast & Hnodes & >Hhistory_auth & Hmodel₂)".
    iDestruct (mpmc_queue_history_agree with "Hhistory_auth Hhistory_elem") as
      %[Hlookup | (_ & [(_ & <-) | (_ & Hlookup)]%lookup_cons_Some)]%lookup_app_Some.

    - wp_apply (node2_next_spec_schain_lookup with "Hpast") as "Hpast".
      { apply lookup_app_l_Some. done. }
      assert (∃ node', (past ++ [front]) !! S i = Some node') as (node' & Hlookup').
      { destruct (decide (S i = length past)).
        - rewrite list_lookup_middle //. naive_solver.
        - rewrite list_lookup_lookup_total_lt; last naive_solver.
          apply lookup_lt_Some in Hlookup. rewrite app_length. lia.
      }
      iDestruct (mpmc_queue_history_elem_get (S i) with "Hhistory_auth") as "#Hhistory_elem'".
      { rewrite (assoc _ _ [_]). apply lookup_app_l_Some. done. }
      rewrite Hlookup' /=. iSteps.

    - admit.

    - admit.
  Admitted.

  #[local] Lemma mpmc_queue_do_push_spec l ι γ i node new_back v :
    <<<
      meta l nroot γ ∗
      inv ι (mpmc_queue_inv_inner l γ) ∗
      mpmc_queue_history_elem γ i node ∗
      node2_model new_back v ()
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
    iIntros "!> %Φ (#Hmeta & #Hinv & #Hhistory_elem & Hnew_back) HΦ".

    iLöb as "HLöb" forall (i node) "Hhistory_elem".

    wp_rec.
    wp_smart_apply (mpmc_queue_node2_next_spec with "[$Hinv $Hhistory_elem]") as (res) "[-> | (%node' & -> & #Hhistory_elem')]"; last iSteps.
    wp_pures.

    wp_bind (Cas _ _ _).
    admit.
  Admitted.
  #[local] Lemma mpmc_queue_fix_back_spec l ι γ i back j new_back :
    {{{
      meta l nroot γ ∗
      inv ι (mpmc_queue_inv_inner l γ) ∗
      mpmc_queue_history_elem γ i back ∗
      mpmc_queue_history_elem γ j new_back
    }}}
      mpmc_queue_fix_back #l #back #new_back
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem_back & #Hhistory_elem_new_back) HΦ".

    iLöb as "HLöb".

    wp_rec.
    admit.
  Admitted.
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
    wp_smart_apply (node2_create_spec with "[//]") as (new_back) "Hnew_back".
    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%past & %front & %nodes & %back & %vs & >%Hback & Hfront & Hback & Hpast & Hnodes & Hhistory_auth & Hmodel₂)".
    wp_load.
    pose proof Hback as (i & Hlookup)%elem_of_list_lookup.
    iDestruct (mpmc_queue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_back"; first done.
    iSplitR "Hnew_back HΦ"; first iSteps.
    iModIntro. clear.

    wp_smart_apply (mpmc_queue_do_push_spec with "[$Hmeta $Hinv $Hhistory_elem_back $Hnew_back]").
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
  Admitted.
End mpmc_queue_G.

#[global] Opaque mpmc_queue_create.
#[global] Opaque mpmc_queue_is_empty.
#[global] Opaque mpmc_queue_push.
#[global] Opaque mpmc_queue_pop.

#[global] Opaque mpmc_queue_inv.
#[global] Opaque mpmc_queue_model.
