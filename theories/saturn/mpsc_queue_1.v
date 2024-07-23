From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.twins.
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

Definition mpsc_queue_create : val :=
  λ: <>,
    let: "front" := { (), () } in
    { "front", "front" }.

Definition mpsc_queue_is_empty : val :=
  λ: "t",
    "t".{front}.{xchain_next} = ().

#[local] Definition mpsc_queue_do_push : val :=
  rec: "mpsc_queue_do_push" "node" "new_back" :=
    let: "node'" := "node".{xchain_next} in
    if: "node'" = () then (
      ifnot: Cas "node".[xchain_next] () "new_back" then (
        Yield ;;
        "mpsc_queue_do_push" "node" "new_back"
      )
    ) else (
      "mpsc_queue_do_push" "node'" "new_back"
    ).
#[local] Definition mpsc_queue_fix_back : val :=
  rec: "mpsc_queue_fix_back" "t" "back" "new_back" :=
    if: "new_back".{xchain_next} = () and ~ Cas "t".[back] "back" "new_back" then (
      Yield ;;
      "mpsc_queue_fix_back" "t" "t".{back} "new_back"
    ).
Definition mpsc_queue_push : val :=
  λ: "t" "v",
    let: "new_back" := { (), "v" } in
    let: "back" := "t".{back} in
    mpsc_queue_do_push "back" "new_back" ;;
    mpsc_queue_fix_back "t" "back" "new_back".

Definition mpsc_queue_pop : val :=
  λ: "t",
    let: "front" := "t".{front}.{xchain_next} in
    if: "front" = () then (
      §None
    ) else (
      "t" <-{front} "front" ;;
      let: "v" := "front".{xchain_data} in
      "front" <-{xchain_data} () ;;
      ‘Some{ "v" }
    ).

Class MpscQueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpsc_queue_G_history_G :: MonoListG Σ location ;
  #[local] mpsc_queue_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpsc_queue_Σ := #[
  mono_list_Σ location ;
  twins_Σ (leibnizO (list val))
].
#[global] Instance subG_mpsc_queue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_queue_Σ Σ →
  MpscQueueG Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_G.
  Context `{mpsc_queue_G : MpscQueueG Σ}.

  Record mpsc_queue_meta := {
    mpsc_queue_meta_history : gname ;
    mpsc_queue_meta_model : gname ;
  }.

  #[local] Instance mpsc_queue_meta_eq_dec : EqDecision mpsc_queue_meta :=
    ltac:(solve_decision).
  #[local] Instance mpsc_queue_meta_countable :
    Countable mpsc_queue_meta.
  Proof.
    pose encode γ := (
      γ.(mpsc_queue_meta_history),
      γ.(mpsc_queue_meta_model)
    ).
    pose decode := λ '(γ_history, γ_model), {|
      mpsc_queue_meta_history := γ_history ;
      mpsc_queue_meta_model := γ_model ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpsc_queue_history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition mpsc_queue_history_auth γ hist :=
    mpsc_queue_history_auth' γ.(mpsc_queue_meta_history) hist.
  #[local] Definition mpsc_queue_history_elem γ i node :=
    mono_list_elem γ.(mpsc_queue_meta_history) i node.

  #[local] Definition mpsc_queue_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition mpsc_queue_model₁ γ vs :=
    mpsc_queue_model₁' γ.(mpsc_queue_meta_model) vs.
  #[local] Definition mpsc_queue_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition mpsc_queue_model₂ γ vs :=
    mpsc_queue_model₂' γ.(mpsc_queue_meta_model) vs.

  #[local] Definition mpsc_queue_inv_inner l γ : iProp Σ :=
    ∃ hist past front nodes back vs,
    ⌜hist = past ++ front :: nodes⌝ ∗
    ⌜back ∈ hist⌝ ∗
    l.[front] ↦{#1/4} #front ∗
    l.[back] ↦ #back ∗
    xchain_model hist () ∗
    ([∗ list] node; v ∈ nodes; vs, node.[xchain_data] ↦ v) ∗
    mpsc_queue_history_auth γ hist ∗
    mpsc_queue_model₂ γ vs.
  Definition mpsc_queue_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (mpsc_queue_inv_inner l γ).

  Definition mpsc_queue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    mpsc_queue_model₁ γ vs.

  Definition mpsc_queue_consumer t : iProp Σ :=
    ∃ l front,
    ⌜t = #l⌝ ∗
    l.[front] ↦{#3/4} #front.

  #[global] Instance mpsc_queue_model_timeless t vs :
    Timeless (mpsc_queue_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_consumer_timeless t :
    Timeless (mpsc_queue_consumer t ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_inv_persistent t ι :
    Persistent (mpsc_queue_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma mpsc_queue_history_alloc front :
    ⊢ |==>
      ∃ γ_hist,
      mpsc_queue_history_auth' γ_hist [front].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma mpsc_queue_history_elem_get {γ hist} i node :
    hist !! i = Some node →
    mpsc_queue_history_auth γ hist ⊢
    mpsc_queue_history_elem γ i node.
  Proof.
    setoid_rewrite mono_list_lb_get. apply mono_list_elem_get.
  Qed.
  #[local] Lemma mpsc_queue_history_agree γ hist i node :
    mpsc_queue_history_auth γ hist -∗
    mpsc_queue_history_elem γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list_lookup.
  Qed.
  #[local] Lemma mpsc_queue_history_update {γ hist} node :
    mpsc_queue_history_auth γ hist ⊢ |==>
    mpsc_queue_history_auth γ (hist ++ [node]).
  Proof.
    apply mono_list_update_app.
  Qed.

  #[local] Lemma mpsc_queue_model_alloc :
    ⊢ |==>
      ∃ γ_model,
      mpsc_queue_model₁' γ_model [] ∗
      mpsc_queue_model₂' γ_model [].
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpsc_queue_model_agree γ model1 model2 :
    mpsc_queue_model₁ γ model1 -∗
    mpsc_queue_model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpsc_queue_model_update {γ vs1 vs2} vs :
    mpsc_queue_model₁ γ vs1 -∗
    mpsc_queue_model₂ γ vs2 ==∗
      mpsc_queue_model₁ γ vs ∗
      mpsc_queue_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  #[local] Lemma mpsc_queue_inv_inner_history_elem ι l γ front :
    inv ι (mpsc_queue_inv_inner l γ) -∗
    l.[front] ↦{#3/4} #front ={⊤}=∗
      ∃ i,
      l.[front] ↦{#3/4} #front ∗
      mpsc_queue_history_elem γ i front.
  Proof.
    iIntros "#Hinv Hl_front_1".
    iInv "Hinv" as "(%hist & %past & %_front & %nodes & %back & %vs & >%Hhist & >%Hback & >Hl_front_2 & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hmodel₂)".
    iDestruct (pointsto_agree with "Hl_front_1 Hl_front_2") as %[= <-].
    iDestruct (mpsc_queue_history_elem_get (length past) front with "Hhistory_auth") as "#Hhistory_elem".
    { rewrite Hhist list_lookup_middle //. }
    iSplitR "Hl_front_1". { repeat iExists _. iSteps. }
    iSteps.
  Qed.

  Lemma mpsc_queue_consumer_exclusive t :
    mpsc_queue_consumer t -∗
    mpsc_queue_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %front & -> & Hl_front_1) (%_l & %_front & %Heq & Hl_front_2)". injection Heq as <-.
    iDestruct (pointsto_frac_ne with "Hl_front_1 Hl_front_2") as %?; naive_solver.
  Qed.

  Lemma mpsc_queue_create_spec ι :
    {{{ True }}}
      mpsc_queue_create ()
    {{{ t,
      RET t;
      mpsc_queue_inv t ι ∗
      mpsc_queue_model t [] ∗
      mpsc_queue_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_record front as "(Hfront_next & _)".
    wp_record l as "Hmeta" "(Hl_front & Hl_back & _)".
    iEval (rewrite -Qp.three_quarter_quarter) in "Hl_front".
    iDestruct "Hl_front" as "(Hl_front_1 & Hl_front_2)".

    iMod mpsc_queue_history_alloc as "(%γ_history & Hhistory_auth)".
    iMod mpsc_queue_model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      mpsc_queue_meta_history := γ_history ;
      mpsc_queue_meta_model := γ_model ;
    |}.

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hl_front_1"; last iSteps.
    iStep 2. iApply inv_alloc.
    iExists [front], [], front, [], front, []. iFrame. iSteps.
    rewrite elem_of_list_singleton //.
  Qed.

  #[local] Lemma mpsc_queue_front_spec l γ ι :
    {{{
      inv ι (mpsc_queue_inv_inner l γ)
    }}}
      !#l.[front]
    {{{ front i,
      RET #front;
      mpsc_queue_history_elem γ i front
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hhistory_auth & Hmodel₂)".
    wp_load.
    iDestruct (mpsc_queue_history_elem_get _ front with "Hhistory_auth") as "#Hhistory_elem".
    { rewrite Hhist list_lookup_middle //. }
    iSplitR "HΦ". { repeat iExists _. iSteps. }
    iSteps.
  Qed.

  #[local] Lemma mpsc_queue_back_spec l γ ι :
    {{{
      inv ι (mpsc_queue_inv_inner l γ)
    }}}
      !#l.[back]
    {{{ back i,
      RET #back;
      mpsc_queue_history_elem γ i back
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hhistory_auth & Hmodel₂)".
    wp_load.
    pose proof Hback as (i & Hlookup)%elem_of_list_lookup.
    iDestruct (mpsc_queue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_back"; first done.
    iSplitR "HΦ". { repeat iExists _. iSteps. }
    iSteps.
  Qed.

  Inductive mpsc_queue_op :=
    | MpscQueueIsEmpty
    | MpscQueuePop
    | MpscQueueOther.
  #[local] Instance mpsc_queue_op_eq_dec : EqDecision mpsc_queue_op :=
    ltac:(solve_decision).

  #[local] Lemma mpsc_queue_xchain_next_spec_strong op TB β x_empty x_nonempty Ψ l γ ι i node :
    {{{
      meta l nroot γ ∗
      inv ι (mpsc_queue_inv_inner l γ) ∗
      mpsc_queue_history_elem γ i node ∗
      if decide (op = MpscQueueOther) then True else
        l.[front] ↦{#3/4} #node ∗
        atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑ι) ∅ (tele_app $ mpsc_queue_model #l) β Ψ ∗
        ( mpsc_queue_model #l [] -∗
          β [tele_arg []] x_empty
        ) ∗
        if decide (op = MpscQueuePop) then True else
          ∀ vs,
          ⌜vs ≠ []⌝ -∗
          mpsc_queue_model #l vs -∗
          β (TeleArgCons vs ()) x_nonempty
    }}}
      !#node.[xchain_next]
    {{{ res,
      RET res;
      ( ⌜res = ()%V⌝ ∗
        if decide (op = MpscQueueOther) then True else
          l.[front] ↦{#3/4} #node ∗
          Ψ [tele_arg []] x_empty
      ) ∨ (
        ∃ node',
        ⌜res = #node'⌝ ∗
        mpsc_queue_history_elem γ (S i) node' ∗
        if decide (op = MpscQueueOther) then True else
          l.[front] ↦{#3/4} #node ∗
          if decide (op = MpscQueueIsEmpty) then
            ∃ vs, Ψ (TeleArgCons vs ()) x_nonempty
          else
            atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑ι) ∅ (tele_app $ mpsc_queue_model #l) β Ψ
      )
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem & Hop) HΦ".

    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & >%Hhist & >%Hback & Hl_front_2 & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hmodel₂)".
    iDestruct (mpsc_queue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup with "Hhist") as "(Hnode & Hhist)"; first done.
    wp_load.
    iDestruct ("Hhist" with "Hnode ") as "Hhist".
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (mpsc_queue_history_elem_get (S i) with "Hhistory_auth") as "#Hhistory_elem'"; first done.
      destruct (decide (op = MpscQueueIsEmpty)) as [-> | Hop].

      + iDestruct "Hop" as "(Hl_front_1 & HΨ & Hβ_empty & Hβ_nonempty)".
        iDestruct (pointsto_agree with "Hl_front_1 Hl_front_2") as %[= ->].
        iMod "HΨ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
        iDestruct ("Hβ_nonempty" with "[#] [Hmodel₁]") as "Hβ"; [| iSteps |].
        { iAssert ⌜length past = i⌝%I as %Hpast_length.
          { iDestruct (xchain_model_NoDup with "Hhist") as %Hnodup.
            iPureIntro. eapply NoDup_lookup; try done.
            rewrite Hhist list_lookup_middle //.
          }
          rewrite -length_zero_iff_nil.
          iDestruct (big_sepL2_length with "Hnodes") as %<-.
          iIntros "%Hnodes_length". iPureIntro.
          apply (f_equal length) in Hhist as Hhist_length.
          rewrite app_length /= in Hhist_length.
          apply lookup_lt_Some in Hlookup'.
          lia.
        }
        iMod ("HΨ" $! x_nonempty with "Hβ") as "HΨ".
        iSplitR "Hl_front_1 HΨ HΦ". { repeat iExists _. iSteps. }
        iSteps.

      + iSplitR "Hop HΦ". { repeat iExists _. iSteps. }
        destruct op; [done | iSteps..].

    - destruct (decide (op = MpscQueueOther)) as [-> | Hop].

      + iSplitR "HΦ". { repeat iExists _. iSteps. }
        iSteps.

      + iDestruct "Hop" as "(Hl_front_1 & HΨ & Hβ_empty & _)".
        iDestruct (pointsto_agree with "Hl_front_1 Hl_front_2") as %[= ->].
        iAssert ⌜length past = i⌝%I as %Hpast_length.
        { iDestruct (xchain_model_NoDup with "Hhist") as %Hnodup.
          iPureIntro. eapply NoDup_lookup; try done.
          rewrite Hhist list_lookup_middle //.
        }
        destruct (decide (length vs = 0)) as [->%nil_length_inv | Hvs]; last first.
        { iDestruct (big_sepL2_length with "Hnodes") as %?.
          exfalso.
          apply (f_equal length) in Hhist.
          opose proof* lookup_last_length as Heq; [done.. |].
          rewrite Heq app_length /= in Hhist. lia.
        }
        iMod "HΨ" as "(%vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
        iDestruct ("Hβ_empty" with "[Hmodel₁]") as "Hβ"; first iSteps.
        iMod ("HΨ" with "Hβ") as "HΨ".
        iSplitR "Hl_front_1 HΨ HΦ". { repeat iExists _. iSteps. }
        iSteps.
  Qed.
  #[local] Lemma mpsc_queue_xchain_next_spec l γ ι i node :
    {{{
      meta l nroot γ ∗
      inv ι (mpsc_queue_inv_inner l γ) ∗
      mpsc_queue_history_elem γ i node
    }}}
      !#node.[xchain_next]
    {{{ res,
      RET res;
        ⌜res = ()%V⌝
      ∨ ∃ node',
        ⌜res = #node'⌝ ∗
        mpsc_queue_history_elem γ (S i) node'
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem) HΦ".
    wp_apply (mpsc_queue_xchain_next_spec_strong MpscQueueOther TeleO inhabitant inhabitant inhabitant inhabitant with "[$Hmeta $Hinv $Hhistory_elem //]").
    iSteps.
  Qed.

  Lemma mpsc_queue_is_empty_spec t ι :
    <<<
      mpsc_queue_inv t ι ∗
      mpsc_queue_consumer t
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_is_empty t @ ↑ι
    <<<
      mpsc_queue_model t vs
    | RET #(bool_decide (vs = []));
      mpsc_queue_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %front & %Heq & Hl_front)) HΦ". injection Heq as <-.

    iMod (mpsc_queue_inv_inner_history_elem with "Hinv Hl_front") as "(%i & Hl_front & #Hhistory_elem)".

    iAssert (
      AU <{
        ∃∃ vs,
        mpsc_queue_model #l vs
      }> @ ⊤ ∖ ↑ι, ∅ <{
        ∀∀ b,
        ⌜b = bool_decide (vs = [])⌝ ∗
        mpsc_queue_model #l vs
      , COMM
        mpsc_queue_consumer #l -∗
        Φ #b
      }>
    )%I with "[HΦ]" as "HΦ".
    { iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; iSteps.
    }

    wp_rec. wp_load. wp_pures.
    wp_smart_apply (mpsc_queue_xchain_next_spec_strong MpscQueueIsEmpty [tele_pair bool] _ [tele_arg true] [tele_arg false] with "[$Hmeta $Hinv $Hhistory_elem $Hl_front $HΦ]"); last iSteps.
    iSplitR; iSteps.
  Qed.

  #[local] Lemma mpsc_queue_do_push_spec l γ ι i node new_back v :
    <<<
      meta l nroot γ ∗
      inv ι (mpsc_queue_inv_inner l γ) ∗
      mpsc_queue_history_elem γ i node ∗
      new_back.[xchain_next] ↦ () ∗
      new_back.[xchain_data] ↦ v
    | ∀∀ vs,
      mpsc_queue_model #l vs
    >>>
      mpsc_queue_do_push #node #new_back @ ↑ι
    <<<
      mpsc_queue_model #l (vs ++ [v])
    | RET ();
      ∃ j,
      mpsc_queue_history_elem γ j new_back
    >>>.
  Proof.
    iIntros "!> %Φ (#Hmeta & #Hinv & #Hhistory_elem & Hnew_back_next & Hnew_back_data) HΦ".

    iLöb as "HLöb" forall (i node) "Hhistory_elem".

    wp_rec.
    wp_smart_apply (mpsc_queue_xchain_next_spec with "[$Hmeta $Hinv $Hhistory_elem]") as (res) "[-> | (%node' & -> & #Hhistory_elem')]"; last iSteps.
    wp_pures.

    wp_bind (Cas _ _ _).
    iInv "Hinv" as "(%hist & %past & %front & %nodes & %back & %vs & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hmodel₂)".
    iDestruct (mpsc_queue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (xchain_model_lookup' with "Hhist") as "(Hhist1 & Hnode & Hhist2)"; first done.
    destruct (hist !! S i) as [node' |] eqn:Hlookup'; simpl.

    - wp_cas as _ | [] _.
      iDestruct (xchain_model_lookup'_2 with "Hhist1 Hnode Hhist2") as "Hhist"; [done | rewrite Hlookup' // |].
      iSplitR "Hnew_back_next Hnew_back_data HΦ". { repeat iExists _. iSteps. }
      iSteps.

    - wp_cas as Hcas | _ _; first done.
      iDestruct (xchain_model_lookup'_2 with "Hhist1 Hnode []") as "Hhist"; [done | rewrite Hlookup' // | ..].
      { rewrite -(lookup_last_length hist i) // drop_all //. }
      iDestruct (big_sepL2_snoc with "[$Hnodes $Hnew_back_data]") as "Hnodes".
      iDestruct (xchain_model_snoc_2 with "Hhist Hnew_back_next") as "Hhist".
      iMod (mpsc_queue_history_update new_back with "Hhistory_auth") as "Hhistory_auth".
      iDestruct (mpsc_queue_history_elem_get with "Hhistory_auth") as "#Hhistory_elem_new_back".
      { rewrite lookup_snoc_Some. naive_solver. }
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (mpsc_queue_model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; [iSteps.. |].
      iSplitR "HΦ".
      { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
        iSteps; iPureIntro.
        - rewrite Hhist -assoc //.
        - rewrite elem_of_app. naive_solver.
      }
      iSteps.
  Qed.

  #[local] Lemma mpsc_queue_fix_back_spec l γ ι i back j new_back :
    {{{
      meta l nroot γ ∗
      inv ι (mpsc_queue_inv_inner l γ) ∗
      mpsc_queue_history_elem γ i back ∗
      mpsc_queue_history_elem γ j new_back
    }}}
      mpsc_queue_fix_back #l #back #new_back
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_elem_back & #Hhistory_elem_new_back) HΦ".

    iLöb as "HLöb" forall (i back) "Hhistory_elem_back".

    wp_rec. wp_pures.
    wp_bind (_ and _)%E.
    wp_apply (wp_wand _ _ (λ res, ∃ b, ⌜res = #b⌝)%I) as (res) "(%b & ->)".
    { wp_smart_apply (mpsc_queue_xchain_next_spec with "[$Hmeta $Hinv $Hhistory_elem_new_back]") as (res) "[-> | (%new_back' & -> & #Hhistory_elem_new_back')]"; last iSteps.
      wp_pures.

      wp_bind (Cas _ _ _).
      iInv "Hinv" as "(%hist & %past & %front & %nodes & %back' & %vs & >%Hhist & >%Hback & Hl_front & Hl_back & Hhist & Hnodes & Hhistory_auth & Hmodel₂)".
      wp_cas as _ | -> _.
      2: iDestruct (mpsc_queue_history_agree with "Hhistory_auth Hhistory_elem_new_back") as %Hnew_back%elem_of_list_lookup_2.
      all: iSplitL; first (repeat iExists _; iSteps).
      all: iSteps.
    }
    destruct b; last iSteps.
    wp_smart_apply (mpsc_queue_back_spec with "Hinv") as (back' i') "#Hhistory_elem_back'".
    iApply ("HLöb" with "HΦ Hhistory_elem_back'").
  Qed.

  Lemma mpsc_queue_push_spec t ι v :
    <<<
      mpsc_queue_inv t ι
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_push t v @ ↑ι
    <<<
      mpsc_queue_model t (vs ++ [v])
    | RET (); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec.
    wp_record new_back as "(Hnew_back_next & Hnew_back_data & _)".
    wp_smart_apply (mpsc_queue_back_spec with "Hinv") as (back i) "#Hhistory_elem_back".
    wp_smart_apply (mpsc_queue_do_push_spec with "[$Hmeta $Hinv $Hhistory_elem_back $Hnew_back_next $Hnew_back_data]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_elem_new_back)".
    wp_smart_apply (mpsc_queue_fix_back_spec with "[$Hmeta $Hinv Hhistory_elem_back Hhistory_elem_new_back] HΦ").
    iSteps.
  Qed.

  Lemma mpsc_queue_pop_spec t ι :
    <<<
      mpsc_queue_inv t ι ∗
      mpsc_queue_consumer t
    | ∀∀ vs,
      mpsc_queue_model t vs
    >>>
      mpsc_queue_pop t @ ↑ι
    <<<
      mpsc_queue_model t (tail vs)
    | RET head vs;
      mpsc_queue_consumer t
    >>>.
  Proof.
    iIntros "!> %Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %front & %Heq & Hl_front_1)) HΦ". injection Heq as <-.

    iLöb as "HLöb".

    iMod (mpsc_queue_inv_inner_history_elem with "Hinv Hl_front_1") as "(%i & Hl_front_1 & #Hhistory_elem)".

    wp_rec. wp_load.
    wp_smart_apply (mpsc_queue_xchain_next_spec_strong MpscQueuePop _ _ [tele_arg] inhabitant with "[$Hmeta $Hinv $Hhistory_elem $Hl_front_1 $HΦ]") as (res) "[(-> & Hl_front_1 & HΦ) | (%front' & -> & #Hhistory_elem' & Hl_front_1 & HΦ)]"; [auto | iSteps |].
    wp_pures.

    wp_bind (_ <- _)%E.
    iInv "Hinv" as "(%hist & %past & %_front & %nodes & %back & %vs & >%Hhist & >%Hback & >Hl_front_2 & Hl_back & Hhist & Hnodes & >Hhistory_auth & Hmodel₂)".
    iDestruct (pointsto_agree with "Hl_front_1 Hl_front_2") as %[= <-].
    iCombine "Hl_front_1 Hl_front_2" as "Hl_front".
    rewrite Qp.three_quarter_quarter.
    wp_store.
    iEval (rewrite -Qp.three_quarter_quarter) in "Hl_front".
    iDestruct "Hl_front" as "(Hl_front_1 & Hl_front_2)".
    iDestruct (mpsc_queue_history_agree with "Hhistory_auth Hhistory_elem") as %Hlookup.
    iDestruct (mpsc_queue_history_agree with "Hhistory_auth Hhistory_elem'") as %Hlookup'.
    iAssert ⌜length past = i⌝%I as %Hpast_length.
    { iDestruct (xchain_model_NoDup with "Hhist") as %Hnodup.
      iPureIntro. eapply NoDup_lookup; try done.
      rewrite Hhist list_lookup_middle //.
    }
    rewrite Hhist (assoc _ _ [_]) lookup_app_r app_length /= in Hlookup'; first lia.
    rewrite Nat.add_1_r Hpast_length Nat.sub_diag in Hlookup'.
    destruct nodes as [| node nodes]; first done. injection Hlookup' as ->.
    rewrite (assoc _ _ [_]) in Hhist.
    iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hfront_data & Hnodes)".
    iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpsc_queue_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (mpsc_queue_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "Hl_front_1 Hfront_data HΦ". { repeat iExists _. iSteps. }
    iSteps.
  Qed.
End mpsc_queue_G.

#[global] Opaque mpsc_queue_create.
#[global] Opaque mpsc_queue_is_empty.
#[global] Opaque mpsc_queue_push.
#[global] Opaque mpsc_queue_pop.

#[global] Opaque mpsc_queue_inv.
#[global] Opaque mpsc_queue_model.
#[global] Opaque mpsc_queue_consumer.
