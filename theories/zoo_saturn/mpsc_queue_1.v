From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_list
  lib.twins.
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
  mpsc_queue_1__code.
From zoo_saturn Require Import
  mpsc_queue_1__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v t : val.
Implicit Types vs : list val.

Class MpscQueue1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpsc_queue_1_G_history_G :: MonoListG Σ location ;
  #[local] mpsc_queue_1_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpsc_queue_1_Σ := #[
  mono_list_Σ location ;
  twins_Σ (leibnizO (list val))
].
#[global] Instance subG_mpsc_queue_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_queue_1_Σ Σ →
  MpscQueue1G Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_1_G.
  Context `{mpsc_queue_1_G : MpscQueue1G Σ}.

  Record metadata := {
    metadata_inv : namespace ;
    metadata_history : gname ;
    metadata_model : gname ;
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

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition node_model γ node i : iProp Σ :=
    node ↦ₕ Header §Node 2 ∗
    history_at γ i node.
  #[local] Instance : CustomIpatFormat "node_model" :=
    "(
      #H{}_header &
      #Hhistory_at_{}
    )".

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ hist past front nodes back vs,
    ⌜hist = past ++ front :: nodes⌝ ∗
    ⌜back ∈ hist⌝ ∗
    l.[front] ↦{#1/4} #front ∗
    l.[back] ↦ #back ∗
    xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
    ([∗ list] node; v ∈ nodes; vs, node.[xtchain_data] ↦ v) ∗
    history_auth γ hist ∗
    model₂ γ vs.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %hist{} &
      %past{} &
      %front{} &
      %nodes{} &
      %back{} &
      %vs{} &
      >%Hhist{} &
      >%Hback{} &
      >Hl_front &
      >Hl_back &
      >Hhist &
      >Hnodes &
      >Hhistory_auth &
      >Hmodel₂
    )".
  #[local] Definition inv' l γ :=
    inv γ.(metadata_inv) (inv_inner l γ).
  Definition mpsc_queue_1_inv t ι : iProp Σ :=
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

  Definition mpsc_queue_1_model t vs : iProp Σ :=
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

  Definition mpsc_queue_1_consumer t : iProp Σ :=
    ∃ l front,
    ⌜t = #l⌝ ∗
    l.[front] ↦{#3/4} #front.
  #[local] Instance : CustomIpatFormat "consumer" :=
    "(
      %l{_{suff}} &
      %front{_{suff}} &
      {%Heq{suff}=->} &
      Hl_front{_{suff}}
    )".

  #[global] Instance mpsc_queue_1_model_timeless t vs :
    Timeless (mpsc_queue_1_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_1_consumer_timeless t :
    Timeless (mpsc_queue_1_consumer t ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_1_inv_persistent t ι :
    Persistent (mpsc_queue_1_inv t ι).
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

  #[local] Lemma inv_inner_history_at l γ front :
    inv' l γ -∗
    l.[front] ↦{#3/4} #front ={⊤}=∗
      ∃ i,
      l.[front] ↦{#3/4} #front ∗
      node_model γ front i.
  Proof.
    iIntros "#Hinv Hl_front_".
    iInv "Hinv" as "(:inv_inner =1)".
    iDestruct (pointsto_agree with "Hl_front Hl_front_") as %[= ->].
    assert (hist1 !! (length past1) = Some front) as Hlookup.
    { rewrite Hhist1 list_lookup_middle //. }
    iDestruct (xtchain_lookup_header with "Hhist") as "#Hfront_header"; first done.
    iDestruct (history_at_get (length past1) front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
    iSplitR "Hl_front_". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma mpsc_queue_1_consumer_exclusive t :
    mpsc_queue_1_consumer t -∗
    mpsc_queue_1_consumer t -∗
    False.
  Proof.
    iIntros "(:consumer) (:consumer suff=)". injection Heq as <-.
    iDestruct (pointsto_dfrac_ne with "Hl_front Hl_front_") as %?; naive_solver.
  Qed.

  Lemma mpsc_queue_1_create_spec ι :
    {{{
      True
    }}}
      mpsc_queue_1_create ()
    {{{ t,
      RET t;
      mpsc_queue_1_inv t ι ∗
      mpsc_queue_1_model t [] ∗
      mpsc_queue_1_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_block front as "#Hfront_header" "_" "(Hfront_next & _)".
    wp_block l as "Hmeta" "(Hl_front & Hl_back & _)".
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl_front".
    iDestruct "Hl_front" as "(Hl_front & Hl_front_)".

    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      metadata_inv := ι ;
      metadata_history := γ_history ;
      metadata_model := γ_model ;
    |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hl_front_"; last iSteps.
    iExists l, γ. iStep 3. iApply inv_alloc.
    iExists [front], [], front, [], front, []. iFrameSteps.
    - rewrite elem_of_list_singleton //.
    - rewrite xtchain_singleton. iSteps.
  Qed.

  #[local] Lemma mpsc_queue_1_front_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{front}
    {{{ front i,
      RET #front;
      node_model γ front i
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    assert (hist !! (length past) = Some front) as Hlookup.
    { rewrite Hhist list_lookup_middle //. }
    iDestruct (xtchain_lookup_header with "Hhist") as "#Hfront_header"; first done.
    iDestruct (history_at_get _ front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma back_spec l γ :
    {{{
      inv' l γ
    }}}
      (#l).{back}
    {{{ back i,
      RET #back;
      node_model γ back i
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

  Inductive op :=
    | IsEmpty
    | Pop
    | Other.
  #[local] Instance op_eq_dec : EqDecision op :=
    ltac:(solve_decision).
  #[local] Lemma xtchain_next_spec_strong op TB β x_empty x_nonempty Ψ l γ i node :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i node ∗
      ( if decide (op = Other) then True else
          l.[front] ↦{#3/4} #node ∗
          atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑γ.(metadata_inv)) ∅ (tele_app $ mpsc_queue_1_model #l) β Ψ ∗
          (mpsc_queue_1_model #l [] -∗ β [tele_arg []] x_empty)
      ) ∗
      ( if decide (op ≠ IsEmpty) then True else
          ∀ vs,
          ⌜vs ≠ []⌝ -∗
          mpsc_queue_1_model #l vs -∗
          β (TeleArgCons vs ()) x_nonempty
      )
    }}}
      (#node).{xtchain_next}
    {{{ res,
      RET res;
      ( ⌜res = ()%V⌝ ∗
        if decide (op = Other) then True else
          l.[front] ↦{#3/4} #node ∗
          Ψ [tele_arg []] x_empty
      ) ∨ (
        ∃ node',
        ⌜res = #node'⌝ ∗
        node_model γ node' (S i) ∗
        ( if decide (op = Other) then True else
            l.[front] ↦{#3/4} #node
        ) ∗
        match op with
        | IsEmpty =>
            ∃ vs,
            Ψ (TeleArgCons vs ()) x_nonempty
        | Pop =>
            atomic_update (TA := [tele vs]) (TB := TB) (⊤ ∖ ↑γ.(metadata_inv)) ∅ (tele_app $ mpsc_queue_1_model #l) β Ψ
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
      destruct (decide (op = IsEmpty)) as [-> | Hop].

      + iDestruct "Hop" as "((Hl_front_ & HΨ & Hβ_empty) & Hβ_nonempty)".
        iDestruct (pointsto_agree with "Hl_front Hl_front_") as %[= <-].

        iMod "HΨ" as "(%vs_ & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iDestruct ("Hβ_nonempty" with "[#] [Hmodel₁]") as "Hβ"; [| iSteps |].
        { iAssert ⌜length past = i⌝%I as %Hpast_length.
          { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
            iPureIntro. eapply NoDup_lookup; try done.
            rewrite Hhist list_lookup_middle //.
          }
          rewrite -length_zero_iff_nil.
          iDestruct (big_sepL2_length with "Hnodes") as %<-.
          iIntros "%Hnodes_length". iPureIntro.
          apply (f_equal length) in Hhist as Hhist_length.
          simpl_length/= in Hhist_length.
          apply lookup_lt_Some in Hlookup'.
          lia.
        }
        iMod ("HΨ" $! x_nonempty with "Hβ") as "HΨ".

        iSplitR "Hl_front_ HΨ HΦ". { iFrameSteps. }
        iSteps.

      + iSplitR "Hop HΦ". { iFrameSteps. }
        destruct op; [done | iSteps..].

    - destruct (decide (op = Other)) as [-> | Hop]; first iSteps.
      iDestruct "Hop" as "((Hl_front_ & HΨ & Hβ_empty) & _)".
      iDestruct (pointsto_agree with "Hl_front Hl_front_") as %[= <-].
      iAssert ⌜length past = i⌝%I as %Hpast_length.
      { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist list_lookup_middle //.
      }
      destruct (decide (length vs = 0)) as [->%nil_length_inv | Hvs]; last first.
      { iDestruct (big_sepL2_length with "Hnodes") as %?.
        exfalso.
        apply (f_equal length) in Hhist.
        opose proof* length_lookup_last as Heq; [done.. |].
        simpl_length/= in Hhist. lia.
      }

      iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iDestruct ("Hβ_empty" with "[Hmodel₁]") as "Hβ"; first iSteps.
      iMod ("HΨ" with "Hβ") as "HΨ".

      iSplitR "Hl_front_ HΨ HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  #[local] Lemma xtchain_next_spec {l γ i} node :
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
        node_model γ node' (S i)
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hhistory_at_node) HΦ".
    wp_apply (xtchain_next_spec_strong Other TeleO inhabitant inhabitant inhabitant inhabitant); iSteps.
  Qed.

  Lemma mpsc_queue_1_is_empty_spec t ι :
    <<<
      mpsc_queue_1_inv t ι ∗
      mpsc_queue_1_consumer t
    | ∀∀ vs,
      mpsc_queue_1_model t vs
    >>>
      mpsc_queue_1_is_empty t @ ↑ι
    <<<
      mpsc_queue_1_model t vs
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_1_consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer suff=)) HΦ". injection Heq as <-.

    iMod (inv_inner_history_at with "Hinv Hl_front_") as "(%i & Hl_front & #Hfront_header & #Hhistory_at_front)".

    iAssert (
      AU <{
        ∃∃ vs,
        mpsc_queue_1_model #l vs
      }> @ ⊤ ∖ ↑γ.(metadata_inv), ∅ <{
        ∀∀ b,
        ⌜b = bool_decide (vs = [])⌝ ∗
        mpsc_queue_1_model #l vs
      , COMM
        mpsc_queue_1_consumer #l -∗
        Φ #b
      }>
    )%I with "[HΦ]" as "HΦ".
    { iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; iSteps.
    }

    wp_rec. wp_load. wp_match.
    wp_smart_apply (xtchain_next_spec_strong IsEmpty [tele_pair bool] _ [tele_arg true] [tele_arg false] with "[$Hl_front $HΦ]"); last iSteps.
    iSteps. iSplitR; iSteps.
  Qed.

  #[local] Lemma mpsc_queue_1_push_0_spec l γ i node new_back v :
    <<<
      meta l nroot γ ∗
      inv' l γ ∗
      node_model γ node i ∗
      new_back ↦ₕ Header §Node 2 ∗
      new_back.[xtchain_next] ↦ () ∗
      new_back.[xtchain_data] ↦ v
    | ∀∀ vs,
      mpsc_queue_1_model #l vs
    >>>
      mpsc_queue_1_push_0 #node #new_back @ ↑γ.(metadata_inv)
    <<<
      mpsc_queue_1_model #l (vs ++ [v])
    | RET ();
      ∃ j,
      history_at γ j new_back
    >>>.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & (:node_model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

    iLöb as "HLöb" forall (i node) "Hnode_header Hhistory_at_node".

    wp_rec. wp_match.
    wp_smart_apply (xtchain_next_spec with "[$]") as (res) "[-> | (%node' & -> & (:node_model =node'))]".
    2:{ wp_match. iSteps. }
    wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (history_agree with "Hhistory_auth Hhistory_at_node") as %Hlookup.
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
      iMod (history_update new_back with "Hhistory_auth") as "Hhistory_auth".
      iDestruct (history_at_get with "Hhistory_auth") as "#Hhistory_at_new_back".
      { rewrite lookup_snoc_Some. naive_solver. }

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; [iSteps.. |].

      iSplitR "HΦ".
      { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
        iSteps; iPureIntro.
        - rewrite Hhist -assoc //.
        - rewrite elem_of_app. naive_solver.
      }
      iSteps.
  Qed.

  #[local] Lemma mpsc_queue_1_fix_back_spec l γ i back j new_back :
    {{{
      meta l nroot γ ∗
      inv' l γ ∗
      history_at γ i back ∗
      node_model γ new_back j
    }}}
      mpsc_queue_1_fix_back #l #back #new_back
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
    { wp_smart_apply (xtchain_next_spec new_back with "[$]") as (res) "[-> | (%new_back' & -> & (:node_model =new_back'))]"; last iSteps.
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =1)".
      wp_cas as _ | [= ->]; first iSteps.
      iDestruct (history_agree with "Hhistory_auth Hhistory_at_new_back") as %Hnew_back%elem_of_list_lookup_2.
      iSteps.
    }
    destruct b; last iSteps.
    wp_smart_apply domain_yield_spec.
    wp_smart_apply (back_spec with "Hinv") as (back' i') "(:node_model =back')".
    iApply ("HLöb" with "HΦ Hhistory_at_back'").
  Qed.

  Lemma mpsc_queue_1_push_spec t ι v :
    <<<
      mpsc_queue_1_inv t ι
    | ∀∀ vs,
      mpsc_queue_1_model t vs
    >>>
      mpsc_queue_1_push t v @ ↑ι
    <<<
      mpsc_queue_1_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
    wp_match.
    wp_smart_apply (back_spec with "Hinv") as (back i) "(:node_model =back)".
    wp_smart_apply (mpsc_queue_1_push_0_spec with "[$]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
    wp_smart_apply (mpsc_queue_1_fix_back_spec with "[] HΦ"); first iSteps.
  Qed.

  Lemma mpsc_queue_1_pop_spec t ι :
    <<<
      mpsc_queue_1_inv t ι ∗
      mpsc_queue_1_consumer t
    | ∀∀ vs,
      mpsc_queue_1_model t vs
    >>>
      mpsc_queue_1_pop t @ ↑ι
    <<<
      mpsc_queue_1_model t (tail vs)
    | RET head vs;
      mpsc_queue_1_consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer suff=)) HΦ". injection Heq as <-.

    iLöb as "HLöb".

    iMod (inv_inner_history_at with "Hinv Hl_front_") as "(%i & Hl_front_ & (:node_model =front))".

    wp_rec. wp_load. wp_match.
    wp_smart_apply (xtchain_next_spec_strong Pop _ _ [tele_arg] inhabitant with "[$Hl_front_ $HΦ]") as (res) "[(-> & Hl_front_ & HΦ) | (%new_front & -> & (:node_model =new_front) & Hl_front_ & HΦ)]"; [auto | iSteps |].
    wp_match. wp_pures.

    wp_bind (_ <-{front} _)%E.
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (pointsto_agree with "Hl_front Hl_front_") as %[= ->].
    iCombine "Hl_front Hl_front_" as "Hl_front".
    rewrite Qp.quarter_three_quarter.
    wp_store.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hl_front".
    iDestruct "Hl_front" as "(Hl_front & Hl_front_)".
    iDestruct (history_agree with "Hhistory_auth Hhistory_at_front") as %Hlookup.
    iDestruct (history_agree with "Hhistory_auth Hhistory_at_new_front") as %Hlookup_new.
    iAssert ⌜length past = i⌝%I as %Hpast_length.
    { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
      iPureIntro. eapply NoDup_lookup; try done.
      rewrite Hhist list_lookup_middle //.
    }
    rewrite Hhist (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup_new; first lia.
    rewrite Nat.add_1_r Hpast_length Nat.sub_diag in Hlookup_new.
    destruct nodes as [| node nodes]; first done. injection Hlookup_new as ->.
    rewrite (assoc _ _ [_]) in Hhist.
    iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hnew_front_data & Hnodes)".

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_front_ Hnew_front_data HΦ". { iFrameSteps. }
    iSteps.
  Qed.
End mpsc_queue_1_G.

#[global] Opaque mpsc_queue_1_create.
#[global] Opaque mpsc_queue_1_is_empty.
#[global] Opaque mpsc_queue_1_push.
#[global] Opaque mpsc_queue_1_pop.

#[global] Opaque mpsc_queue_1_inv.
#[global] Opaque mpsc_queue_1_model.
#[global] Opaque mpsc_queue_1_consumer.
