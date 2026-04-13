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
Implicit Types front node back new_back : location.
Implicit Types hist past nodes : list location.
Implicit Types v : val.
Implicit Types o : option val.
Implicit Types vs : list val.

Class MpscQueue1G Σ `{zoo_G : !ZooG Σ} :=
  { #[local] mpsc_queue_1_G_history_G :: MonoListG Σ location
  ; #[local] mpsc_queue_1_G_model_G :: TwinsG Σ (leibnizO (list val))
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

Module base.
  Section mpsc_queue_1_G.
    Context `{mpsc_queue_1_G : MpscQueue1G Σ}.

    Implicit Types t : location.

    Record mpsc_queue_1_name :=
      { mpsc_queue_1_name_inv : namespace
      ; mpsc_queue_1_name_history : gname
      ; mpsc_queue_1_name_model : gname
      }.
    Implicit Type γ : mpsc_queue_1_name.

    #[global] Instance mpsc_queue_1_name_eq_dec : EqDecision mpsc_queue_1_name :=
      ltac:(solve_decision).
    #[global] Instance mpsc_queue_1_name_countable :
      Countable mpsc_queue_1_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition history_auth' γ_history hist :=
      mono_list_auth γ_history (DfracOwn 1) hist.
    #[local] Definition history_auth γ hist :=
      history_auth' γ.(mpsc_queue_1_name_history) hist.
    #[local] Definition history_at γ i node :=
      mono_list_at γ.(mpsc_queue_1_name_history) i node.

    #[local] Definition model₁' γ_model vs :=
      twins_twin1 γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ vs :=
      model₁' γ.(mpsc_queue_1_name_model) vs.
    #[local] Definition model₂' γ_model vs :=
      twins_twin2 γ_model vs.
    #[local] Definition model₂ γ vs :=
      model₂' γ.(mpsc_queue_1_name_model) vs.

    #[local] Definition node_model γ node i : iProp Σ :=
      node ↦ₕ Header §Node 2 ∗
      history_at γ i node.
    #[local] Instance : CustomIpat "node_model" :=
      " ( #H{}_header
        & #Hhistory_at_{}
        )
      ".

    #[local] Definition inv_inner t γ : iProp Σ :=
      ∃ hist past front nodes back vs,
      ⌜hist = past ++ front :: nodes⌝ ∗
      ⌜back ∈ hist⌝ ∗
      t.[front] ↦{#1/4} #front ∗
      t.[back] ↦ #back ∗
      xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
      ([∗ list] node; v ∈ nodes; vs, node.[data] ↦ v) ∗
      history_auth γ hist ∗
      model₂ γ vs.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %hist{}
        & %past{}
        & %front{}
        & %nodes{}
        & %back{}
        & %vs{}
        & >%Hhist{}
        & >%Hback{}
        & >Ht_front
        & >Ht_back
        & >Hhist
        & >Hnodes
        & >Hhistory_auth
        & >Hmodel₂
        )
      ".
    #[local] Definition inv' t γ :=
      inv γ.(mpsc_queue_1_name_inv) (inv_inner t γ).
    Definition mpsc_queue_1_inv t γ ι : iProp Σ :=
      ⌜ι = γ.(mpsc_queue_1_name_inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Hinv
        )
      ".

    Definition mpsc_queue_1_model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[local] Definition consumer_1 t front : iProp Σ :=
      t.[front] ↦{#3/4} #front.
    #[local] Definition consumer_2 t : iProp Σ :=
      ∃ front,
      consumer_1 t front.
    #[local] Instance : CustomIpat "consumer_2" :=
      " ( %front{}
        & Hconsumer{_{}}
        )
      ".
    Definition mpsc_queue_1_consumer :=
      consumer_2.
    #[local] Instance : CustomIpat "consumer" :=
      " (:consumer_2)
      ".

    #[global] Instance mpsc_queue_1_model_timeless γ vs :
      Timeless (mpsc_queue_1_model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_queue_1_consumer_timeless t :
      Timeless (mpsc_queue_1_consumer t).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpsc_queue_1_inv_persistent t γ ι :
      Persistent (mpsc_queue_1_inv t γ ι).
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

    #[local] Lemma inv_inner_history_at t γ front :
      inv' t γ -∗
      consumer_1 t front ={⊤}=∗
        ∃ i,
        consumer_1 t front ∗
        node_model γ front i.
    Proof.
      iIntros "#Hinv Hconsumer".
      iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (pointsto_agree with "Ht_front Hconsumer") as %[= ->].
      assert (hist1 !! (length past1) = Some front) as Hlookup.
      { rewrite Hhist1 list_lookup_middle //. }
      iDestruct (xtchain_lookup_header with "Hhist") as "#Hfront_header"; first done.
      iDestruct (history_at_get (length past1) front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
      iSplitR "Hconsumer". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma mpsc_queue_1_model_exclusive γ vs1 vs2 :
      mpsc_queue_1_model γ vs1 -∗
      mpsc_queue_1_model γ vs2 -∗
      False.
    Proof.
      apply model₁_exclusive.
    Qed.

    Lemma mpsc_queue_1_consumer_exclusive t :
      mpsc_queue_1_consumer t -∗
      mpsc_queue_1_consumer t -∗
      False.
    Proof.
      iIntros "(:consumer =1) (:consumer =2)".
      iDestruct (pointsto_dfrac_ne with "Hconsumer_1 Hconsumer_2") as %?; naive_solver.
    Qed.

    Lemma mpsc_queue_1_create𑁒spec ι :
      {{{
        True
      }}}
        mpsc_queue_1_create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mpsc_queue_1_inv t γ ι ∗
        mpsc_queue_1_model γ [] ∗
        mpsc_queue_1_consumer t
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_block front as "#Hfront_header" "_" "(Hfront_next & _)".
      wp_block t as "Hmeta" "(Ht_front & Ht_back & _)".
      iEval (rewrite -Qp.quarter_three_quarter) in "Ht_front".
      iDestruct "Ht_front" as "(Ht_front & Hconsumer)".

      iMod history_alloc as "(%γ_history & Hhistory_auth)".
      iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

      pose γ := {|
        mpsc_queue_1_name_inv := ι ;
        mpsc_queue_1_name_history := γ_history ;
        mpsc_queue_1_name_model := γ_model ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameStep.
      iApply inv_alloc.
      iExists [front], [], front, [], front, []. iFrameSteps.
      - rewrite list_elem_of_singleton //.
      - rewrite xtchain_singleton. iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1_front𑁒spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{front}
      {{{
        front i
      , RET #front;
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

    #[local] Lemma back𑁒spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{back}
      {{{
        back i
      , RET #back;
        node_model γ back i
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
      | IsEmpty (Ψ : bool → iProp Σ)
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
      | IsEmpty _ =>
          IsEmpty'
      | Pop _ =>
          Pop'
      | Other =>
          Other'
      end.
    #[local] Definition is_empty_au γ (Ψ : bool → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(mpsc_queue_1_name_inv), ∅ <{
        model₁ γ vs
      , COMM
        Ψ (bool_decide (vs = []))
      }>.
    #[local] Definition pop_au γ (Ψ : option val → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(mpsc_queue_1_name_inv), ∅ <{
        model₁ γ (tail vs)
      , COMM
        Ψ (head vs)
      }>.
    #[local] Lemma next𑁒spec_aux op t γ i node :
      {{{
        inv' t γ ∗
        history_at γ i node ∗
        ( if decide (op = Other' :> operation') then True else
            consumer_1 t node
        ) ∗
        match op with
        | IsEmpty Ψ =>
            is_empty_au γ Ψ
        | Pop Ψ =>
            pop_au γ Ψ
        | Other =>
            True
        end
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
        ( if decide (op = Other' :> operation') then True else
            consumer_1 t node
        ) ∗
        ( ⌜res = §Null%V⌝ ∗
          match op with
          | IsEmpty Ψ =>
              Ψ true
          | Pop Ψ =>
              Ψ None
          | Other =>
              True
          end
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node_model γ node' (S i) ∗
          match op with
          | IsEmpty Ψ =>
              Ψ false
          | Pop Ψ =>
              pop_au γ Ψ
          | Other =>
              True
          end
        )
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
        destruct op; [| iFrameSteps..].
        iDestruct "Hop" as "(Hconsumer & HΨ)".
        iDestruct (pointsto_agree with "Ht_front Hconsumer") as %[= <-].

        iMod "HΨ" as "(%vs_ & (:model) & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iAssert ⌜length past = i⌝%I as %Hpast_length.
        { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
          iPureIntro. eapply NoDup_lookup; try done.
          rewrite Hhist list_lookup_middle //.
        }
        rewrite -(bool_decide_ext _ _ (length_zero_iff_nil _)).
        iDestruct (big_sepL2_length with "Hnodes") as %<-.
        rewrite bool_decide_eq_false_2.
        { apply (f_equal length) in Hhist as Hhist_length.
          simpl_length/= in Hhist_length.
          apply lookup_lt_Some in Hlookup'.
          lia.
        }

        iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
        iSteps.

      - destruct_decide (op = Other' :> operation').
        { destruct op; try done. iSteps. }
        iDestruct "Hop" as "(Hconsumer & HΨ)".
        iDestruct (pointsto_agree with "Ht_front Hconsumer") as %[= <-].

        iAssert ⌜length past = i⌝%I as %Hpast_length.
        { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
          iPureIntro. eapply NoDup_lookup; try done.
          rewrite Hhist list_lookup_middle //.
        }
        destruct_decide (length vs = 0) as ->%nil_length_inv | Hvs; last first.
        { iDestruct (big_sepL2_length with "Hnodes") as %?.
          exfalso.
          apply (f_equal length) in Hhist.
          opose proof* length_lookup_last as Heq; [done.. |].
          simpl_length/= in Hhist. lia.
        }

        destruct op; last done.

        + iMod "HΨ" as "(%vs & (:model) & _ & HΨ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
          iSteps.

        + iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
          iSteps.
    Qed.
    #[local] Lemma next𑁒spec {t γ i} node :
      {{{
        inv' t γ ∗
        history_at γ i node
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
          ⌜res = §Null%V⌝
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node_model γ node' (S i)
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node) HΦ".

      wp_apply (next𑁒spec_aux Other); iSteps.
    Qed.
    #[local] Lemma next𑁒spec_is_empty {t γ i node} Ψ :
      {{{
        inv' t γ ∗
        history_at γ i node ∗
        consumer_1 t node ∗
        is_empty_au γ Ψ
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
        consumer_1 t node ∗
        ( ⌜res = §Null%V⌝ ∗
          Ψ true
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node_model γ node' (S i) ∗
          Ψ false
        )
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & Ht_front & Hau) HΦ".

      wp_apply (next𑁒spec_aux (IsEmpty _) with "[$]").
      iFrameSteps.
    Qed.
    #[local] Lemma next𑁒spec_pop {t γ i node} Ψ :
      {{{
        inv' t γ ∗
        history_at γ i node ∗
        consumer_1 t node ∗
        pop_au γ Ψ
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
        consumer_1 t node ∗
        ( ⌜res = §Null%V⌝ ∗
          Ψ None
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node_model γ node' (S i) ∗
          pop_au γ Ψ
        )
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & Ht_front & Hau) HΦ".

      wp_apply (next𑁒spec_aux (Pop _) with "[$]").
      iFrameSteps.
    Qed.

    Lemma mpsc_queue_1_is_empty𑁒spec t γ ι :
      <<<
        mpsc_queue_1_inv t γ ι ∗
        mpsc_queue_1_consumer t
      | ∀∀ vs,
        mpsc_queue_1_model γ vs
      >>>
        mpsc_queue_1_is_empty #t @ ↑ι
      <<<
        mpsc_queue_1_model γ vs
      | RET #(bool_decide (vs = []%list));
        mpsc_queue_1_consumer t
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:consumer)) HΦ".

      iMod (inv_inner_history_at with "Hinv Hconsumer") as "(%i & Ht_front & #Hfront_header & #Hhistory_at_front)".

      wp_rec. wp_load. wp_match.
      wp_apply+ (next𑁒spec_is_empty (λ b, _ -∗ Φ #b)%I with "[$]").
      iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1_push_0𑁒spec t γ i node new_back v :
      <<<
        inv' t γ ∗
        node_model γ node i ∗
        new_back ↦ₕ Header §Node 2 ∗
        new_back.[next] ↦ §Null ∗
        new_back.[data] ↦ v
      | ∀∀ vs,
        mpsc_queue_1_model γ vs
      >>>
        mpsc_queue_1_push_0 #node #new_back @ ↑γ.(mpsc_queue_1_name_inv)
      <<<
        mpsc_queue_1_model γ (vs ++ [v])
      | RET ();
        ∃ j,
        history_at γ j new_back
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & (:node_model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

      iLöb as "HLöb" forall (i node) "Hnode_header Hhistory_at_node".

      wp_rec. wp_match.
      wp_apply+ (next𑁒spec with "[$]") as (res) "[-> | (%node' & -> & (:node_model =node'))]"; last iSteps.
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

    #[local] Lemma mpsc_queue_1_fix_back𑁒spec t γ i back j new_back :
      {{{
        inv' t γ ∗
        history_at γ i back ∗
        node_model γ new_back j
      }}}
        mpsc_queue_1_fix_back #t #back #new_back
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
      { wp_apply+ (next𑁒spec new_back with "[$]") as (res) "[-> | (%new_back' & -> & (:node_model =new_back'))]"; last iSteps.
        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =1)".
        wp_cas as _ | [= ->]; first iSteps.
        iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_new_back") as %Hnew_back%list_elem_of_lookup_2.
        iSteps.
      }

      destruct b; last iSteps.
      wp_apply+ domain_yield𑁒spec.
      wp_apply+ (back𑁒spec with "Hinv") as (back' i') "(:node_model =back')".
      iApply ("HLöb" with "HΦ Hhistory_at_back'").
    Qed.

    Lemma mpsc_queue_1_push𑁒spec t γ ι v :
      <<<
        mpsc_queue_1_inv t γ ι
      | ∀∀ vs,
        mpsc_queue_1_model γ vs
      >>>
        mpsc_queue_1_push #t v @ ↑ι
      <<<
        mpsc_queue_1_model γ (vs ++ [v])
      | RET ();
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec.
      wp_block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
      wp_match.
      wp_apply+ (back𑁒spec with "Hinv") as (back i) "(:node_model =back)".
      wp_apply+ (mpsc_queue_1_push_0𑁒spec with "[$]").
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
      wp_apply+ (mpsc_queue_1_fix_back𑁒spec with "[] HΦ"); first iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1_pop𑁒spec_aux t γ :
      <<<
        inv' t γ ∗
        consumer_2 t
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpsc_queue_1_pop #t @ ↑γ.(mpsc_queue_1_name_inv)
      <<<
        model₁ γ (tail vs)
      | RET head vs;
        consumer_2 t
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & (:consumer_2)) HΦ".

      iLöb as "HLöb".

      iMod (inv_inner_history_at with "Hinv Hconsumer") as "(%i & Hconsumer & (:node_model =front))".

      wp_rec. wp_load. wp_match.
      wp_apply+ (next𑁒spec_pop (λ o, _ -∗ Φ o)%I with "[$]") as (res) "(Hconsumer & [(-> & HΦ) | (%new_front & -> & (:node_model =new_front) & HΦ)])"; first iSteps.
      wp_match. wp_pures.

      wp_bind (_ <-{front} _)%E.
      iInv "Hinv" as "(:inv_inner =1)".
      iDestruct (pointsto_agree with "Ht_front Hconsumer") as %[= ->].
      iCombine "Ht_front Hconsumer" as "Ht_front".
      rewrite Qp.quarter_three_quarter.
      wp_store.
      iEval (rewrite -Qp.quarter_three_quarter) in "Ht_front".
      iDestruct "Ht_front" as "(Ht_front & Hconsumer)".
      iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_front") as %Hlookup.
      iDestruct (history_at_lookup with "Hhistory_auth Hhistory_at_new_front") as %Hlookup_new.
      iAssert ⌜length past1 = i⌝%I as %Hpast1_length.
      { iDestruct (xtchain_NoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist1 list_lookup_middle //.
      }
      rewrite Hhist1 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup_new; first lia.
      rewrite Nat.add_1_r Hpast1_length Nat.sub_diag in Hlookup_new.
      destruct nodes1 as [| node nodes1]; first done. injection Hlookup_new as ->.
      rewrite (assoc _ _ [_]) in Hhist1.
      iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hnew_front_data & Hnodes)".

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Hconsumer Hnew_front_data HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    Lemma mpsc_queue_1_pop𑁒spec t γ ι :
      <<<
        mpsc_queue_1_inv t γ ι ∗
        mpsc_queue_1_consumer t
      | ∀∀ vs,
        mpsc_queue_1_model γ vs
      >>>
        mpsc_queue_1_pop #t @ ↑ι
      <<<
        mpsc_queue_1_model γ (tail vs)
      | RET head vs;
        mpsc_queue_1_consumer t
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:consumer)) HΦ".

      wp_apply (mpsc_queue_1_pop𑁒spec_aux with "[$]").
      iAuIntro.
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
      iAaccIntro with "Hmodel₁"; iSteps.
    Qed.
  End mpsc_queue_1_G.

  #[global] Opaque mpsc_queue_1_inv.
  #[global] Opaque mpsc_queue_1_model.
  #[global] Opaque mpsc_queue_1_consumer.
End base.

From zoo_saturn Require
  mpsc_queue_1__opaque.

Section mpsc_queue_1_G.
  Context `{mpsc_queue_1_G : MpscQueue1G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition mpsc_queue_1_inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpsc_queue_1_inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mpsc_queue_1_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpsc_queue_1_model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition mpsc_queue_1_consumer t : iProp Σ :=
    ∃ 𝑡,
    ⌜t = #𝑡⌝ ∗
    base.mpsc_queue_1_consumer 𝑡.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %𝑡{}
      & {%Heq{};->}
      & Hconsumer{_{}}
      )
    ".

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

  Lemma mpsc_queue_1_model_exclusive t vs1 vs2 :
    mpsc_queue_1_model t vs1 -∗
    mpsc_queue_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpsc_queue_1_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma mpsc_queue_1_consumer_exclusive t :
    mpsc_queue_1_consumer t -∗
    mpsc_queue_1_consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iApply (base.mpsc_queue_1_consumer_exclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma mpsc_queue_1_create𑁒spec ι :
    {{{
      True
    }}}
      mpsc_queue_1_create ()
    {{{
      t
    , RET t;
      mpsc_queue_1_inv t ι ∗
      mpsc_queue_1_model t [] ∗
      mpsc_queue_1_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.mpsc_queue_1_create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Hconsumer)".
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma mpsc_queue_1_is_empty𑁒spec t ι :
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
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.

    awp_apply (base.mpsc_queue_1_is_empty𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =3)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_3") as %->. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_3"; iSteps.
    }
  Qed.

  Lemma mpsc_queue_1_push𑁒spec t ι v :
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

    awp_apply (base.mpsc_queue_1_push𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma mpsc_queue_1_pop𑁒spec t ι :
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
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.

    awp_apply (base.mpsc_queue_1_pop𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =3)". simplify.
      iDestruct (meta_agree with "Hmeta_1 Hmeta_3") as %->. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_3"; iSteps.
    }
  Qed.
End mpsc_queue_1_G.

#[global] Opaque mpsc_queue_1_inv.
#[global] Opaque mpsc_queue_1_model.
#[global] Opaque mpsc_queue_1_consumer.
