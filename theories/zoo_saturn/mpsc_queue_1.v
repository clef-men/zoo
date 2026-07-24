Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Import zoo_std.domain.
Require Export zoo_saturn.mpsc_queue_1__code.
Require Import zoo_saturn.mpsc_queue_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front node back new_back : location.
Implicit Type hist past nodes : list location.
Implicit Type v : val.
Implicit Type o : option val.
Implicit Type vs : list val.

Class MpscQueue1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpsc_queue_1۰G۰history۰G :: MonoListG Σ location
  ; #[local] mpsc_queue_1۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  }.

Definition mpsc_queue_1۰Σ :=
  #[mono_list۰Σ location
  ; twins۰Σ (leibnizO (list val))
  ].
#[global] Instance subG𑁒mpsc_queue_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpsc_queue_1۰Σ Σ →
  MpscQueue1G Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section mpsc_queue_1۰G.
    Context `{mpsc_queue_1۰G : MpscQueue1G Σ}.

    Implicit Type t : location.

    Record mpsc_queue_1۰name :=
      { mpsc_queue_1۰name۰inv : namespace
      ; mpsc_queue_1۰name۰history : gname
      ; mpsc_queue_1۰name۰model : gname
      }.
    Implicit Type γ : mpsc_queue_1۰name.

    #[global] Instance mpsc_queue_1۰name𑁒eq_dec : EqDecision mpsc_queue_1۰name :=
      ltac:(solve_decision).
    #[global] Instance mpsc_queue_1۰name𑁒countable :
      Countable mpsc_queue_1۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition history۰auth' γ_history hist :=
      mono_list۰auth γ_history (DfracOwn 1) hist.
    #[local] Definition history۰auth γ hist :=
      history۰auth' γ.(mpsc_queue_1۰name۰history) hist.
    #[local] Definition history۰at γ i node :=
      mono_list۰at γ.(mpsc_queue_1۰name۰history) i node.

    #[local] Definition model₁' γ_model vs :=
      twins۰twin₁ γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ vs :=
      model₁' γ.(mpsc_queue_1۰name۰model) vs.
    #[local] Definition model₂' γ_model vs :=
      twins۰twin₂ γ_model vs.
    #[local] Definition model₂ γ vs :=
      model₂' γ.(mpsc_queue_1۰name۰model) vs.

    #[local] Definition node۰model γ node i : iProp Σ :=
      node ↦ₕ Header §Node 2 ∗
      history۰at γ i node.
    #[local] Instance : CustomIpat "node۰model" :=
      " ( #H{}_header
        & #Hhistory_at_{}
        )
      ".

    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ hist past front nodes back vs,
      ⌜hist = past ++ front :: nodes⌝ ∗
      ⌜back ∈ hist⌝ ∗
      t.[front] ↦{#1/4} #front ∗
      t.[back] ↦ #back ∗
      xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
      ([∗ list] node; v ∈ nodes; vs, node.[data] ↦ v) ∗
      history۰auth γ hist ∗
      model₂ γ vs.
    #[local] Instance : CustomIpat "inv۰inner" :=
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
      inv γ.(mpsc_queue_1۰name۰inv) (inv۰inner t γ).
    Definition mpsc_queue_1۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(mpsc_queue_1۰name۰inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Hinv
        )
      ".

    Definition mpsc_queue_1۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[local] Definition consumer₁ t front : iProp Σ :=
      t.[front] ↦{#3/4} #front.
    #[local] Definition consumer₂ t : iProp Σ :=
      ∃ front,
      consumer₁ t front.
    #[local] Instance : CustomIpat "consumer₂" :=
      " ( %front{}
        & Hconsumer{_{}}
        )
      ".
    Definition mpsc_queue_1۰consumer :=
      consumer₂.
    #[local] Instance : CustomIpat "consumer" :=
      " (:consumer₂)
      ".

    #[global] Instance mpsc_queue_1۰model𑁒timeless γ vs :
      Timeless (mpsc_queue_1۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_queue_1۰consumer𑁒timeless t :
      Timeless (mpsc_queue_1۰consumer t).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpsc_queue_1۰inv𑁒persistent t γ ι :
      Persistent (mpsc_queue_1۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma history𑁒alloc front :
      ⊢ |==>
        ∃ γ_history,
        history۰auth' γ_history [front].
    Proof.
      apply mono_list𑁒alloc.
    Qed.
    #[local] Lemma history۰at𑁒get {γ hist} i node :
      hist !! i = Some node →
      history۰auth γ hist ⊢
      history۰at γ i node.
    Proof.
      apply mono_list۰at𑁒get.
    Qed.
    #[local] Lemma history۰at𑁒lookup γ hist i node :
      history۰auth γ hist -∗
      history۰at γ i node -∗
      ⌜hist !! i = Some node⌝.
    Proof.
      apply mono_list۰at𑁒valid.
    Qed.
    #[local] Lemma history𑁒update {γ hist} node :
      history۰auth γ hist ⊢ |==>
        history۰auth γ (hist ++ [node]) ∗
        history۰at γ (length hist) node.
    Proof.
      iIntros "Hauth".
      iMod (mono_list𑁒update𑁒snoc with "Hauth") as "Hauth".
      iDestruct (history۰at𑁒get with "Hauth") as "#Hat".
      { rewrite lookup_snoc_Some. naive_solver. }
      iSteps.
    Qed.

    #[local] Lemma model𑁒alloc :
      ⊢ |==>
        ∃ γ_model,
        model₁' γ_model [] ∗
        model₂' γ_model [].
    Proof.
      apply twins𑁒alloc'.
    Qed.
    #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma model𑁒agree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: twins𑁒agree𑁒L.
    Qed.
    #[local] Lemma model𑁒update {γ vs1 vs2} vs :
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        model₁ γ vs ∗
        model₂ γ vs.
    Proof.
      apply twins𑁒update.
    Qed.

    #[local] Lemma inv۰inner𑁒history۰at t γ front :
      inv' t γ -∗
      consumer₁ t front ={⊤}=∗
        ∃ i,
        consumer₁ t front ∗
        node۰model γ front i.
    Proof.
      iIntros "#Hinv Hconsumer".
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (pointsto𑁒agree with "Ht_front Hconsumer") as %[= ->].
      assert (hist1 !! (length past1) = Some front) as Hlookup.
      { rewrite Hhist1 list_lookup_middle //. }
      iDestruct (xtchain𑁒lookup𑁒header with "Hhist") as "#Hfront_header"; first done.
      iDestruct (history۰at𑁒get (length past1) front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
      iSplitR "Hconsumer". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma mpsc_queue_1۰model𑁒exclusive γ vs1 vs2 :
      mpsc_queue_1۰model γ vs1 -∗
      mpsc_queue_1۰model γ vs2 -∗
      False.
    Proof.
      apply model₁𑁒exclusive.
    Qed.

    Lemma mpsc_queue_1۰consumer𑁒exclusive t :
      mpsc_queue_1۰consumer t -∗
      mpsc_queue_1۰consumer t -∗
      False.
    Proof.
      iIntros "(:consumer =1) (:consumer =2)".
      iDestruct (pointsto𑁒dfrac𑁒ne with "Hconsumer_1 Hconsumer_2") as %?; naive_solver.
    Qed.

    Lemma mpsc_queue_1٠create𑁒spec ι :
      {{{
        True
      }}}
        mpsc_queue_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mpsc_queue_1۰inv t γ ι ∗
        mpsc_queue_1۰model γ [] ∗
        mpsc_queue_1۰consumer t
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰block front as "#Hfront_header" "_" "(Hfront_next & _)".
      wp۰block t as "Hmeta" "(Ht_front & Ht_back & _)".
      iEval (rewrite -Qp.quarter_three_quarter) in "Ht_front".
      iDestruct "Ht_front" as "(Ht_front & Hconsumer)".

      iMod history𑁒alloc as "(%γ_history & Hhistory_auth)".
      iMod model𑁒alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

      pose γ :=
        {|mpsc_queue_1۰name۰inv := ι
        ; mpsc_queue_1۰name۰history := γ_history
        ; mpsc_queue_1۰name۰model := γ_model
        |}.

      iApply ("HΦ" $! t γ).
      iFrameStep.
      iApply inv_alloc.
      iExists [front], [], front, [], front, []. iFrameSteps.
      - rewrite list_elem_of_singleton //.
      - rewrite xtchain𑁒singleton. iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1٠front𑁒spec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{front}
      {{{
        front i
      , RET #front;
        node۰model γ front i
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      assert (hist !! (length past) = Some front) as Hlookup.
      { rewrite Hhist list_lookup_middle //. }
      iDestruct (xtchain𑁒lookup𑁒header with "Hhist") as "#Hfront_header"; first done.
      iDestruct (history۰at𑁒get _ front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
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
        node۰model γ back i
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      pose proof Hback as (i & Hlookup)%list_elem_of_lookup.
      iDestruct (xtchain𑁒lookup𑁒header with "Hhist") as "#Hback_header"; first done.
      iDestruct (history۰at𑁒get with "Hhistory_auth") as "#Hhistory_at_back"; first done.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Variant operation :=
      | IsEmpty (Ψ : bool → iProp Σ)
      | Pop (Ψ : option val → iProp Σ)
      | Other.
    Implicit Type op : operation.
    Variant operation' :=
      | IsEmpty'
      | Pop'
      | Other'.
    #[local] Instance operation'𑁒eq_dec : EqDecision operation' :=
      ltac:(solve_decision).
    #[local] Coercion operation۰to_operation' op :=
      match op with
      | IsEmpty _ =>
          IsEmpty'
      | Pop _ =>
          Pop'
      | Other =>
          Other'
      end.
    #[local] Definition is_empty۰au γ (Ψ : bool → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(mpsc_queue_1۰name۰inv), ∅ <{
        model₁ γ vs
      , COMM
        Ψ (bool_decide (vs = []))
      }>.
    #[local] Definition pop۰au γ (Ψ : option val → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(mpsc_queue_1۰name۰inv), ∅ <{
        model₁ γ (tail vs)
      , COMM
        Ψ (head vs)
      }>.
    #[local] Lemma next𑁒spec𑁒aux op t γ i node :
      {{{
        inv' t γ ∗
        history۰at γ i node ∗
        ( if decide (op = Other' :> operation') then True else
            consumer₁ t node
        ) ∗
        match op with
        | IsEmpty Ψ =>
            is_empty۰au γ Ψ
        | Pop Ψ =>
            pop۰au γ Ψ
        | Other =>
            True
        end
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
        ( if decide (op = Other' :> operation') then True else
            consumer₁ t node
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
          node۰model γ node' ˖i ∗
          match op with
          | IsEmpty Ψ =>
              Ψ false
          | Pop Ψ =>
              pop۰au γ Ψ
          | Other =>
              True
          end
        )
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & Hop) HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
      iDestruct (xtchain𑁒lookup𑁒acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
      wp۰load.
      iDestruct ("Hhist" with "Hnode") as "Hhist".
      destruct (hist !! ˖i) as [node' |] eqn:Hlookup'; simpl.

      - iDestruct (xtchain𑁒lookup𑁒header with "Hhist") as "#Hnode'_header"; first done.
        iDestruct (history۰at𑁒get ˖i with "Hhistory_auth") as "#Hhistory_at_node'"; first done.
        destruct op; [| iFrameSteps..].
        iDestruct "Hop" as "(Hconsumer & HΨ)".
        iDestruct (pointsto𑁒agree with "Ht_front Hconsumer") as %[= <-].

        iMod "HΨ" as "(%vs_ & (:model) & _ & HΨ)".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iAssert ⌜length past = i⌝%I as %Hpast_length.
        { iDestruct (xtchain𑁒NoDup with "Hhist") as %Hnodup.
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
        iDestruct (pointsto𑁒agree with "Ht_front Hconsumer") as %[= <-].

        iAssert ⌜length past = i⌝%I as %Hpast_length.
        { iDestruct (xtchain𑁒NoDup with "Hhist") as %Hnodup.
          iPureIntro. eapply NoDup_lookup; try done.
          rewrite Hhist list_lookup_middle //.
        }
        destruct_decide (length vs = 0) as ->%nil_length_inv | Hvs; last first.
        { iDestruct (big_sepL2_length with "Hnodes") as %?.
          exfalso.
          apply (f_equal length) in Hhist.
          opose proof* length𑁒lookup𑁒last as Heq; [done.. |].
          simpl_length/= in Hhist. lia.
        }

        destruct op; last done.

        + iMod "HΨ" as "(%vs & (:model) & _ & HΨ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
          iSteps.

        + iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
          iSteps.
    Qed.
    #[local] Lemma next𑁒spec {t γ i} node :
      {{{
        inv' t γ ∗
        history۰at γ i node
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
          ⌜res = §Null%V⌝
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node۰model γ node' ˖i
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node) HΦ".

      wp۰apply (next𑁒spec𑁒aux Other); iSteps.
    Qed.
    #[local] Lemma next𑁒spec𑁒is_empty {t γ i node} Ψ :
      {{{
        inv' t γ ∗
        history۰at γ i node ∗
        consumer₁ t node ∗
        is_empty۰au γ Ψ
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
        consumer₁ t node ∗
        ( ⌜res = §Null%V⌝ ∗
          Ψ true
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node۰model γ node' ˖i ∗
          Ψ false
        )
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & Ht_front & Hau) HΦ".

      wp۰apply (next𑁒spec𑁒aux (IsEmpty _) with "[$]").
      iFrameSteps.
    Qed.
    #[local] Lemma next𑁒spec𑁒pop {t γ i node} Ψ :
      {{{
        inv' t γ ∗
        history۰at γ i node ∗
        consumer₁ t node ∗
        pop۰au γ Ψ
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
        consumer₁ t node ∗
        ( ⌜res = §Null%V⌝ ∗
          Ψ None
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node۰model γ node' ˖i ∗
          pop۰au γ Ψ
        )
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & Ht_front & Hau) HΦ".

      wp۰apply (next𑁒spec𑁒aux (Pop _) with "[$]").
      iFrameSteps.
    Qed.

    Lemma mpsc_queue_1٠is_empty𑁒spec t γ ι :
      <<<
        mpsc_queue_1۰inv t γ ι ∗
        mpsc_queue_1۰consumer t
      | ∀∀ vs,
        mpsc_queue_1۰model γ vs
      >>>
        mpsc_queue_1٠is_empty #t @ ↑ι
      <<<
        mpsc_queue_1۰model γ vs
      | RET #(bool_decide (vs = []%list));
        mpsc_queue_1۰consumer t
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:consumer)) HΦ".

      iMod (inv۰inner𑁒history۰at with "Hinv Hconsumer") as "(%i & Ht_front & #Hfront_header & #Hhistory_at_front)".

      wp۰rec. wp۰load. wp۰match.
      wp۰apply+ (next𑁒spec𑁒is_empty (λ b, _ -∗ Φ #b)%I with "[$]").
      iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1٠push₀𑁒spec t γ i node new_back v :
      <<<
        inv' t γ ∗
        node۰model γ node i ∗
        new_back ↦ₕ Header §Node 2 ∗
        new_back.[next] ↦ §Null ∗
        new_back.[data] ↦ v
      | ∀∀ vs,
        mpsc_queue_1۰model γ vs
      >>>
        mpsc_queue_1٠push₀ #node #new_back @ ↑γ.(mpsc_queue_1۰name۰inv)
      <<<
        mpsc_queue_1۰model γ (vs ++ [v])
      | RET ();
        ∃ j,
        history۰at γ j new_back
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & (:node۰model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

      iLöb as "HLöb" forall (i node) "Hnode_header Hhistory_at_node".

      wp۰rec. wp۰match.
      wp۰apply+ (next𑁒spec with "[$]") as (res) "[-> | (%node' & -> & (:node۰model =node'))]"; last iSteps.
      wp۰pures.

      wp۰bind (CAS _ _ _).
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
      iDestruct (xtchain𑁒lookup with "Hhist") as "(Hhist1 & _ & Hnode & Hhist2)"; first done.
      destruct (hist !! ˖i) as [node' |] eqn:Hlookup'; simpl.

      - wp۰cas as _ | [=].
        iDestruct (xtchain𑁒lookup₂ with "Hhist1 Hnode_header Hnode Hhist2") as "Hhist"; [done | rewrite Hlookup' // |].
        iSplitR "Hnew_back_next Hnew_back_data HΦ". { iFrameSteps. }
        iSteps.

      - wp۰cas as ? | _; first done.
        iDestruct (xtchain𑁒lookup₂ with "Hhist1 Hnode_header Hnode []") as "Hhist"; [done | rewrite Hlookup' // | ..].
        { rewrite -(length𑁒lookup𑁒last hist i) // drop_all.
          iApply xtchain𑁒nil.
        }
        iDestruct (big_sepL2𑁒snoc₂ with "Hnodes Hnew_back_data") as "Hnodes".
        iDestruct (xtchain𑁒snoc₂ with "Hhist Hnew_back_header Hnew_back_next") as "Hhist".
        iMod (history𑁒update new_back with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at_new_back)".

        iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)".
        iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model𑁒update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁") as "HΦ".

        iSplitR "HΦ".
        { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
          iSteps; iPureIntro.
          - rewrite Hhist -assoc //.
          - set_solver.
        }
        iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1٠fix_back𑁒spec t γ i back j new_back :
      {{{
        inv' t γ ∗
        history۰at γ i back ∗
        node۰model γ new_back j
      }}}
        mpsc_queue_1٠fix_back #t #back #new_back
      {{{
        RET ();
        True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_back & (:node۰model =new_back)) HΦ".

      iLöb as "HLöb" forall (i back) "Hhistory_at_back".

      wp۰rec. wp۰match.

      wp۰bind (_ and _)%E.
      wp۰apply (wp𑁒wand itype۰bool) as (res) "(%b & ->)".
      { wp۰apply+ (next𑁒spec new_back with "[$]") as (res) "[-> | (%new_back' & -> & (:node۰model =new_back'))]"; last iSteps.
        wp۰pures.

        wp۰bind (CAS _ _ _).
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰cas as _ | [= ->]; first iSteps.
        iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_new_back") as %Hnew_back%list_elem_of_lookup_2.
        iSteps.
      }

      destruct b; last iSteps.
      wp۰apply+ domain٠yield𑁒spec.
      wp۰apply+ (back𑁒spec with "Hinv") as (back' i') "(:node۰model =back')".
      iApply ("HLöb" with "HΦ Hhistory_at_back'").
    Qed.

    Lemma mpsc_queue_1٠push𑁒spec t γ ι v :
      <<<
        mpsc_queue_1۰inv t γ ι
      | ∀∀ vs,
        mpsc_queue_1۰model γ vs
      >>>
        mpsc_queue_1٠push #t v @ ↑ι
      <<<
        mpsc_queue_1۰model γ (vs ++ [v])
      | RET ();
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec.
      wp۰block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
      wp۰match.
      wp۰apply+ (back𑁒spec with "Hinv") as (back i) "(:node۰model =back)".
      wp۰apply+ (mpsc_queue_1٠push₀𑁒spec with "[$]").
      iApply (atomic_update𑁒wand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
      wp۰apply+ (mpsc_queue_1٠fix_back𑁒spec with "[] HΦ"); first iSteps.
    Qed.

    #[local] Lemma mpsc_queue_1٠pop𑁒spec𑁒aux t γ :
      <<<
        inv' t γ ∗
        consumer₂ t
      | ∀∀ vs,
        model₁ γ vs
      >>>
        mpsc_queue_1٠pop #t @ ↑γ.(mpsc_queue_1۰name۰inv)
      <<<
        model₁ γ (tail vs)
      | RET head vs;
        consumer₂ t
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & (:consumer₂)) HΦ".

      iLöb as "HLöb".

      iMod (inv۰inner𑁒history۰at with "Hinv Hconsumer") as "(%i & Hconsumer & (:node۰model =front))".

      wp۰rec. wp۰load. wp۰match.
      wp۰apply+ (next𑁒spec𑁒pop (λ o, _ -∗ Φ o)%I with "[$]") as (res) "(Hconsumer & [(-> & HΦ) | (%new_front & -> & (:node۰model =new_front) & HΦ)])"; first iSteps.
      wp۰match. wp۰pures.

      wp۰bind (_ <-{front} _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (pointsto𑁒agree with "Ht_front Hconsumer") as %[= ->].
      iCombine "Ht_front Hconsumer" as "Ht_front".
      rewrite Qp.quarter_three_quarter.
      wp۰store.
      iEval (rewrite -Qp.quarter_three_quarter) in "Ht_front".
      iDestruct "Ht_front" as "(Ht_front & Hconsumer)".
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_front") as %Hlookup.
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_new_front") as %Hlookup_new.
      iAssert ⌜length past1 = i⌝%I as %Hpast1_length.
      { iDestruct (xtchain𑁒NoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist1 list_lookup_middle //.
      }
      rewrite Hhist1 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup_new; first lia.
      rewrite Nat.add_1_r Hpast1_length Nat.sub_diag in Hlookup_new.
      destruct nodes1 as [| node nodes1]; first done. injection Hlookup_new as ->.
      rewrite (assoc _ _ [_]) in Hhist1.
      iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hnew_front_data & Hnodes)".

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Hconsumer Hnew_front_data HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    Lemma mpsc_queue_1٠pop𑁒spec t γ ι :
      <<<
        mpsc_queue_1۰inv t γ ι ∗
        mpsc_queue_1۰consumer t
      | ∀∀ vs,
        mpsc_queue_1۰model γ vs
      >>>
        mpsc_queue_1٠pop #t @ ↑ι
      <<<
        mpsc_queue_1۰model γ (tail vs)
      | RET head vs;
        mpsc_queue_1۰consumer t
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:consumer)) HΦ".

      wp۰apply (mpsc_queue_1٠pop𑁒spec𑁒aux with "[$]").
      iAuIntro.
      iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model)".
      iAaccIntro with "Hmodel₁"; iSteps.
    Qed.
  End mpsc_queue_1۰G.

  #[global] Opaque mpsc_queue_1۰inv.
  #[global] Opaque mpsc_queue_1۰model.
  #[global] Opaque mpsc_queue_1۰consumer.
End base.

Require zoo_saturn.mpsc_queue_1__opaque.

Section mpsc_queue_1۰G.
  Context `{mpsc_queue_1۰G : MpscQueue1G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition mpsc_queue_1۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpsc_queue_1۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mpsc_queue_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpsc_queue_1۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition mpsc_queue_1۰consumer t : iProp Σ :=
    ∃ 𝑡,
    ⌜t = #𝑡⌝ ∗
    base.mpsc_queue_1۰consumer 𝑡.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %𝑡{}
      & {%Heq{};->}
      & Hconsumer{_{}}
      )
    ".

  #[global] Instance mpsc_queue_1۰model𑁒timeless t vs :
    Timeless (mpsc_queue_1۰model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_1۰consumer𑁒timeless t :
    Timeless (mpsc_queue_1۰consumer t ).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_queue_1۰inv𑁒persistent t ι :
    Persistent (mpsc_queue_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma mpsc_queue_1۰model𑁒exclusive t vs1 vs2 :
    mpsc_queue_1۰model t vs1 -∗
    mpsc_queue_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpsc_queue_1۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma mpsc_queue_1۰consumer𑁒exclusive t :
    mpsc_queue_1۰consumer t -∗
    mpsc_queue_1۰consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iApply (base.mpsc_queue_1۰consumer𑁒exclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma mpsc_queue_1٠create𑁒spec ι :
    {{{
      True
    }}}
      mpsc_queue_1٠create ()
    {{{
      t
    , RET t;
      mpsc_queue_1۰inv t ι ∗
      mpsc_queue_1۰model t [] ∗
      mpsc_queue_1۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.mpsc_queue_1٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel & Hconsumer)".
    iMod (meta𑁒set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma mpsc_queue_1٠is_empty𑁒spec t ι :
    <<<
      mpsc_queue_1۰inv t ι ∗
      mpsc_queue_1۰consumer t
    | ∀∀ vs,
      mpsc_queue_1۰model t vs
    >>>
      mpsc_queue_1٠is_empty t @ ↑ι
    <<<
      mpsc_queue_1۰model t vs
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_1۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.

    awp۰apply (base.mpsc_queue_1٠is_empty𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =3)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_3") as %->. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_3"; iSteps.
    }
  Qed.

  Lemma mpsc_queue_1٠push𑁒spec t ι v :
    <<<
      mpsc_queue_1۰inv t ι
    | ∀∀ vs,
      mpsc_queue_1۰model t vs
    >>>
      mpsc_queue_1٠push t v @ ↑ι
    <<<
      mpsc_queue_1۰model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.mpsc_queue_1٠push𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma mpsc_queue_1٠pop𑁒spec t ι :
    <<<
      mpsc_queue_1۰inv t ι ∗
      mpsc_queue_1۰consumer t
    | ∀∀ vs,
      mpsc_queue_1۰model t vs
    >>>
      mpsc_queue_1٠pop t @ ↑ι
    <<<
      mpsc_queue_1۰model t (tail vs)
    | RET head vs;
      mpsc_queue_1۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.

    awp۰apply (base.mpsc_queue_1٠pop𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =3)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_3") as %->. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_3"; iSteps.
    }
  Qed.
End mpsc_queue_1۰G.

#[global] Opaque mpsc_queue_1۰inv.
#[global] Opaque mpsc_queue_1۰model.
#[global] Opaque mpsc_queue_1۰consumer.
