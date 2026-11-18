Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Export zoo_saturn.queue_mpsc_1__code.
Require Import zoo_saturn.queue_mpsc_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front node back new_back : location.
Implicit Type hist past nodes : list location.
Implicit Type v backoff : val.
Implicit Type o : option val.
Implicit Type vs : list val.

Zoo name :=
  { self : location
  ; inv : namespace
  ; history : gname
  ; model : gname
  }.

Zoo global :=
  { history : mono_list location
  ; model : twins (leibnizO (list val))
  }.

Section queue_mpsc_1۰G.
  Context `{queue_mpsc_1۰G : QueueMpsc1G Σ}.

  #[local] Definition history۰auth' γ_history hist :=
    mono_list۰auth γ_history (DfracOwn 1) hist.
  #[local] Definition history۰auth γ hist :=
    history۰auth' γ.(queue_mpsc_1۰name۰history) hist.
  #[local] Definition history۰at γ i node :=
    mono_list۰at γ.(queue_mpsc_1۰name۰history) i node.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(queue_mpsc_1۰name۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(queue_mpsc_1۰name۰model) vs.

  #[local] Definition node۰model γ node i : iProp Σ :=
    node ↦ₕ Header §Node 2 ∗
    history۰at γ i node.
  #[local] Instance : CustomIpat "node۰model" :=
    " ( #H{}_header
      & #Hhistory_at_{}
      )
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ hist past front nodes back vs,
    ⌜hist = past ++ front :: nodes⌝ ∗
    ⌜back ∈ hist⌝ ∗
    γ.(queue_mpsc_1۰name۰self).[front] ↦{#1/4} #front ∗
    γ.(queue_mpsc_1۰name۰self).[back] ↦ #back ∗
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
  #[local] Definition inv' γ :=
    inv γ.(queue_mpsc_1۰name۰inv) (inv۰inner γ).
  Please Definition queue_mpsc_1۰inv γ ι : iProp Σ :=
    ⌜ι = γ.(queue_mpsc_1۰name۰inv)⌝ ∗
    inv' γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( ->
      & #Hinv
      )
    ".

  Please Definition queue_mpsc_1۰model :=
    model₁.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  #[local] Definition consumer₁ γ front : iProp Σ :=
    γ.(queue_mpsc_1۰name۰self).[front] ↦{#3/4} #front.
  #[local] Definition consumer₂ γ : iProp Σ :=
    ∃ front,
    consumer₁ γ front.
  #[local] Instance : CustomIpat "consumer₂" :=
    " ( %front{}
      & Hconsumer{_{}}
      )
    ".
  Please Definition queue_mpsc_1۰consumer :=
    consumer₂.
  #[local] Instance : CustomIpat "consumer" :=
    " (:consumer₂)
    ".

  Zoo derive Timeless for queue_mpsc_1۰model.
  Zoo derive Timeless for queue_mpsc_1۰consumer.

  Zoo derive Persistent for queue_mpsc_1۰inv.

  #[local] Lemma historyｰalloc front :
    ⊢ |==>
      ∃ γ_history,
      history۰auth' γ_history [front].
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma history۰atｰget {γ hist} i node :
    hist !! i = Some node →
    history۰auth γ hist ⊢
    history۰at γ i node.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  #[local] Lemma history۰atｰlookup γ hist i node :
    history۰auth γ hist -∗
    history۰at γ i node -∗
    ⌜hist !! i = Some node⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma historyｰupdate {γ hist} node :
    history۰auth γ hist ⊢ |==>
      history۰auth γ (hist ++ [node]) ∗
      history۰at γ (length hist) node.
  Proof.
    iIntros "Hauth".
    iMod (mono_listｰupdateｰsnoc with "Hauth") as "Hauth".
    iDestruct (history۰atｰget with "Hauth") as "#Hat".
    { rewrite lookup_snoc_Some. naive. }
    iSteps.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma inv۰innerｰhistory۰at γ front :
    inv' γ -∗
    consumer₁ γ front ={⊤}=∗
      ∃ i,
      consumer₁ γ front ∗
      node۰model γ front i.
  Proof.
    iIntros "#Hinv Hconsumer".
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (pointstoｰagree with "Ht_front Hconsumer") as %[= ->].
    assert (hist1 !! (length past1) = Some front) as Hlookup.
    { rewrite Hhist1 list_lookup_middle //. }
    iDestruct (xtchainｰlookupｰheader with "Hhist") as "#Hfront_header"; first done.
    iDestruct (history۰atｰget (length past1) front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
    iSplitR "Hconsumer". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma queue_mpsc_1۰modelｰexclusive γ vs1 vs2 :
    queue_mpsc_1۰model γ vs1 -∗
    queue_mpsc_1۰model γ vs2 -∗
    False.
  Proof.
    apply model₁ｰexclusive.
  Qed.

  Lemma queue_mpsc_1۰consumerｰexclusive γ :
    queue_mpsc_1۰consumer γ -∗
    queue_mpsc_1۰consumer γ -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)".
    iDestruct (pointstoｰdfracｰne with "Hconsumer_1 Hconsumer_2") as %?; naive.
  Qed.

  Lemma queue_mpsc_1٠createｰspec ι :
    {{{
      True
    }}}
      queue_mpsc_1٠create ()
    {{{
      γ
    , RET γ;
      queue_mpsc_1۰inv γ ι ∗
      queue_mpsc_1۰model γ [] ∗
      queue_mpsc_1۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰block front as "Hfront_next" header:"#Hfront_header".
    wp۰block t as "Ht_front Ht_back".
    iEval (rewrite -Qp.quarter_three_quarter) in "Ht_front".
    iDestruct "Ht_front" as "(Ht_front & Hconsumer)".

    iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|queue_mpsc_1۰name۰self := t
      ; queue_mpsc_1۰name۰inv := ι
      ; queue_mpsc_1۰name۰history := γ_history
      ; queue_mpsc_1۰name۰model := γ_model
      |}.

    iApply ("HΦ" $! γ).
    iFrameStep.
    iApply inv_alloc.
    iExists [front], [], front, [], front, []. iFrameSteps.
    - rewrite list_elem_of_singleton //.
    - rewrite xtchainｰsingleton. iSteps.
  Qed.

  #[local] Lemma queue_mpsc_1٠frontｰspec γ :
    {{{
      inv' γ
    }}}
      (#γ.(queue_mpsc_1۰name۰self)).{front}
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
    iDestruct (xtchainｰlookupｰheader with "Hhist") as "#Hfront_header"; first done.
    iDestruct (history۰atｰget _ front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma backｰspec γ :
    {{{
      inv' γ
    }}}
      (#γ.(queue_mpsc_1۰name۰self)).{back}
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
    iDestruct (xtchainｰlookupｰheader with "Hhist") as "#Hback_header"; first done.
    iDestruct (history۰atｰget with "Hhistory_auth") as "#Hhistory_at_back"; first done.
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
  #[local] Please derive EqDecision for operation'.
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
    }> @ ⊤ ∖ ↑γ.(queue_mpsc_1۰name۰inv), ∅ <{
      model₁ γ vs
    , COMM
      Ψ (bool_decide (vs = []))
    }>.
  #[local] Definition pop۰au γ (Ψ : option val → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(queue_mpsc_1۰name۰inv), ∅ <{
      model₁ γ (tail vs)
    , COMM
      Ψ (head vs)
    }>.
  #[local] Lemma nextｰspecｰaux op γ i node :
    {{{
      inv' γ ∗
      history۰at γ i node ∗
      ( if decide (op = Other' :> operation') then True else
          consumer₁ γ node
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
          consumer₁ γ node
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
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
    iDestruct (xtchainｰlookupｰacc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
    wp۰load.
    iDestruct ("Hhist" with "Hnode") as "Hhist".
    destruct (hist !! ˖i) as [node' |] eqn:Hlookup'; simpl.

    - iDestruct (xtchainｰlookupｰheader with "Hhist") as "#Hnode'_header"; first done.
      iDestruct (history۰atｰget ˖i with "Hhistory_auth") as "#Hhistory_at_node'"; first done.
      destruct op; [| iFrameSteps..].
      iDestruct "Hop" as "(Hconsumer & HΨ)".
      iDestruct (pointstoｰagree with "Ht_front Hconsumer") as %[= <-].

      iMod "HΨ" as "(%vs_ & (:model) & _ & HΨ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΨ" with "Hmodel₁") as "HΨ".

      iAssert ⌜length past = i⌝%I as %Hpast_length.
      { iDestruct (xtchainｰNoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist list_lookup_middle //.
      }
      rewrite -(bool_decide_ext _ _ (length_zero_iff_nil _)).
      iDestruct (big_sepL2_length with "Hnodes") as %<-.
      rewrite bool_decide_eq_false_2.
      { apply lookup_lt_Some in Hlookup'.
        lengths/=. lia.
      }

      iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
      iSteps.

    - destruct_decide (op = Other' :> operation').
      { destruct op; try done. iSteps. }
      iDestruct "Hop" as "(Hconsumer & HΨ)".
      iDestruct (pointstoｰagree with "Ht_front Hconsumer") as %[= <-].

      iAssert ⌜length past = i⌝%I as %Hpast_length.
      { iDestruct (xtchainｰNoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist list_lookup_middle //.
      }
      destruct_decide (length vs = 0) as ->%nil_length_inv | Hvs; last first.
      { iDestruct (big_sepL2_length with "Hnodes") as %?.
        exfalso.
        opose proof* lengthｰlookupｰlast as Heq; [done.. |].
        lengths/=. lia.
      }

      destruct op; last done.

      + iMod "HΨ" as "(%vs & (:model) & _ & HΨ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
        iSteps.

      + iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΨ" with "Hmodel₁") as "HΨ".

        iSplitR "Hconsumer HΨ HΦ". { iFrameSteps. }
        iSteps.
  Qed.
  #[local] Lemma nextｰspec {γ i} node :
    {{{
      inv' γ ∗
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

    wp۰apply (nextｰspecｰaux Other); iSteps.
  Qed.
  #[local] Lemma nextｰspecｰis_empty {γ i node} Ψ :
    {{{
      inv' γ ∗
      history۰at γ i node ∗
      consumer₁ γ node ∗
      is_empty۰au γ Ψ
    }}}
      (#node).{next}
    {{{
      res
    , RET res;
      consumer₁ γ node ∗
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

    wp۰apply (nextｰspecｰaux (IsEmpty _) with "[$]").
    iFrameSteps.
  Qed.
  #[local] Lemma nextｰspecｰpop {γ i node} Ψ :
    {{{
      inv' γ ∗
      history۰at γ i node ∗
      consumer₁ γ node ∗
      pop۰au γ Ψ
    }}}
      (#node).{next}
    {{{
      res
    , RET res;
      consumer₁ γ node ∗
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

    wp۰apply (nextｰspecｰaux (Pop _) with "[$]").
    iFrameSteps.
  Qed.

  Lemma queue_mpsc_1٠is_emptyｰspec γ ι :
    <<<
      queue_mpsc_1۰inv γ ι ∗
      queue_mpsc_1۰consumer γ
    | ∀∀ vs,
      queue_mpsc_1۰model γ vs
    >>>
      queue_mpsc_1٠is_empty γ
      @ ↑ι
    <<<
      queue_mpsc_1۰model γ vs
    | RET #(bool_decide (vs = []%list));
      queue_mpsc_1۰consumer γ
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ".

    iMod (inv۰innerｰhistory۰at with "Hinv Hconsumer") as "(%i & Ht_front & #Hfront_header & #Hhistory_at_front)".

    wp۰rec. wp۰load. wp۰match.
    wp۰apply+ (nextｰspecｰis_empty (λ b, _ -∗ Φ #b)%I with "[$]").
    iSteps.
  Qed.

  #[local] Lemma queue_mpsc_1٠push₂ｰspec γ i node new_back v backoff :
    <<<
      inv' γ ∗
      node۰model γ node i ∗
      new_back ↦ₕ Header §Node 2 ∗
      new_back.[next] ↦ §Null ∗
      new_back.[data] ↦ v ∗
      backoff۰model backoff
    | ∀∀ vs,
      queue_mpsc_1۰model γ vs
    >>>
      queue_mpsc_1٠push₂ #node #new_back backoff
      @ ↑γ.(queue_mpsc_1۰name۰inv)
    <<<
      queue_mpsc_1۰model γ (vs ++ [v])
    | RET ();
      ∃ j,
      history۰at γ j new_back
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:node۰model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data& Hbackoff) HΦ".

    iLöb as "HLöb" forall (i node backoff) "Hnode_header Hhistory_at_node".

    wp۰rec. wp۰match.
    wp۰apply+ (nextｰspec with "[$]") as (res) "[-> | (%node' & -> & (:node۰model =node'))]"; last iSteps.
    wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
    iDestruct (xtchainｰlookup with "Hhist") as "(Hhist1 & _ & Hnode & Hhist2)"; first done.
    destruct (hist !! ˖i) as [node' |] eqn:Hlookup'; simpl.

    - wp۰cas as _ | [=].
      iDestruct (xtchainｰlookup₂ with "Hhist1 Hnode_header Hnode Hhist2") as "Hhist"; [done | rewrite Hlookup' // |].
      iSplitR "Hnew_back_next Hnew_back_data Hbackoff HΦ". { iFrameSteps. }
      iSteps.

    - wp۰cas as ? | _; first done.
      iDestruct (xtchainｰlookup₂ with "Hhist1 Hnode_header Hnode []") as "Hhist"; [done | rewrite Hlookup' // | ..].
      { rewrite -(lengthｰlookupｰlast hist i) // drop_all.
        iApply xtchainｰnil.
      }
      iDestruct (big_sepL2ｰsnoc₂ with "Hnodes Hnew_back_data") as "Hnodes".
      iDestruct (xtchainｰsnoc₂ with "Hhist Hnew_back_header Hnew_back_next") as "Hhist".
      iMod (historyｰupdate new_back with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at_new_back)".

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "HΦ".
      { iExists (hist ++ [new_back]), past, front, (nodes ++ [new_back]), back, (vs ++ [v]).
        iSteps; iPureIntro.
        - rewrite Hhist -assoc //.
        - set_solver.
      }
      iSteps.
  Qed.

  #[local] Lemma queue_mpsc_1٠push₁ｰspec γ i node new_back v :
    <<<
      inv' γ ∗
      node۰model γ node i ∗
      new_back ↦ₕ Header §Node 2 ∗
      new_back.[next] ↦ §Null ∗
      new_back.[data] ↦ v
    | ∀∀ vs,
      queue_mpsc_1۰model γ vs
    >>>
      queue_mpsc_1٠push₁ #node #new_back
      @ ↑γ.(queue_mpsc_1۰name۰inv)
    <<<
      queue_mpsc_1۰model γ (vs ++ [v])
    | RET ();
      ∃ j,
      history۰at γ j new_back
    >>>.
  Proof.
    iIntros "%Φ (Hinv & Hnode & Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

    wp۰rec.
    wp۰apply+ (queue_mpsc_1٠push₂ｰspec with "[- HΦ] HΦ"). 1: iFrameSteps.
  Qed.

  #[local] Lemma queue_mpsc_1٠fix_back₁ｰspec γ i back j new_back backoff :
    {{{
      inv' γ ∗
      history۰at γ i back ∗
      node۰model γ new_back j ∗
      backoff۰model backoff
    }}}
      queue_mpsc_1٠fix_back₁ γ #back #new_back backoff
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hhistory_at_back & (:node۰model =new_back) & Hbackoff) HΦ".

    iLöb as "HLöb" forall (i back backoff) "Hhistory_at_back".

    wp۰rec. wp۰match.

    wp۰bind (_ 𝗮𝗻𝗱 _)%E.
    wp۰apply (wpｰwand itype۰bool) as (res) "(%b & ->)".
    { wp۰apply+ (nextｰspec new_back with "[$]") as (res) "[-> | (%new_back' & -> & (:node۰model =new_back'))]"; last iSteps.
      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      wp۰cas as _ | [= ->]; first iSteps.
      iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_new_back") as %Hnew_back%list_elem_of_lookup_2.
      iSteps.
    }

    destruct b; last iSteps.
    wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as "{% backoff} %backoff Hbackoff".
    wp۰apply+ (backｰspec with "Hinv") as (back' i') "(:node۰model =back')".
    iApply ("HLöb" with "Hbackoff HΦ Hhistory_at_back'").
  Qed.

  #[local] Lemma queue_mpsc_1٠fix_backｰspec γ i back j new_back :
    {{{
      inv' γ ∗
      history۰at γ i back ∗
      node۰model γ new_back j
    }}}
      queue_mpsc_1٠fix_back γ #back #new_back
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (Hinv & Hhistory_at_back & Hnew_back) HΦ".

    wp۰rec.
    wp۰apply+ (queue_mpsc_1٠fix_back₁ｰspec with "[- HΦ] HΦ"). 1: iFrameSteps.
  Qed.

  Lemma queue_mpsc_1٠pushｰspec γ ι v :
    <<<
      queue_mpsc_1۰inv γ ι
    | ∀∀ vs,
      queue_mpsc_1۰model γ vs
    >>>
      queue_mpsc_1٠push γ v
      @ ↑ι
    <<<
      queue_mpsc_1۰model γ (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰block new_back as "Hnew_back_next Hnew_back_data" header:"#Hnew_back_header".
    wp۰match.
    wp۰apply+ (backｰspec with "Hinv") as (back i) "(:node۰model =back)".
    wp۰apply+ (queue_mpsc_1٠push₁ｰspec with "[$]").
    iApply (aupdｰwand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
    wp۰apply+ (queue_mpsc_1٠fix_backｰspec with "[] HΦ"); first iSteps.
  Qed.

  #[local] Lemma queue_mpsc_1٠popｰspecｰaux γ :
    <<<
      inv' γ ∗
      consumer₂ γ
    | ∀∀ vs,
      model₁ γ vs
    >>>
      queue_mpsc_1٠pop γ
      @ ↑γ.(queue_mpsc_1۰name۰inv)
    <<<
      model₁ γ (tail vs)
    | RET head vs;
      consumer₂ γ
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & (:consumer₂)) HΦ".

    iLöb as "HLöb".

    iMod (inv۰innerｰhistory۰at with "Hinv Hconsumer") as "(%i & Hconsumer & (:node۰model =front))".

    wp۰rec. wp۰load. wp۰match.
    wp۰apply+ (nextｰspecｰpop (λ o, _ -∗ Φ o)%I with "[$]") as (res) "(Hconsumer & [(-> & HΦ) | (%new_front & -> & (:node۰model =new_front) & HΦ)])"; first iSteps.
    wp۰match. wp۰pures.

    wp۰bind (_ <-{front} _)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (pointstoｰagree with "Ht_front Hconsumer") as %[= ->].
    iCombine "Ht_front Hconsumer" as "Ht_front".
    rewrite Qp.quarter_three_quarter.
    wp۰store.
    iEval (rewrite -Qp.quarter_three_quarter) in "Ht_front".
    iDestruct "Ht_front" as "(Ht_front & Hconsumer)".
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_front") as %Hlookup.
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_new_front") as %Hlookup_new.
    iAssert ⌜length past1 = i⌝%I as %Hpast1_length.
    { iDestruct (xtchainｰNoDup with "Hhist") as %Hnodup.
      iPureIntro. eapply NoDup_lookup; try done.
      rewrite Hhist1 list_lookup_middle //.
    }
    rewrite Hhist1 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup_new; first lia.
    rewrite Nat.add_1_r Hpast1_length Nat.sub_diag in Hlookup_new.
    destruct nodes1 as [| node nodes1]; first done. injection Hlookup_new as ->.
    rewrite (assoc _ _ [_]) in Hhist1.
    iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hnew_front_data & Hnodes)".

    iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "Hmodel₁") as "HΦ".

    iSplitR "Hconsumer Hnew_front_data HΦ". { iFrameSteps. }
    iSteps.
  Qed.
  Lemma queue_mpsc_1٠popｰspec γ ι :
    <<<
      queue_mpsc_1۰inv γ ι ∗
      queue_mpsc_1۰consumer γ
    | ∀∀ vs,
      queue_mpsc_1۰model γ vs
    >>>
      queue_mpsc_1٠pop γ
      @ ↑ι
    <<<
      queue_mpsc_1۰model γ (tail vs)
    | RET head vs;
      queue_mpsc_1۰consumer γ
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ".

    awp۰apply (queue_mpsc_1٠popｰspecｰaux with "[$]").
    iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
    iAaccIntro with "Hmodel₁"; iSteps.
  Qed.
End queue_mpsc_1۰G.

Require zoo_saturn.queue_mpsc_1__opaque.

Please opacify.
