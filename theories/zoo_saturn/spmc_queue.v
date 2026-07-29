Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.relations.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.auth_twins.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Import zoo_std.domain.
Require Export zoo_saturn.spmc_queue__code.
Require Import zoo_saturn.spmc_queue__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front node back new_back : location.
Implicit Type hist past nodes : list location.
Implicit Type v : val.
Implicit Type vs ws : list val.
Implicit Type waiter : gname.
Implicit Type waiters : gmap gname nat.

Class SpmcQueueG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] spmc_queue۰G۰history۰G :: MonoListG Σ location
  ; #[local] spmc_queue۰G۰front۰G :: AuthNatMaxG Σ
  ; #[local] spmc_queue۰G۰model۰G :: AuthTwinsG Σ (leibnizO (list val)) suffix
  ; #[local] spmc_queue۰G۰waiters۰G :: ghost_mapG Σ gname nat
  ; #[local] spmc_queue۰G۰saved_pred۰G :: SavedPredG Σ bool
  }.

Definition spmc_queue۰Σ :=
  #[mono_list۰Σ location
  ; auth_nat_max۰Σ
  ; auth_twins۰Σ (leibnizO (list val)) suffix
  ; ghost_mapΣ gname nat
  ; saved_pred۰Σ bool
  ].
#[global] Instance subGｰspmc_queue۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG spmc_queue۰Σ Σ →
  SpmcQueueG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section spmc_queue۰G.
    Context `{spmc_queue۰G : SpmcQueueG Σ}.

    Implicit Type t : location.

    Record metadata :=
      { metadata۰inv : namespace
      ; metadata۰history : gname
      ; metadata۰front : gname
      ; metadata۰model : auth_twins۰name
      ; metadata۰waiters : gname
      }.
    Implicit Type γ : metadata.

    #[global] Instance metadataｰeq_dec : EqDecision metadata :=
      ltac:(solve_decision).
    #[global] Instance metadataｰcountable :
      Countable metadata.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition history۰auth' γ_history hist :=
      mono_list۰auth γ_history (DfracOwn (1/2)) hist.
    #[local] Definition history۰auth γ hist :=
      history۰auth' γ.(metadata۰history) hist.
    #[local] Definition history۰last' γ_history node : iProp Σ :=
      ∃ hist,
      mono_list۰auth γ_history (DfracOwn (1/2)) hist ∗
      ⌜last hist = Some node⌝.
    #[local] Instance : CustomIpat "history۰last" :=
      " ( %hist{}
        & Hauth{_{}}
        & %Hlast
        )
      ".
    #[local] Definition history۰last γ :=
      history۰last' γ.(metadata۰history).
    #[local] Definition history۰at γ i node :=
      mono_list۰at γ.(metadata۰history) i node.

    #[local] Definition front۰auth' γ_front i :=
      auth_nat_max۰auth γ_front (DfracOwn 1) i.
    #[local] Definition front۰auth γ i :=
      front۰auth' γ.(metadata۰front) i.
    #[local] Definition front۰lb γ i :=
      auth_nat_max۰lb γ.(metadata۰front) i.

    #[local] Definition producer' γ_model ws :=
      auth_twins۰auth _ γ_model ws.
    #[local] Definition producer γ :=
      producer' γ.(metadata۰model).

    #[local] Definition model₁' γ_model vs :=
      auth_twins۰twin₁ _ γ_model vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(metadata۰model).
    #[local] Definition model₂' γ_model vs :=
      auth_twins۰twin₂ _ γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(metadata۰model).

    #[local] Definition waiters۰auth' γ_waiters waiters :=
      ghost_map_auth γ_waiters 1 waiters.
    #[local] Definition waiters۰auth γ waiters :=
      waiters۰auth' γ.(metadata۰waiters) waiters.
    #[local] Definition waiters۰at γ waiter i :=
      ghost_map_elem γ.(metadata۰waiters) waiter (DfracOwn 1) i.

    #[local] Definition node۰model γ node i b : iProp Σ :=
      node ↦ₕ Header §Node 2 ∗
      history۰at γ i node ∗
      if b then front۰lb γ i else True%I.
    #[local] Instance : CustomIpat "node۰model" :=
      " ( #H{}_header
        & #Hhistory_at_{}
        & {{front}#Hfront_lb_{};_}
        )
      ".

    #[local] Definition waiter۰au γ (Ψ : bool → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(metadata۰inv), ∅ <{
        model₁ γ vs
      , COMM
        Ψ (bool_decide (vs = []))
      }>.
    #[local] Definition waiter۰model γ past waiter i : iProp Σ :=
      ∃ Ψ,
      saved_pred waiter Ψ ∗
      if decide (i < length past) then
        Ψ false
      else
        waiter۰au γ Ψ.

    #[local] Definition inv۰inner t γ : iProp Σ :=
      ∃ hist past front nodes vs waiters,
      ⌜hist = past ++ front :: nodes⌝ ∗
      t.[front] ↦ #front ∗
      xtchain (Header §Node 2) (DfracOwn 1) hist §Null ∗
      ([∗ list] node; v ∈ nodes; vs, node.[data] ↦ v) ∗
      history۰auth γ hist ∗
      front۰auth γ (length past) ∗
      model₂ γ vs ∗
      waiters۰auth γ waiters ∗
      ([∗ map] waiter ↦ i ∈ waiters, waiter۰model γ past waiter i).
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %hist{}
        & %past{}
        & %front{}
        & %nodes{}
        & %vs{}
        & %waiters{}
        & >%Hhist{}
        & >Ht_front
        & >Hhist
        & >Hnodes
        & >Hhistory_auth
        & >Hfront_auth
        & >Hmodel₂
        & >Hwaiters_auth
        & Hwaiters
        )
      ".
    #[local] Definition inv' t γ :=
      inv γ.(metadata۰inv) (inv۰inner t γ).
    Definition spmc_queue۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(metadata۰inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Hinv
        )
      ".

    Definition spmc_queue۰producer t γ ws : iProp Σ :=
      ∃ back,
      t.[back] ↦ #back ∗
      back ↦ₕ Header §Node 2 ∗
      history۰last γ back ∗
      producer γ ws.
    #[local] Instance : CustomIpat "producer" :=
      " ( %back{}
        & Ht_back{_{}}
        & #Hback{}_header
        & Hhistory_last{_{}}
        & Hproducer{_{}}
        )
      ".

    Definition spmc_queue۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[global] Instance spmc_queue۰modelｰtimeless γ vs :
      Timeless (spmc_queue۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance spmc_queue۰producerｰtimeless t γ ws :
      Timeless (spmc_queue۰producer t γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance spmc_queue۰invｰpersistent t γ ι :
      Persistent (spmc_queue۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma historyｰalloc front :
      ⊢ |==>
        ∃ γ_history,
        history۰auth' γ_history [front] ∗
        history۰last' γ_history front.
    Proof.
      iMod mono_listｰalloc as "(%γ_history & $ & $)".
      iSteps.
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
    #[local] Lemma historyｰauthｰlast γ hist node :
      history۰auth γ hist -∗
      history۰last γ node -∗
      ⌜last hist = Some node⌝.
    Proof.
      iIntros "Hauth_1 (:history۰last =2)".
      iDestruct (mono_list۰authｰagree with "Hauth_1 Hauth_2") as %<-.
      iSteps.
    Qed.
    #[local] Lemma historyｰupdate {γ hist node} node' :
      history۰auth γ hist -∗
      history۰last γ node ==∗
        history۰auth γ (hist ++ [node']) ∗
        history۰last γ node'.
    Proof.
      iIntros "Hauth_1 (:history۰last =2)".
      rewrite /history۰auth /history۰auth'.
      iDestruct (mono_list۰authｰcombine with "Hauth_1 Hauth_2") as "(<- & Hauth)". rewrite dfrac_op_own Qp.half_half.
      iMod (mono_listｰupdateｰsnoc with "Hauth") as "($ & $)".
      rewrite last_snoc //.
    Qed.
    Opaque history۰last'.

    #[local] Lemma frontｰalloc :
      ⊢ |==>
        ∃ γ_front,
        front۰auth' γ_front 0.
    Proof.
      apply auth_nat_maxｰalloc.
    Qed.
    #[local] Lemma front۰lbｰget γ i :
      front۰auth γ i ⊢
      front۰lb γ i.
    Proof.
      apply auth_nat_max۰lbｰget.
    Qed.
    #[local] Lemma front۰lbｰvalid γ i1 i2 :
      front۰auth γ i1 -∗
      front۰lb γ i2 -∗
      ⌜i2 ≤ i1⌝.
    Proof.
      apply auth_nat_max۰lbｰvalid.
    Qed.
    #[local] Lemma frontｰupdate {γ i} i' :
      i ≤ i' →
      front۰auth γ i ⊢ |==>
      front۰auth γ i'.
    Proof.
      apply auth_nat_maxｰupdate.
    Qed.

    #[local] Lemma producerｰvalid γ ws vs :
      producer γ ws -∗
      model₁ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      rewrite -preorderｰrtc.
      apply: auth_twinsｰvalid₁.
    Qed.
    #[local] Lemma producerｰexclusive γ ws1 ws2 :
      producer γ ws1 -∗
      producer γ ws2 -∗
      False.
    Proof.
      apply: auth_twins۰authｰexclusive.
    Qed.

    #[local] Lemma modelｰproducerｰalloc :
      ⊢ |==>
        ∃ γ_model,
        producer' γ_model [] ∗
        model₁' γ_model [] ∗
        model₂' γ_model [].
    Proof.
      apply auth_twinsｰalloc.
    Qed.
    #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply auth_twins۰twin₁ｰexclusive.
    Qed.
    #[local] Lemma modelｰagree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: auth_twinsｰagreeｰL.
    Qed.
    #[local] Lemma modelｰpush {γ ws vs1 vs2} v :
      producer γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        producer γ (vs1 ++ [v]) ∗
        model₁ γ (vs1 ++ [v]) ∗
        model₂ γ (vs1 ++ [v]).
    Proof.
      apply auth_twinsｰupdateｰauth.
    Qed.
    #[local] Lemma modelｰpop γ v vs1 vs2 :
      model₁ γ (v :: vs1) -∗
      model₂ γ vs2 ==∗
        model₁ γ vs1 ∗
        model₂ γ vs1.
    Proof.
      apply: auth_twinsｰupdateｰtwinsｰL.
      rewrite preorderｰrtc. solve_suffix.
    Qed.

    #[local] Lemma waitersｰalloc :
      ⊢ |==>
        ∃ γ_waiters,
        waiters۰auth' γ_waiters ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ_waiters & Hwaiters_auth & _)".
      iSteps.
    Qed.
    #[local] Lemma waitersｰinsert {γ waiters} i Ψ :
      waiters۰auth γ waiters ⊢ |==>
        ∃ waiter,
        waiters۰auth γ (<[waiter := i]> waiters) ∗
        saved_pred waiter Ψ ∗
        waiters۰at γ waiter i.
    Proof.
      iIntros "Hwaiters_auth".
      iMod (saved_predｰallocｰcofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & $)".
      rewrite not_elem_of_dom in Hwaiter.
      iApply (ghost_map_insert with "Hwaiters_auth"); first done.
    Qed.
    #[local] Lemma waitersｰdelete γ waiters waiter i :
      waiters۰auth γ waiters -∗
      waiters۰at γ waiter i ==∗
        ⌜waiters !! waiter = Some i⌝ ∗
        waiters۰auth γ (delete waiter waiters).
    Proof.
      iIntros "Hwaiters_auth Hwaiters_at".
      iDestruct (ghost_map_lookup with "Hwaiters_auth Hwaiters_at") as %?.
      iMod (ghost_map_delete with "Hwaiters_auth Hwaiters_at") as "$".
      iSteps.
    Qed.

    Lemma spmc_queue۰modelｰexclusive γ vs1 vs2 :
      spmc_queue۰model γ vs1 -∗
      spmc_queue۰model γ vs2 -∗
      False.
    Proof.
      apply model₁ｰexclusive.
    Qed.

    Lemma spmc_queue۰producerｰvalid t γ vs ws :
      spmc_queue۰producer t γ ws -∗
      spmc_queue۰model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:producer =1) (:model =2)".
      iApply (producerｰvalid with "Hproducer_1 Hmodel₁_2").
    Qed.
    Lemma spmc_queue۰producerｰexclusive t γ ws1 ws2 :
      spmc_queue۰producer t γ ws1 -∗
      spmc_queue۰producer t γ ws2 -∗
      False.
    Proof.
      iIntros "(:producer =1) (:producer =2)".
      iApply (producerｰexclusive with "Hproducer_1 Hproducer_2").
    Qed.

    Lemma spmc_queue٠createｰspec ι :
      {{{
        True
      }}}
        spmc_queue٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        spmc_queue۰inv t γ ι ∗
        spmc_queue۰model γ [] ∗
        spmc_queue۰producer t γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰block front as "#Hfront_header" "_" "(Hfront_next & _)".
      wp۰block t as "Hmeta" "(Ht_front & Ht_back & _)".

      iMod historyｰalloc as "(%γ_history & Hhistory_auth & Hhistory_last)".
      iMod frontｰalloc as "(%γ_front & Hfront_auth)".
      iMod modelｰproducerｰalloc as "(%γ_model & Hproducer & Hmodel₁ & Hmodel₂)".
      iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ :=
        {|metadata۰inv := ι
        ; metadata۰history := γ_history
        ; metadata۰front := γ_front
        ; metadata۰model := γ_model
        ; metadata۰waiters := γ_waiters
        |}.

      iApply ("HΦ" $! t γ).
      iFrame "#∗". iStep.
      iApply inv_alloc.
      iExists [front], [], front, [], [], ∅. iFrameSteps.
      rewrite xtchainｰsingleton big_sepM_empty. iSteps.
    Qed.

    #[local] Lemma frontｰspecｰstrong Ψ t γ :
      {{{
        inv' t γ ∗
        if Ψ is Some Ψ then
          waiter۰au γ Ψ
        else
          True
      }}}
        (#t).{front}
      {{{
        front i
      , RET #front;
        node۰model γ front i true ∗
        if Ψ is Some Ψ then
          ∃ waiter,
          saved_pred waiter Ψ ∗
          waiters۰at γ waiter i
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & HΨ) HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      assert (hist !! (length past) = Some front) as Hlookup.
      { rewrite Hhist list_lookup_middle //. }
      iDestruct (xtchainｰlookupｰheader with "Hhist") as "#Hfront_header"; first done.
      iDestruct (history۰atｰget _ front with "Hhistory_auth") as "#Hhistory_at"; first done.
      iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_front".
      destruct Ψ as [Ψ |]; last iSteps.
      iMod (waitersｰinsert (length past) Ψ with "Hwaiters_auth") as "(%waiter & Hwaiter_auth & #Hwaiter & Hwaiters_at)".
      iDestruct (big_sepM_insert_2 _ _ waiter (length past) with "[HΨ] Hwaiters") as "Hwaiters".
      { iExists Ψ. rewrite decide_False; first lia. iSteps. }
      iSplitR "Hwaiters_at HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma frontｰspec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{front}
      {{{
        front i
      , RET #front;
        node۰model γ front i true
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰apply (frontｰspecｰstrong None with "[$Hinv]").
      iSteps.
    Qed.

    Variant operation :=
      | IsEmpty waiter (Ψ : bool → iProp Σ)
      | Pop (Ψ : option val → iProp Σ)
      | Other.
    Implicit Type op : operation.
    Variant operation' :=
      | IsEmpty'
      | Pop'
      | Other'.
    #[local] Instance operation'ｰeq_dec : EqDecision operation' :=
      ltac:(solve_decision).
    #[local] Coercion operation۰to_operation' op :=
      match op with
      | IsEmpty _ _ =>
          IsEmpty'
      | Pop _ =>
          Pop'
      | Other =>
          Other'
      end.
    #[local] Definition pop۰au γ (Ψ : option val → iProp Σ) : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(metadata۰inv), ∅ <{
        model₁ γ (tail vs)
      , COMM
        Ψ (head vs)
      }>.
    #[local] Lemma nextｰspecｰaux op t γ i node :
      {{{
        inv' t γ ∗
        history۰at γ i node ∗
        ( if decide (op = Other' :> operation') then True else
            front۰lb γ i
        ) ∗
        match op with
        | IsEmpty waiter Ψ =>
            saved_pred waiter Ψ ∗
            waiters۰at γ waiter i ∗
            £ 1
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
          node۰model γ node' ˖i false ∗
          match op with
          | IsEmpty waiter Ψ =>
              Ψ false
          | Pop Ψ =>
              pop۰au γ Ψ
          | Other =>
              True
          end
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
        destruct op; [| iSteps..].
        iDestruct "Hop" as "(#Hfront_lb_node & #Hwaiter & Hwaiters_at & H£)".
        iMod (waitersｰdelete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
        iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
        iDestruct (saved_predｰagree false with "Hwaiter Hwaiter_") as "Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        destruct_decide (i = length past) as -> | Hi.

        + rewrite decide_False; first lia.

          iMod "HΨ" as "(%vs_ & Hmodel₁ & _ & HΨ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
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

        + iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_node") as %Hi_.
          rewrite decide_True; first lia.
          iSplitR "Heq HΨ HΦ". { iFrameSteps. }
          iSteps. iRewrite "Heq". iSteps.

      - destruct_decide (op = Other' :> operation').
        { destruct op; try done. iSteps. }
        iDestruct "Hop" as "(#Hfront_lb_node & Hop)".
        iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_node") as %Hi.
        opose proof* lengthｰlookupｰlast as Hlength; [done.. |].
        rewrite Hhist length_app /= in Hlength.
        assert (i = length past) as -> by lia.
        assert (length nodes = 0) as ->%nil_length_inv by lia.
        iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
        destruct op; last done.

        + iDestruct "Hop" as "(#Hwaiter & Hwaiters_at & H£)".
          iMod (waitersｰdelete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
          iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
          iDestruct (saved_predｰagree true with "Hwaiter Hwaiter_") as "Heq".
          iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
          rewrite decide_False; first lia.

          iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "Heq HΨ HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          iApply "HΦ".
          iLeft. iRewrite "Heq". iSteps.

        + iMod "Hop" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "HΨ HΦ". { iFrameSteps. }
          iSteps.
    Qed.
    #[local] Lemma nextｰspec t γ i node :
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
          node۰model γ node' ˖i false
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node) HΦ".

      wp۰apply (nextｰspecｰaux Other); iSteps.
    Qed.
    #[local] Lemma nextｰspecｰis_empty {t γ i node} waiter Ψ :
      {{{
        inv' t γ ∗
        history۰at γ i node ∗
        front۰lb γ i ∗
        saved_pred waiter Ψ ∗
        waiters۰at γ waiter i ∗
        £ 1
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
          ⌜res = §Null%V⌝ ∗
          Ψ true
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node۰model γ node' ˖i false ∗
          Ψ false
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & #Hfront_lb_node & #Hwaiter & Hwaiters_at & H£) HΦ".

      wp۰apply (nextｰspecｰaux (IsEmpty _ _) with "[$]").
      iSteps.
    Qed.
    #[local] Lemma nextｰspecｰpop {t γ i node} Ψ :
      {{{
        inv' t γ ∗
        history۰at γ i node ∗
        front۰lb γ i ∗
        pop۰au γ Ψ
      }}}
        (#node).{next}
      {{{
        res
      , RET res;
          ⌜res = §Null%V⌝ ∗
          Ψ None
        ∨ ∃ node',
          ⌜res = #node'⌝ ∗
          node۰model γ node' ˖i false ∗
          pop۰au γ Ψ
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_node & #Hfront_lb_node & Hau) HΦ".

      wp۰apply (nextｰspecｰaux (Pop _) with "[$]").
      iSteps.
    Qed.

    Lemma spmc_queue٠is_emptyｰspec t γ ι :
      <<<
        spmc_queue۰inv t γ ι
      | ∀∀ vs,
        spmc_queue۰model γ vs
      >>>
        spmc_queue٠is_empty #t @ ↑ι
      <<<
        spmc_queue۰model γ vs
      | RET #(bool_decide (vs = []%list));
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec credit:"H£".
      wp۰apply+ (frontｰspecｰstrong (Some $ λ b, Φ #b) with "[$Hinv HΦ]") as (node i) "((:node۰model =node front=) & %waiter & #Hwaiter & Hwaiters_at)".
      { rewrite /= /waiter۰au. iAuIntro.
        iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; iSteps.
      }
      wp۰match.
      wp۰apply+ (nextｰspecｰis_empty with "[$]"); iSteps.
    Qed.

    Lemma spmc_queue٠pushｰspec t γ ι ws v :
      <<<
        spmc_queue۰inv t γ ι ∗
        spmc_queue۰producer t γ ws
      | ∀∀ vs,
        spmc_queue۰model γ vs
      >>>
        spmc_queue٠push #t v @ ↑ι
      <<<
        spmc_queue۰model γ (vs ++ [v])
      | RET ();
        spmc_queue۰producer t γ (vs ++ [v])
      >>>.
    Proof.
      iIntros "%Φ ((:inv) & (:producer)) HΦ".

      wp۰rec.
      wp۰block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
      wp۰match. wp۰load. wp۰match.

      wp۰bind (_ <-{next} _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (historyｰauthｰlast with "Hhistory_auth Hhistory_last") as %?.
      wp۰apply (xtchain٠set_nextｰspecｰlast' new_back with "[$]") as "Hhist"; first done.
      iMod (historyｰupdate new_back with "Hhistory_auth Hhistory_last") as "(Hhistory_auth & Hhistory_last)".
      iDestruct (big_sepL2ｰsnoc₂ with "Hnodes Hnew_back_data") as "Hnodes".

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰpush v with "Hproducer Hmodel₁ Hmodel₂") as "(Hproducer & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Ht_back Hhistory_last Hproducer HΦ".
      { iFrameSteps. list_simplifier. done. }
      iSteps.
    Qed.

    #[local] Lemma spmc_queue٠popｰspecｰaux t γ :
      <<<
        inv' t γ
      | ∀∀ vs,
        model₁ γ vs
      >>>
        spmc_queue٠pop #t @ ↑γ.(metadata۰inv)
      <<<
        model₁ γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      iLöb as "HLöb".

      wp۰rec credit:"H£".
      wp۰apply+ (frontｰspec with "Hinv") as (front i) "(#Hfront_header & #Hhistory_at_front & #Hfront_lb_front)".
      wp۰match.
      wp۰apply+ (nextｰspecｰpop (λ o, _ -∗ Φ o)%I with "[$]") as (res) "[(-> & HΦ) | (%new_front & -> & (:node۰model =new_front) & HΦ)]"; first iSteps.
      wp۰match. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_new_front") as %Hlookup.
      iDestruct (xtchainｰlookupｰacc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
      wp۰cas as _ | [= <-]; first iSteps.
      iDestruct ("Hhist" with "Hnode") as "Hhist".
      iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_front") as %Hlookup_old.
      iAssert ⌜length past1 = i⌝%I as %Hpast_length.
      { iDestruct (xtchainｰNoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist1 list_lookup_middle //.
      }
      rewrite Hhist1 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup; first lia.
      rewrite Nat.add_1_r Hpast_length Nat.sub_diag in Hlookup.
      destruct nodes1 as [| node nodes1]; first done. injection Hlookup as ->.
      rewrite (assoc _ _ [_]) in Hhist1.
      iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hfront_data & Hnodes)".
      set past := past1 ++ [front].
      iMod (frontｰupdate (length past) with "Hfront_auth") as "Hfront_auth".
      { rewrite /past. simpl_length. lia. }
      iDestruct (big_sepMｰimplｰthreadｰfupd _ (waiter۰model γ past)%I with "Hwaiters Hmodel₂ [#]") as ">(Hwaiters & Hmodel₂)".
      { iIntros "!> %waiter %j %Hlookup (%P & #Hwaiter & HP) Hmodel₂".
        destruct (Nat.lt_trichotomy j (length past1)) as [Hj | [-> | Hj]].
        - rewrite decide_True //.
          rewrite /waiter۰model. setoid_rewrite decide_True; last first.
          { rewrite /past. simpl_length. lia. }
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /waiter۰model. setoid_rewrite decide_True; last first.
          { rewrite /past. simpl_length/=. lia. }
          iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /waiter۰model. setoid_rewrite decide_False; last first.
          { rewrite /past. simpl_length/=. lia. }
          iSteps.
      }

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰpop with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Hfront_data H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    Lemma spmc_queue٠popｰspec t γ ι :
      <<<
        spmc_queue۰inv t γ ι
      | ∀∀ vs,
        spmc_queue۰model γ vs
      >>>
        spmc_queue٠pop #t @ ↑ι
      <<<
        spmc_queue۰model γ (tail vs)
      | RET head vs;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰apply (spmc_queue٠popｰspecｰaux with "Hinv").
      iAuIntro.
      iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
      iAaccIntro with "Hmodel₁"; iSteps.
    Qed.
  End spmc_queue۰G.

  #[global] Opaque spmc_queue۰inv.
  #[global] Opaque spmc_queue۰producer.
  #[global] Opaque spmc_queue۰model.
End base.

Require zoo_saturn.spmc_queue__opaque.

Section spmc_queue۰G.
  Context `{spmc_queue۰G : SpmcQueueG Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition spmc_queue۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.spmc_queue۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition spmc_queue۰producer t ws : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.spmc_queue۰producer 𝑡 γ ws.
  #[local] Instance : CustomIpat "producer" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hproducer{_{}}
      )
    ".

  Definition spmc_queue۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.spmc_queue۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  #[global] Instance spmc_queue۰modelｰtimeless t vs :
    Timeless (spmc_queue۰model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_queue۰producerｰtimeless t ws :
    Timeless (spmc_queue۰producer t ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance spmc_queue۰invｰpersistent t ι :
    Persistent (spmc_queue۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma spmc_queue۰modelｰexclusive t vs1 vs2 :
    spmc_queue۰model t vs1 -∗
    spmc_queue۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.spmc_queue۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma spmc_queue۰producerｰvalid t vs ws :
    spmc_queue۰producer t ws -∗
    spmc_queue۰model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer =1) (:model =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.spmc_queue۰producerｰvalid with "Hproducer_1 Hmodel_2").
  Qed.
  Lemma spmc_queue۰producerｰexclusive t ws1 ws2 :
    spmc_queue۰producer t ws1 -∗
    spmc_queue۰producer t ws2 -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.spmc_queue۰producerｰexclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma spmc_queue٠createｰspec ι :
    {{{
      True
    }}}
      spmc_queue٠create ()
    {{{
      t
    , RET t;
      spmc_queue۰inv t ι ∗
      spmc_queue۰model t [] ∗
      spmc_queue۰producer t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.spmc_queue٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma spmc_queue٠is_emptyｰspec t ι :
    <<<
      spmc_queue۰inv t ι
    | ∀∀ vs,
      spmc_queue۰model t vs
    >>>
      spmc_queue٠is_empty t @ ↑ι
    <<<
      spmc_queue۰model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.spmc_queue٠is_emptyｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma spmc_queue٠pushｰspec t ι ws v :
    <<<
      spmc_queue۰inv t ι ∗
      spmc_queue۰producer t ws
    | ∀∀ vs,
      spmc_queue۰model t vs
    >>>
      spmc_queue٠push t v @ ↑ι
    <<<
      spmc_queue۰model t (vs ++ [v])
    | RET ();
      spmc_queue۰producer t (vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv =1) & (:producer =2)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.spmc_queue٠pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma spmc_queue٠popｰspec t ι :
    <<<
      spmc_queue۰inv t ι
    | ∀∀ vs,
      spmc_queue۰model t vs
    >>>
      spmc_queue٠pop t @ ↑ι
    <<<
      spmc_queue۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.spmc_queue٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End spmc_queue۰G.

#[global] Opaque spmc_queue۰inv.
#[global] Opaque spmc_queue۰producer.
#[global] Opaque spmc_queue۰model.
