Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Export zoo_saturn.mpmc_queue_1__code.
Require Import zoo_saturn.mpmc_queue_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type front node back new_back : location.
Implicit Type hist past nodes : list location.
Implicit Type v : val.
Implicit Type vs : list val.
Implicit Type waiter : gname.
Implicit Type waiters : gmap gname nat.

Class MpmcQueue1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpmc_queue_1۰G۰history۰G :: MonoListG Σ location
  ; #[local] mpmc_queue_1۰G۰front۰G :: AuthNatMaxG Σ
  ; #[local] mpmc_queue_1۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  ; #[local] mpmc_queue_1۰G۰waiters۰G :: ghost_mapG Σ gname nat
  ; #[local] mpmc_queue_1۰G۰saved_pred۰G :: SavedPredG Σ bool
  }.

Definition mpmc_queue_1۰Σ :=
  #[mono_list۰Σ location
  ; auth_nat_max۰Σ
  ; twins۰Σ (leibnizO (list val))
  ; ghost_mapΣ gname nat
  ; saved_pred۰Σ bool
  ].
#[global] Instance subGｰmpmc_queue_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpmc_queue_1۰Σ Σ →
  MpmcQueue1G Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section mpmc_queue_1۰G.
    Context `{mpmc_queue_1۰G : MpmcQueue1G Σ}.

    Implicit Type t : location.

    Record mpmc_queue_1۰name :=
      { mpmc_queue_1۰name۰inv : namespace
      ; mpmc_queue_1۰name۰history : gname
      ; mpmc_queue_1۰name۰front : gname
      ; mpmc_queue_1۰name۰model : gname
      ; mpmc_queue_1۰name۰waiters : gname
      }.
    Implicit Type γ : mpmc_queue_1۰name.

    #[global] Instance mpmc_queue_1۰nameｰeq_dec : EqDecision mpmc_queue_1۰name :=
      ltac:(solve_decision).
    #[global] Instance mpmc_queue_1۰nameｰcountable :
      Countable mpmc_queue_1۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition history۰auth' γ_history hist :=
      mono_list۰auth γ_history (DfracOwn 1) hist.
    #[local] Definition history۰auth γ hist :=
      history۰auth' γ.(mpmc_queue_1۰name۰history) hist.
    #[local] Definition history۰at γ i node :=
      mono_list۰at γ.(mpmc_queue_1۰name۰history) i node.

    #[local] Definition front۰auth' γ_front i :=
      auth_nat_max۰auth γ_front (DfracOwn 1) i.
    #[local] Definition front۰auth γ i :=
      front۰auth' γ.(mpmc_queue_1۰name۰front) i.
    #[local] Definition front۰lb γ i :=
      auth_nat_max۰lb γ.(mpmc_queue_1۰name۰front) i.

    #[local] Definition model₁' γ_model vs :=
      twins۰twin₁ γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ vs :=
      model₁' γ.(mpmc_queue_1۰name۰model) vs.
    #[local] Definition model₂' γ_model vs :=
      twins۰twin₂ γ_model vs.
    #[local] Definition model₂ γ vs :=
      model₂' γ.(mpmc_queue_1۰name۰model) vs.

    #[local] Definition waiters۰auth' γ_waiters waiters :=
      ghost_map_auth γ_waiters 1 waiters.
    #[local] Definition waiters۰auth γ waiters :=
      waiters۰auth' γ.(mpmc_queue_1۰name۰waiters) waiters.
    #[local] Definition waiters۰at γ waiter i :=
      ghost_map_elem γ.(mpmc_queue_1۰name۰waiters) waiter (DfracOwn 1) i.

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
      }> @ ⊤ ∖ ↑γ.(mpmc_queue_1۰name۰inv), ∅ <{
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
      ∃ hist past front nodes back vs waiters,
      ⌜hist = past ++ front :: nodes⌝ ∗
      ⌜back ∈ hist⌝ ∗
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
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
        & %back{}
        & %vs{}
        & %waiters{}
        & >%Hhist{}
        & >%Hback{}
        & >Ht_front
        & >Ht_back
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
      inv γ.(mpmc_queue_1۰name۰inv) (inv۰inner t γ).
    Definition mpmc_queue_1۰inv t γ ι : iProp Σ :=
      ⌜ι = γ.(mpmc_queue_1۰name۰inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & #Hinv
        )
      ".

    Definition mpmc_queue_1۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[global] Instance mpmc_queue_1۰modelｰtimeless γ vs :
      Timeless (mpmc_queue_1۰model γ vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpmc_queue_1۰invｰpersistent t γ ι :
      Persistent (mpmc_queue_1۰inv t γ ι).
    Proof.
      apply _.
    Qed.

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
      { rewrite lookup_snoc_Some. naive_solver. }
      iSteps.
    Qed.

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

    Lemma mpmc_queue_1۰modelｰexclusive γ vs1 vs2 :
      mpmc_queue_1۰model γ vs1 -∗
      mpmc_queue_1۰model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma mpmc_queue_1٠createｰspec ι :
      {{{
        True
      }}}
        mpmc_queue_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mpmc_queue_1۰inv t γ ι ∗
        mpmc_queue_1۰model γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰block front as "#Hfront_header" "_" "(Hfront_next & _)".
      wp۰block t as "Hmeta" "(Ht_front & Ht_back & _)".

      iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
      iMod frontｰalloc as "(%γ_front & Hfront_auth)".
      iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ :=
        {|mpmc_queue_1۰name۰inv := ι
        ; mpmc_queue_1۰name۰history := γ_history
        ; mpmc_queue_1۰name۰front := γ_front
        ; mpmc_queue_1۰name۰model := γ_model
        ; mpmc_queue_1۰name۰waiters := γ_waiters
        |}.

      iApply ("HΦ" $! t γ).
      iFrameStep.
      iApply inv_alloc.
      iExists [front], [], front, [], front, [], ∅. iFrameSteps.
      - rewrite list_elem_of_singleton //.
      - rewrite xtchainｰsingleton big_sepM_empty. iSteps.
    Qed.

    #[local] Lemma frontｰspec_strong Ψ t γ :
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
      iDestruct (history۰atｰget _ front with "Hhistory_auth") as "#Hhistory_at_front"; first done.
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
      wp۰apply (frontｰspec_strong None with "[$Hinv]").
      iSteps.
    Qed.

    #[local] Lemma backｰspec t γ :
      {{{
        inv' t γ
      }}}
        (#t).{back}
      {{{
        back i
      , RET #back;
        node۰model γ back i false
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
      }> @ ⊤ ∖ ↑γ.(mpmc_queue_1۰name۰inv), ∅ <{
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
    #[local] Lemma nextｰspec {t γ i} node :
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

    Lemma mpmc_queue_1٠is_emptyｰspec t γ ι :
      <<<
        mpmc_queue_1۰inv t γ ι
      | ∀∀ vs,
        mpmc_queue_1۰model γ vs
      >>>
        mpmc_queue_1٠is_empty #t @ ↑ι
      <<<
        mpmc_queue_1۰model γ vs
      | RET #(bool_decide (vs = []%list));
        £ 1
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "(H£1 & H£2)"; first done.
      iDestruct (atomic_updateｰframeｰl with "[H£1 $HΦ]") as "HΦ"; first iAccu.

      wp۰apply+ (frontｰspec_strong (Some $ λ b, Φ #b) with "[$Hinv HΦ]")
      as (node i) "((:node۰model =node front=) & %waiter & #Hwaiter & Hwaiters_at)".
      { rewrite /= /waiter۰au. iAuIntro.
        iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; iSteps.
      }
      wp۰match.
      wp۰apply+ (nextｰspecｰis_empty with "[$]"); iSteps.
    Qed.
    Lemma mpmc_queue_1٠is_emptyｰspec' t γ ι :
      {{{
        mpmc_queue_1۰inv t γ ι
      }}}
        mpmc_queue_1٠is_empty #t
      {{{
        b
      , RET #b;
        True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec.
      wp۰apply (frontｰspec with "Hinv") as (front i) "(:node۰model =front front=)".
      wp۰match.
      wp۰apply (nextｰspec with "[$]") as (res) "[-> | (%node & -> & _)]"; iSteps.
    Qed.

    #[local] Lemma mpmc_queue_1٠push₁ｰspec t γ i node new_back v :
      <<<
        inv' t γ ∗
        node۰model γ node i false ∗
        new_back ↦ₕ Header §Node 2 ∗
        new_back.[next] ↦ §Null ∗
        new_back.[data] ↦ v
      | ∀∀ vs,
        mpmc_queue_1۰model γ vs
      >>>
        mpmc_queue_1٠push₁ #node #new_back @ ↑γ.(mpmc_queue_1۰name۰inv)
      <<<
        mpmc_queue_1۰model γ (vs ++ [v])
      | RET ();
        ∃ j,
        history۰at γ j new_back
      >>>.
    Proof.
      iIntros "%Φ (#Hinv & (:node۰model =node) & #Hnew_back_header & Hnew_back_next & Hnew_back_data) HΦ".

      iLöb as "HLöb" forall (i node) "Hnode_header Hhistory_at_node".

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
        iSplitR "Hnew_back_next Hnew_back_data HΦ". { iFrameSteps. }
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

    #[local] Lemma mpmc_queue_1٠fix_backｰspec t γ i back j new_back :
      {{{
        inv' t γ ∗
        history۰at γ i back ∗
        node۰model γ new_back j false
      }}}
        mpmc_queue_1٠fix_back #t #back #new_back
      {{{
        RET ();
        True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hhistory_at_back & (:node۰model =new_back)) HΦ".

      iLöb as "HLöb" forall (i back) "Hhistory_at_back".

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
      wp۰apply+ domain٠yieldｰspec.
      wp۰apply+ (backｰspec with "Hinv") as (back' i') "(:node۰model =back')".
      iApply ("HLöb" with "HΦ Hhistory_at_back'").
    Qed.

    Lemma mpmc_queue_1٠pushｰspec t γ ι v :
      <<<
        mpmc_queue_1۰inv t γ ι
      | ∀∀ vs,
        mpmc_queue_1۰model γ vs
      >>>
        mpmc_queue_1٠push #t v @ ↑ι
      <<<
        mpmc_queue_1۰model γ (vs ++ [v])
      | RET ();
        £ 1
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec credit:"H£".
      iDestruct (atomic_updateｰframeｰl with "[H£ $HΦ]") as "HΦ"; first iAccu.
      wp۰block new_back as "#Hnew_back_header" "_" "(Hnew_back_next & Hnew_back_data & _)".
      wp۰match.
      wp۰apply+ (backｰspec with "Hinv") as (back i) "(:node۰model =back)".
      wp۰apply+ (mpmc_queue_1٠push₁ｰspec with "[$]").
      iApply (atomic_updateｰwand with "HΦ"). iIntros "%vs HΦ (%j & #Hhistory_at_new_back)".
      wp۰apply+ (mpmc_queue_1٠fix_backｰspec with "[]"); first iSteps.
      iSteps.
    Qed.

    Lemma mpmc_queue_1٠popｰspec t γ ι :
      <<<
        mpmc_queue_1۰inv t γ ι
      | ∀∀ vs,
        mpmc_queue_1۰model γ vs
      >>>
        mpmc_queue_1٠pop #t @ ↑ι
      <<<
        mpmc_queue_1۰model γ (tail vs)
      | RET head vs;
        £ 1
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp۰rec credit:"H£".
      wp۰apply+ (frontｰspec with "Hinv") as (front i) "(:node۰model =front front=)".
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
      { rewrite /past. simp_length. lia. }
      iDestruct (big_sepMｰimplｰthreadｰfupd _ (waiter۰model γ past)%I with "Hwaiters Hmodel₂ [#]") as ">(Hwaiters & Hmodel₂)".
      { iIntros "!> %waiter %j %Hlookup (%P & #Hwaiter & HP) Hmodel₂".
        destruct (Nat.lt_trichotomy j (length past1)) as [Hj | [-> | Hj]].
        - rewrite decide_True //.
          rewrite /waiter۰model. setoid_rewrite decide_True; last first.
          { rewrite /past. simp_length. lia. }
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /waiter۰model. setoid_rewrite decide_True; last first.
          { rewrite /past. simp_length/=. lia. }
          iMod "HP" as "(%vs & Hmodel₁ & _ & HP)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /waiter۰model. setoid_rewrite decide_False; last first.
          { rewrite /past. simp_length/=. lia. }
          iSteps.
      }

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Hfront_data H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
  End mpmc_queue_1۰G.

  #[global] Opaque mpmc_queue_1۰inv.
  #[global] Opaque mpmc_queue_1۰model.
End base.

Require zoo_saturn.mpmc_queue_1__opaque.

Section mpmc_queue_1۰G.
  Context `{mpmc_queue_1۰G : MpmcQueue1G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.

  Definition mpmc_queue_1۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpmc_queue_1۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mpmc_queue_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpmc_queue_1۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  #[global] Instance mpmc_queue_1۰modelｰtimeless t vs :
    Timeless (mpmc_queue_1۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_queue_1۰invｰpersistent t ι :
    Persistent (mpmc_queue_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma mpmc_queue_1۰modelｰexclusive t vs1 vs2 :
    mpmc_queue_1۰model t vs1 -∗
    mpmc_queue_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpmc_queue_1۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma mpmc_queue_1٠createｰspec ι :
    {{{
      True
    }}}
      mpmc_queue_1٠create ()
    {{{
      t
    , RET t;
      mpmc_queue_1۰inv t ι ∗
      mpmc_queue_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.mpmc_queue_1٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (metaｰset γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma mpmc_queue_1٠is_emptyｰspec t ι :
    <<<
      mpmc_queue_1۰inv t ι
    | ∀∀ vs,
      mpmc_queue_1۰model t vs
    >>>
      mpmc_queue_1٠is_empty t @ ↑ι
    <<<
      mpmc_queue_1۰model t vs
    | RET #(bool_decide (vs = []%list));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.mpmc_queue_1٠is_emptyｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
  Lemma mpmc_queue_1٠is_emptyｰspec' t ι :
    {{{
      mpmc_queue_1۰inv t ι
    }}}
      mpmc_queue_1٠is_empty t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.mpmc_queue_1٠is_emptyｰspec' with "[$] HΦ").
  Qed.

  Lemma mpmc_queue_1٠pushｰspec t ι v :
    <<<
      mpmc_queue_1۰inv t ι
    | ∀∀ vs,
      mpmc_queue_1۰model t vs
    >>>
      mpmc_queue_1٠push t v @ ↑ι
    <<<
      mpmc_queue_1۰model t (vs ++ [v])
    | RET ();
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.mpmc_queue_1٠pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma mpmc_queue_1٠popｰspec t ι :
    <<<
      mpmc_queue_1۰inv t ι
    | ∀∀ vs,
      mpmc_queue_1۰model t vs
    >>>
      mpmc_queue_1٠pop t @ ↑ι
    <<<
      mpmc_queue_1۰model t (tail vs)
    | RET head vs;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.mpmc_queue_1٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"); first done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End mpmc_queue_1۰G.

#[global] Opaque mpmc_queue_1۰inv.
#[global] Opaque mpmc_queue_1۰model.

Section mpmc_queue_1۰G.
  Context `{mpmc_queue_1۰G : MpmcQueue1G Σ}.
  Context τ `{!iType (iProp Σ) τ}.

  #[local] Definition itype۰inner t : iProp Σ :=
    ∃ vs,
    mpmc_queue_1۰model t vs ∗
    [∗ list] v ∈ vs, τ v.
  #[local] Instance : CustomIpat "itype۰inner" :=
    " ( %vs
      & >Hmodel
      & #Hvs
      )
    ".
  Definition itype۰mpmc_queue_1 t : iProp Σ :=
    mpmc_queue_1۰inv t (nroot.@"1") ∗
    inv (nroot.@"2") (itype۰inner t).
  #[local] Instance : CustomIpat "itype" :=
    " ( #Hinv1
      & #Hinv2
      )
    ".

  #[global] Instance itype۰mpmc_queue_1ｰitype :
    iType _ itype۰mpmc_queue_1.
  Proof.
    split. apply _.
  Qed.

  Lemma mpmc_queue_1٠createｰtype :
    {{{
      True
    }}}
      mpmc_queue_1٠create ()
    {{{
      t
    , RET t;
      itype۰mpmc_queue_1 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (mpmc_queue_1٠createｰspec with "[//]") as (t) "(#Hinv & Hmodel)".
    rewrite /itype۰mpmc_queue_1 /itype۰inner. iSteps.
  Qed.

  Lemma mpmc_queue_1٠is_emptyｰtype t :
    {{{
      itype۰mpmc_queue_1 t
    }}}
      mpmc_queue_1٠is_empty t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:itype) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_queue_1٠is_emptyｰspec with "Hinv1").
    iInv "Hinv2" as "(:itype۰inner)".
    iAaccIntro with "Hmodel"; first iSteps. iSteps as "_ H£".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_queue_1٠pushｰtype t v :
    {{{
      itype۰mpmc_queue_1 t ∗
      τ v
    }}}
      mpmc_queue_1٠push t v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((:itype) & #Hv) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_queue_1٠pushｰspec with "Hinv1").
    iInv "Hinv2" as "(:itype۰inner)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "$ !>".
    iSplitR.
    { iModIntro.
      iApply (big_sepLｰsnoc₂ with "Hvs Hv").
    }
    iIntros "H£".
    iMod (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_queue_1٠popｰtype t :
    {{{
      itype۰mpmc_queue_1 t
    }}}
      mpmc_queue_1٠pop t
    {{{
      o
    , RET o;
      itype۰option τ o
    }}}.
  Proof.
    iIntros "%Φ (:itype) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_queue_1٠popｰspec with "Hinv1").
    iInv "Hinv2" as "(:itype۰inner)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "$ !>".
    iSplitR.
    { iModIntro.
      destruct vs as [| v vs]; first iSteps.
      iDestruct (big_sepLｰcons₁ with "Hvs") as "(_ & $)".
    }
    iIntros "H£".
    iDestruct "Hvs" as "-#Hvs".
    iMod (lc_fupd_elim_later with "H£ [-]") as "H"; first (iModIntro; iAccu). iDestruct "H" as "(Hvs & HΦ)".
    destruct vs; iSteps.
  Qed.
End mpmc_queue_1۰G.

#[global] Opaque itype۰mpmc_queue_1.
