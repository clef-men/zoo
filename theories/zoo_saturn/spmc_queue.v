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
#[global] Instance subG𑁒spmc_queue۰Σ Σ `{zoo۰G : !ZooG Σ} :
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

    #[global] Instance metadata𑁒eq_dec : EqDecision metadata :=
      ltac:(solve_decision).
    #[global] Instance metadata𑁒countable :
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

    #[global] Instance spmc_queue۰model𑁒timeless γ vs :
      Timeless (spmc_queue۰model γ vs).
    Proof.
      apply _.
    Qed.
    #[global] Instance spmc_queue۰producer𑁒timeless t γ ws :
      Timeless (spmc_queue۰producer t γ ws).
    Proof.
      apply _.
    Qed.

    #[global] Instance spmc_queue۰inv𑁒persistent t γ ι :
      Persistent (spmc_queue۰inv t γ ι).
    Proof.
      apply _.
    Qed.

    #[local] Lemma history𑁒alloc front :
      ⊢ |==>
        ∃ γ_history,
        history۰auth' γ_history [front] ∗
        history۰last' γ_history front.
    Proof.
      iMod mono_list𑁒alloc as "(%γ_history & $ & $)".
      iSteps.
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
    #[local] Lemma history𑁒auth𑁒last γ hist node :
      history۰auth γ hist -∗
      history۰last γ node -∗
      ⌜last hist = Some node⌝.
    Proof.
      iIntros "Hauth_1 (:history۰last =2)".
      iDestruct (mono_list۰auth𑁒agree with "Hauth_1 Hauth_2") as %<-.
      iSteps.
    Qed.
    #[local] Lemma history𑁒update {γ hist node} node' :
      history۰auth γ hist -∗
      history۰last γ node ==∗
        history۰auth γ (hist ++ [node']) ∗
        history۰last γ node'.
    Proof.
      iIntros "Hauth_1 (:history۰last =2)".
      rewrite /history۰auth /history۰auth'.
      iDestruct (mono_list۰auth𑁒combine with "Hauth_1 Hauth_2") as "(<- & Hauth)". rewrite dfrac_op_own Qp.half_half.
      iMod (mono_list𑁒update𑁒snoc with "Hauth") as "($ & $)".
      rewrite last_snoc //.
    Qed.
    Opaque history۰last'.

    #[local] Lemma front𑁒alloc :
      ⊢ |==>
        ∃ γ_front,
        front۰auth' γ_front 0.
    Proof.
      apply auth_nat_max𑁒alloc.
    Qed.
    #[local] Lemma front۰lb𑁒get γ i :
      front۰auth γ i ⊢
      front۰lb γ i.
    Proof.
      apply auth_nat_max۰lb𑁒get.
    Qed.
    #[local] Lemma front۰lb𑁒valid γ i1 i2 :
      front۰auth γ i1 -∗
      front۰lb γ i2 -∗
      ⌜i2 ≤ i1⌝.
    Proof.
      apply auth_nat_max۰lb𑁒valid.
    Qed.
    #[local] Lemma front𑁒update {γ i} i' :
      i ≤ i' →
      front۰auth γ i ⊢ |==>
      front۰auth γ i'.
    Proof.
      apply auth_nat_max𑁒update.
    Qed.

    #[local] Lemma producer𑁒valid γ ws vs :
      producer γ ws -∗
      model₁ γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      rewrite -preorder𑁒rtc.
      apply: auth_twins𑁒valid₁.
    Qed.
    #[local] Lemma producer𑁒exclusive γ ws1 ws2 :
      producer γ ws1 -∗
      producer γ ws2 -∗
      False.
    Proof.
      apply: auth_twins۰auth𑁒exclusive.
    Qed.

    #[local] Lemma model𑁒producer𑁒alloc :
      ⊢ |==>
        ∃ γ_model,
        producer' γ_model [] ∗
        model₁' γ_model [] ∗
        model₂' γ_model [].
    Proof.
      apply auth_twins𑁒alloc.
    Qed.
    #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply auth_twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma model𑁒agree γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₂ γ vs2 -∗
      ⌜vs1 = vs2⌝.
    Proof.
      apply: auth_twins𑁒agree𑁒L.
    Qed.
    #[local] Lemma model𑁒push {γ ws vs1 vs2} v :
      producer γ ws -∗
      model₁ γ vs1 -∗
      model₂ γ vs2 ==∗
        producer γ (vs1 ++ [v]) ∗
        model₁ γ (vs1 ++ [v]) ∗
        model₂ γ (vs1 ++ [v]).
    Proof.
      apply auth_twins𑁒update𑁒auth.
    Qed.
    #[local] Lemma model𑁒pop γ v vs1 vs2 :
      model₁ γ (v :: vs1) -∗
      model₂ γ vs2 ==∗
        model₁ γ vs1 ∗
        model₂ γ vs1.
    Proof.
      apply: auth_twins𑁒update𑁒twins𑁒L.
      rewrite preorder𑁒rtc. solve_suffix.
    Qed.

    #[local] Lemma waiters𑁒alloc :
      ⊢ |==>
        ∃ γ_waiters,
        waiters۰auth' γ_waiters ∅.
    Proof.
      iMod ghost_map_alloc as "(%γ_waiters & Hwaiters_auth & _)".
      iSteps.
    Qed.
    #[local] Lemma waiters𑁒insert {γ waiters} i Ψ :
      waiters۰auth γ waiters ⊢ |==>
        ∃ waiter,
        waiters۰auth γ (<[waiter := i]> waiters) ∗
        saved_pred waiter Ψ ∗
        waiters۰at γ waiter i.
    Proof.
      iIntros "Hwaiters_auth".
      iMod (saved_pred𑁒alloc𑁒cofinite (dom waiters) Ψ) as "(%waiter & %Hwaiter & $)".
      rewrite not_elem_of_dom in Hwaiter.
      iApply (ghost_map_insert with "Hwaiters_auth"); first done.
    Qed.
    #[local] Lemma waiters𑁒delete γ waiters waiter i :
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

    Lemma spmc_queue۰model𑁒exclusive γ vs1 vs2 :
      spmc_queue۰model γ vs1 -∗
      spmc_queue۰model γ vs2 -∗
      False.
    Proof.
      apply model₁𑁒exclusive.
    Qed.

    Lemma spmc_queue۰producer𑁒valid t γ vs ws :
      spmc_queue۰producer t γ ws -∗
      spmc_queue۰model γ vs -∗
      ⌜vs `suffix_of` ws⌝.
    Proof.
      iIntros "(:producer =1) (:model =2)".
      iApply (producer𑁒valid with "Hproducer_1 Hmodel₁_2").
    Qed.
    Lemma spmc_queue۰producer𑁒exclusive t γ ws1 ws2 :
      spmc_queue۰producer t γ ws1 -∗
      spmc_queue۰producer t γ ws2 -∗
      False.
    Proof.
      iIntros "(:producer =1) (:producer =2)".
      iApply (producer𑁒exclusive with "Hproducer_1 Hproducer_2").
    Qed.

    Lemma spmc_queue٠create𑁒spec ι :
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

      iMod history𑁒alloc as "(%γ_history & Hhistory_auth & Hhistory_last)".
      iMod front𑁒alloc as "(%γ_front & Hfront_auth)".
      iMod model𑁒producer𑁒alloc as "(%γ_model & Hproducer & Hmodel₁ & Hmodel₂)".
      iMod waiters𑁒alloc as "(%γ_waiters & Hwaiters_auth)".

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
      rewrite xtchain𑁒singleton big_sepM_empty. iSteps.
    Qed.

    #[local] Lemma front𑁒spec𑁒strong Ψ t γ :
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
      iDestruct (xtchain𑁒lookup𑁒header with "Hhist") as "#Hfront_header"; first done.
      iDestruct (history۰at𑁒get _ front with "Hhistory_auth") as "#Hhistory_at"; first done.
      iDestruct (front۰lb𑁒get with "Hfront_auth") as "#Hfront_lb_front".
      destruct Ψ as [Ψ |]; last iSteps.
      iMod (waiters𑁒insert (length past) Ψ with "Hwaiters_auth") as "(%waiter & Hwaiter_auth & #Hwaiter & Hwaiters_at)".
      iDestruct (big_sepM_insert_2 _ _ waiter (length past) with "[HΨ] Hwaiters") as "Hwaiters".
      { iExists Ψ. rewrite decide_False; first lia. iSteps. }
      iSplitR "Hwaiters_at HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    #[local] Lemma front𑁒spec t γ :
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

      wp۰apply (front𑁒spec𑁒strong None with "[$Hinv]").
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
    #[local] Instance operation'𑁒eq_dec : EqDecision operation' :=
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
    #[local] Lemma next𑁒spec𑁒aux op t γ i node :
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
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_node") as %Hlookup.
      iDestruct (xtchain𑁒lookup𑁒acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
      wp۰load.
      iDestruct ("Hhist" with "Hnode") as "Hhist".
      destruct (hist !! ˖i) as [node' |] eqn:Hlookup'; simpl.

      - iDestruct (xtchain𑁒lookup𑁒header with "Hhist") as "#Hnode'_header"; first done.
        iDestruct (history۰at𑁒get ˖i with "Hhistory_auth") as "#Hhistory_at_node'"; first done.
        destruct op; [| iSteps..].
        iDestruct "Hop" as "(#Hfront_lb_node & #Hwaiter & Hwaiters_at & H£)".
        iMod (waiters𑁒delete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
        iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
        iDestruct (saved_pred𑁒agree false with "Hwaiter Hwaiter_") as "Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        destruct_decide (i = length past) as -> | Hi.

        + rewrite decide_False; first lia.

          iMod "HΨ" as "(%vs_ & Hmodel₁ & _ & HΨ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
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

        + iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb_node") as %Hi_.
          rewrite decide_True; first lia.
          iSplitR "Heq HΨ HΦ". { iFrameSteps. }
          iSteps. iRewrite "Heq". iSteps.

      - destruct_decide (op = Other' :> operation').
        { destruct op; try done. iSteps. }
        iDestruct "Hop" as "(#Hfront_lb_node & Hop)".
        iDestruct (front۰lb𑁒valid with "Hfront_auth Hfront_lb_node") as %Hi.
        opose proof* length𑁒lookup𑁒last as Hlength; [done.. |].
        rewrite Hhist length_app /= in Hlength.
        assert (i = length past) as -> by lia.
        assert (length nodes = 0) as ->%nil_length_inv by lia.
        iDestruct (big_sepL2_length with "Hnodes") as %->%symmetry%nil_length_inv.
        destruct op; last done.

        + iDestruct "Hop" as "(#Hwaiter & Hwaiters_at & H£)".
          iMod (waiters𑁒delete with "Hwaiters_auth Hwaiters_at") as "(%Hwaiters_lookup & Hwaiters_auth)".
          iDestruct (big_sepM_delete with "Hwaiters") as "((%Ψ_ & Hwaiter_ & HΨ) & Hwaiters)"; first done.
          iDestruct (saved_pred𑁒agree true with "Hwaiter Hwaiter_") as "Heq".
          iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
          rewrite decide_False; first lia.

          iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "Heq HΨ HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          iApply "HΦ".
          iLeft. iRewrite "Heq". iSteps.

        + iMod "Hop" as "(%vs & Hmodel₁ & _ & HΨ)".
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΨ" with "Hmodel₁") as "HΨ".

          iSplitR "HΨ HΦ". { iFrameSteps. }
          iSteps.
    Qed.
    #[local] Lemma next𑁒spec t γ i node :
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

      wp۰apply (next𑁒spec𑁒aux Other); iSteps.
    Qed.
    #[local] Lemma next𑁒spec𑁒is_empty {t γ i node} waiter Ψ :
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

      wp۰apply (next𑁒spec𑁒aux (IsEmpty _ _) with "[$]").
      iSteps.
    Qed.
    #[local] Lemma next𑁒spec𑁒pop {t γ i node} Ψ :
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

      wp۰apply (next𑁒spec𑁒aux (Pop _) with "[$]").
      iSteps.
    Qed.

    Lemma spmc_queue٠is_empty𑁒spec t γ ι :
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
      wp۰apply+ (front𑁒spec𑁒strong (Some $ λ b, Φ #b) with "[$Hinv HΦ]") as (node i) "((:node۰model =node front=) & %waiter & #Hwaiter & Hwaiters_at)".
      { rewrite /= /waiter۰au. iAuIntro.
        iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model)".
        iAaccIntro with "Hmodel₁"; iSteps.
      }
      wp۰match.
      wp۰apply+ (next𑁒spec𑁒is_empty with "[$]"); iSteps.
    Qed.

    Lemma spmc_queue٠push𑁒spec t γ ι ws v :
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
      iDestruct (history𑁒auth𑁒last with "Hhistory_auth Hhistory_last") as %?.
      wp۰apply (xtchain٠set_next𑁒spec𑁒last' new_back with "[$]") as "Hhist"; first done.
      iMod (history𑁒update new_back with "Hhistory_auth Hhistory_last") as "(Hhistory_auth & Hhistory_last)".
      iDestruct (big_sepL2𑁒snoc₂ with "Hnodes Hnew_back_data") as "Hnodes".

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒push v with "Hproducer Hmodel₁ Hmodel₂") as "(Hproducer & Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Ht_back Hhistory_last Hproducer HΦ".
      { iFrameSteps. list_simplifier. done. }
      iSteps.
    Qed.

    #[local] Lemma spmc_queue٠pop𑁒spec𑁒aux t γ :
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
      wp۰apply+ (front𑁒spec with "Hinv") as (front i) "(#Hfront_header & #Hhistory_at_front & #Hfront_lb_front)".
      wp۰match.
      wp۰apply+ (next𑁒spec𑁒pop (λ o, _ -∗ Φ o)%I with "[$]") as (res) "[(-> & HΦ) | (%new_front & -> & (:node۰model =new_front) & HΦ)]"; first iSteps.
      wp۰match. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_new_front") as %Hlookup.
      iDestruct (xtchain𑁒lookup𑁒acc with "Hhist") as "(_ & Hnode & Hhist)"; first done.
      wp۰cas as _ | [= <-]; first iSteps.
      iDestruct ("Hhist" with "Hnode") as "Hhist".
      iDestruct (history۰at𑁒lookup with "Hhistory_auth Hhistory_at_front") as %Hlookup_old.
      iAssert ⌜length past1 = i⌝%I as %Hpast_length.
      { iDestruct (xtchain𑁒NoDup with "Hhist") as %Hnodup.
        iPureIntro. eapply NoDup_lookup; try done.
        rewrite Hhist1 list_lookup_middle //.
      }
      rewrite Hhist1 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup; first lia.
      rewrite Nat.add_1_r Hpast_length Nat.sub_diag in Hlookup.
      destruct nodes1 as [| node nodes1]; first done. injection Hlookup as ->.
      rewrite (assoc _ _ [_]) in Hhist1.
      iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & -> & Hfront_data & Hnodes)".
      set past := past1 ++ [front].
      iMod (front𑁒update (length past) with "Hfront_auth") as "Hfront_auth".
      { rewrite /past. simpl_length. lia. }
      iDestruct (big_sepM𑁒impl𑁒thread𑁒fupd _ (waiter۰model γ past)%I with "Hwaiters Hmodel₂ [#]") as ">(Hwaiters & Hmodel₂)".
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
          iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
          iSteps.
        - rewrite decide_False; first lia.
          rewrite /waiter۰model. setoid_rewrite decide_False; last first.
          { rewrite /past. simpl_length/=. lia. }
          iSteps.
      }

      iMod "HΦ" as "(%vs & Hmodel₁ & _ & HΦ)".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒pop with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iSplitR "Hfront_data H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    Lemma spmc_queue٠pop𑁒spec t γ ι :
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

      wp۰apply (spmc_queue٠pop𑁒spec𑁒aux with "Hinv").
      iAuIntro.
      iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model)".
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

  #[global] Instance spmc_queue۰model𑁒timeless t vs :
    Timeless (spmc_queue۰model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_queue۰producer𑁒timeless t ws :
    Timeless (spmc_queue۰producer t ws).
  Proof.
    apply _.
  Qed.

  #[global] Instance spmc_queue۰inv𑁒persistent t ι :
    Persistent (spmc_queue۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma spmc_queue۰model𑁒exclusive t vs1 vs2 :
    spmc_queue۰model t vs1 -∗
    spmc_queue۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.spmc_queue۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma spmc_queue۰producer𑁒valid t vs ws :
    spmc_queue۰producer t ws -∗
    spmc_queue۰model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.spmc_queue۰producer𑁒valid with "Hproducer_1 Hmodel_2").
  Qed.
  Lemma spmc_queue۰producer𑁒exclusive t ws1 ws2 :
    spmc_queue۰producer t ws1 -∗
    spmc_queue۰producer t ws2 -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.spmc_queue۰producer𑁒exclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma spmc_queue٠create𑁒spec ι :
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

    iApply wp𑁒fupd.
    wp۰apply (base.spmc_queue٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (meta𑁒set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma spmc_queue٠is_empty𑁒spec t ι :
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

    awp۰apply (base.spmc_queue٠is_empty𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma spmc_queue٠push𑁒spec t ι ws v :
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
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    awp۰apply (base.spmc_queue٠push𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma spmc_queue٠pop𑁒spec t ι :
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

    awp۰apply (base.spmc_queue٠pop𑁒spec with "[$]").
    { iApply (aacc𑁒aupd𑁒commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End spmc_queue۰G.

#[global] Opaque spmc_queue۰inv.
#[global] Opaque spmc_queue۰producer.
#[global] Opaque spmc_queue۰model.
