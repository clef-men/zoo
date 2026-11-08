Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo.program_logic.prophet_bool.
Require Import zoo_std.option.
Require Import zoo_std.xtchain.
Require Export zoo_saturn.queue_mpmc_4__code.
Require Import zoo_saturn.queue_mpmc_4__types.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types front node back new_back : location.
Implicit Types v backoff : val.
Implicit Types vs ws : list val.
Implicit Types vss : list $ list val.

#[local] Definition prophet_null :=
  {|prophet_typed₁۰type :=
      bool
  ; prophet_typed₁۰of_val w _ :=
      Some $ Some $ bool_decide (w = §Null%V)
  |}.

Zoo name :=
  { self : location
  ; inv : namespace
  ; history : gname
  ; front : gname
  ; model : gname
  }.

Record descriptor :=
  { descriptor۰node : location
  ; descriptor۰queue : tqueue_mpmc_2۰name
  }.
Implicit Types descr descr_front descr_back : descriptor.
Implicit Types hist past descrs : list descriptor.

#[local] Please derive Inhabited for descriptor.

Zoo global :=
  { tqueue : tqueue_mpmc_2
  ; history : mono_list descriptor
  ; front : auth_nat_max
  ; model : twins (leibnizO (list val))
  }.

Section queue_mpmc_4۰G.
  Context `{queue_mpmc_4۰G : QueueMpmc4G Σ}.

  #[local] Definition history۰auth' γ_history hist :=
    mono_list۰auth γ_history (DfracOwn 1) hist.
  #[local] Definition history۰auth γ hist :=
    history۰auth' γ.(queue_mpmc_4۰name۰history) hist.
  #[local] Definition history۰at γ i descr :=
    mono_list۰at γ.(queue_mpmc_4۰name۰history) i descr.

  #[local] Definition front۰auth' γ_front i :=
    auth_nat_max۰auth γ_front (DfracOwn 1) i.
  #[local] Definition front۰auth γ i :=
    front۰auth' γ.(queue_mpmc_4۰name۰front) i.
  #[local] Definition front۰lb γ i :=
    auth_nat_max۰lb γ.(queue_mpmc_4۰name۰front) i.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(queue_mpmc_4۰name۰model) vs.
  #[local] Instance : CustomIpat "model₁" :=
    " Htwin₁
    ".
  #[local] Definition model₂' γ_model vss : iProp Σ :=
    ∃ vs,
    ⌜vs = concat vss⌝ ∗
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vss :=
    model₂' γ.(queue_mpmc_4۰name۰model) vss.
  #[local] Instance : CustomIpat "model₂" :=
    " ( %
      & ->
      & Htwin₂
      )
    ".

  #[local] Definition descriptor۰model₁ γ descr : iProp Σ :=
    descr.(descriptor۰node).[queue] ↦□ descr.(descriptor۰queue) ∗
    tqueue_mpmc_2۰inv descr.(descriptor۰queue) (γ.(queue_mpmc_4۰name۰inv).@"queue").
  #[local] Instance : CustomIpat "descriptor۰model_1" :=
    " ( #H{;descr}_node_queue
      & #H{;descr}_queue_inv
      )
    ".
  #[local] Definition descriptor۰model₂ γ descr i b : iProp Σ :=
    descriptor۰model₁ γ descr ∗
    descr.(descriptor۰node) ↦ₕ Header §Node 2 ∗
    history۰at γ i descr ∗
    if b then front۰lb γ i else True%I.
  #[local] Instance : CustomIpat "descriptor۰model_2" :=
    " ( (:descriptor۰model₁)
      & #H{;descr}_node_header
      & #Hhistory_at_{}
      & { {front} #Hfront_lb_{}
        ; {front} #Hfront_lb_descr
        ; _
        }
      )
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ hist past descr_front descrs descr_back vss,
    ⌜hist = past ++ descr_front :: descrs⌝ ∗
    ⌜descr_back ∈ hist⌝ ∗
    γ.(queue_mpmc_4۰name۰self).[front] ↦ #descr_front.(descriptor۰node) ∗
    γ.(queue_mpmc_4۰name۰self).[back] ↦ #descr_back.(descriptor۰node) ∗
    xtchain (Header §Node 2) (DfracOwn 1) (descriptor۰node <$> hist) §Null ∗
    ( [∗ list] descr ∈ hist,
      descriptor۰model₁ γ descr
    ) ∗
    ( [∗ list] descr ∈ removelast hist,
      tqueue_mpmc_2۰full descr.(descriptor۰queue)
    ) ∗
    ( [∗ list] descr ∈ past,
      tqueue_mpmc_2۰model descr.(descriptor۰queue) []
    ) ∗
    ( [∗ list] descr; vs ∈ descr_front :: descrs; vss,
      tqueue_mpmc_2۰model descr.(descriptor۰queue) vs
    ) ∗
    history۰auth γ hist ∗
    front۰auth γ (length past) ∗
    model₂ γ vss.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %hist{}
      & %past{}
      & %descr_front{_{}}
      & %descrs{}
      & %descr_back{_{}}
      & %vss{}
      & >%Hhist{}
      & >%Hdescr_back{_{}}
      & >Ht_front
      & >Ht_back
      & >Hhist_chain
      & Hhist_model
      & >Hhist_full
      & >Hpast_model
      & >Hdescrs
      & >Hhistory_auth
      & >Hfront_auth
      & >Hmodel₂
      )
    ".
  #[local] Definition inv' γ :=
    inv (γ.(queue_mpmc_4۰name۰inv).@"inv") (inv۰inner γ).
  Please Definition queue_mpmc_4۰inv γ ι : iProp Σ :=
    ⌜ι = γ.(queue_mpmc_4۰name۰inv)⌝ ∗
    inv' γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( ->
      & #Hinv
      )
    ".

  Please Definition queue_mpmc_4۰model :=
    model₁.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  #[local] Zoo derive Timeless for model₂.
  Zoo derive Timeless for queue_mpmc_4۰model.

  Zoo derive Persistent for queue_mpmc_4۰inv.

  #[local] Lemma historyｰalloc descr_front :
    ⊢ |==>
      ∃ γ_history,
      history۰auth' γ_history [descr_front].
  Proof.
    apply mono_listｰalloc.
  Qed.
  #[local] Lemma history۰atｰget {γ hist} i descr :
    hist !! i = Some descr →
    history۰auth γ hist ⊢
    history۰at γ i descr.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  #[local] Lemma history۰atｰlookup γ hist i descr :
    history۰auth γ hist -∗
    history۰at γ i descr -∗
    ⌜hist !! i = Some descr⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  #[local] Lemma historyｰupdate {γ hist} descr :
    history۰auth γ hist ⊢ |==>
      history۰auth γ (hist ++ [descr]) ∗
      history۰at γ (length hist) descr.
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

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    iMod twinsｰalloc' as "(%γ_model & $ & $)".
    iSteps.
  Qed.
  #[local] Lemma model₁_exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs vss :
    model₁ γ vs -∗
    model₂ γ vss -∗
    ⌜vs = concat vss⌝.
  Proof.
    iIntros "(:model₁) (:model₂)".
    iApply (twinsｰagreeｰL with "Htwin₁ Htwin₂").
  Qed.
  #[local] Lemma modelｰupdate {γ vs vss} vss' :
    model₁ γ vs -∗
    model₂ γ vss ==∗
      model₁ γ (concat vss') ∗
      model₂ γ vss'.
  Proof.
    iIntros "(:model₁) (:model₂)".
    iMod (twinsｰupdate with "Htwin₁ Htwin₂") as "($ & $)".
    iSteps.
  Qed.
  #[local] Lemma model₂ｰequiv {γ} vss1 vss2 :
    concat vss1 = concat vss2 →
    model₂ γ vss1 ⊢
    model₂ γ vss2.
  Proof.
    iIntros "%Heq (:model₂)".
    iExists _. iFrame "Htwin₂". iPureIntro. congruence.
  Qed.
  Opaque model₂'.

  Lemma queue_mpmc_4۰model_exclusive γ vs1 vs2 :
    queue_mpmc_4۰model γ vs1 -∗
    queue_mpmc_4۰model γ vs2 -∗
    False.
  Proof.
    apply model₁_exclusive.
  Qed.

  Lemma queue_mpmc_4٠createｰspec ι :
    {{{
      True
    }}}
      queue_mpmc_4٠create ()
    {{{
      γ
    , RET γ;
      queue_mpmc_4۰inv γ ι ∗
      queue_mpmc_4۰model γ []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply (tqueue_mpmc_2٠createｰspec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)". 1: done.
    wp۰block front as "Hfront_next #Hfront_queue" header:"#Hfront_header".
    wp۰block t as "Ht_front Ht_back".

    iMod historyｰalloc as "(%γ_history & Hhistory_auth)".
    iMod frontｰalloc as "(%γ_front & Hfront_auth)".
    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|queue_mpmc_4۰name۰self := t
      ; queue_mpmc_4۰name۰inv := ι
      ; queue_mpmc_4۰name۰history := γ_history
      ; queue_mpmc_4۰name۰front := γ_front
      ; queue_mpmc_4۰name۰model := γ_model
      |}.

    pose descr :=
      {|descriptor۰node := front
      ; descriptor۰queue := queue
      |}.

    iApply ("HΦ" $! γ).
    iFrameStep.
    iApply inv_alloc.
    iExists [descr], [], descr, [], descr, [[]]. iFrameSteps.
    - rewrite list_elem_of_singleton //.
    - rewrite xtchainｰsingleton. iSteps.
  Qed.

  #[local] Lemma inv۰fullｰlookup hist i descr :
    hist !! i = Some descr →
    is_Some (hist !! S i) →
    ( [∗ list] descr ∈ removelast hist,
      tqueue_mpmc_2۰full descr.(descriptor۰queue)
    ) ⊢
    tqueue_mpmc_2۰full descr.(descriptor۰queue).
  Proof.
    iIntros "%Hlookup %Hlookup' H".
    iApply (big_sepL_lookup with "H").
    rewrite lookupｰremovelast //.
    apply lookup_lt_is_Some in Hlookup'. done.
  Qed.

  #[local] Lemma inv۰modelｰlookup {past descr_front descrs vss} i descr :
    (past ++ descr_front :: descrs) !! i = Some descr →
    ( [∗ list] descr ∈ past,
      tqueue_mpmc_2۰model descr.(descriptor۰queue) []
    ) -∗
    ( [∗ list] descr; vs ∈ descr_front :: descrs; vss,
      tqueue_mpmc_2۰model descr.(descriptor۰queue) vs
    ) -∗
      ∃ vs,
      tqueue_mpmc_2۰model descr.(descriptor۰queue) vs ∗
      ⌜ i < length past ∧ vs = []
      ∨ length past ≤ i ∧ vss !! (i - length past) = Some vs
      ⌝ ∗
      ( ( tqueue_mpmc_2۰model descr.(descriptor۰queue) vs -∗
          ( [∗ list] descr ∈ past,
            tqueue_mpmc_2۰model descr.(descriptor۰queue) []
          ) ∗
          ( [∗ list] descr; vs ∈ descr_front :: descrs; vss,
            tqueue_mpmc_2۰model descr.(descriptor۰queue) vs
          )
        ) ∧ (
          ⌜length past ≤ i⌝ -∗
          ∀ vs',
          tqueue_mpmc_2۰model descr.(descriptor۰queue) vs' -∗
            ( [∗ list] descr ∈ past,
              tqueue_mpmc_2۰model descr.(descriptor۰queue) []
            ) ∗
            ( [∗ list] descr; vs ∈ descr_front :: descrs; <[i - length past := vs']> vss,
              tqueue_mpmc_2۰model descr.(descriptor۰queue) vs
            )
        )
      ).
  Proof.
    iIntros ([Hlookup | (Hi & Hlookup)]%lookup_app_Some) "Hpast Hdescrs".
    - iDestruct (big_sepL_lookup_acc with "Hpast") as "(Hmodel & Hpast)"; first done.
      apply lookup_lt_Some in Hlookup.
      iExists []. iFrame "Hmodel". iSplitR; first iSteps.
      iSplit.
      + iIntros "Hmodel". iFrame.
        iApply ("Hpast" with "Hmodel").
      + iIntros "%". lia.
    - iDestruct (big_sepL2ｰinsertｰaccｰl with "Hdescrs") as "(%vs & %Hvss_lookup & Hmodel & Hdescrs)"; first done.
      iExists vs. iFrame "Hmodel". iSplitR; first iSteps.
      iSplit.
      + iIntros "Hmodel". iFrame.
        iDestruct ("Hdescrs" $! descr vs with "Hmodel") as "Hdescrs".
        rewrite !list_insert_id //.
      + iIntros "_ %vs' Hmodel". iFrame.
        iDestruct ("Hdescrs" $! descr vs' with "Hmodel") as "Hdescrs".
        rewrite list_insert_id //.
  Qed.

  #[local] Lemma inv۰lastｰfront {past descr_front descrs vss} i vs :
    length (past ++ descr_front :: descrs) = S i →
    i ≤ length past →
    length (descr_front :: descrs) = length vss →
    ( i < length past ∧ vs = []
    ∨ length past ≤ i ∧ vss !! (i - length past) = Some vs
    ) →
    concat vss = vs.
  Proof.
    rewrite length_app /=.
    intros Hlength Hi Hvss [(? & _) | (_ & Hlookup)]; first lia.
    assert (i = length past) as -> by lia.
    rewrite Nat.sub_diag in Hlookup.
    destruct vss as [| vs' [| vs'' vss]]; simpl in *; try lia.
    injection Hlookup as ->. rewrite app_nil_r //.
  Qed.

  #[local] Lemma frontｰspec γ :
    {{{
      inv' γ
    }}}
      (#γ.(queue_mpmc_4۰name۰self)).{front}
    {{{
      descr i
    , RET #descr.(descriptor۰node);
      descriptor۰model₂ γ descr i true
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.

    assert (hist !! (length past) = Some descr_front) as Hlookup.
    { rewrite Hhist list_lookup_middle //. }

    iDestruct (xtchainｰlookupｰheader (length past) with "Hhist_chain") as "#Hdescr_front_header".
    { rewrite list_lookup_fmap Hlookup //. }

    iDestruct (big_sepL_lookup with "Hhist_model") as "#Hdescr_front_model". 1: done.

    iDestruct (history۰atｰget _ descr_front with "Hhistory_auth") as "#Hhistory_at_descr_front". 1: done.
    iDestruct (front۰lbｰget with "Hfront_auth") as "#Hfront_lb_front".

    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!>".

    iApply ("HΦ" with "[$]").
  Qed.

  #[local] Lemma backｰspec γ :
    {{{
      inv' γ
    }}}
      (#γ.(queue_mpmc_4۰name۰self)).{back}
    {{{
      descr i
    , RET #descr.(descriptor۰node);
      descriptor۰model₂ γ descr i false
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.

    pose proof Hdescr_back as (i & Hlookup)%list_elem_of_lookup.
    iDestruct (xtchainｰlookupｰheader i with "Hhist_chain") as "#Hdescr_back_header".
    { rewrite list_lookup_fmap Hlookup //. }
    iDestruct (big_sepL_lookup with "Hhist_model") as "#Hdescr_back_model"; first done.
    iDestruct (history۰atｰget with "Hhistory_auth") as "#Hhistory_at_descr_back"; first done.

    iSplitR "HΦ". { iFrameSteps. }
    iIntros "!>".

    iApply ("HΦ" $! descr_back i with "[$]").
  Qed.

  #[local] Lemma nextｰspec {γ i descr} odescr :
    {{{
      inv' γ ∗
      history۰at γ i descr ∗
      if odescr is Some descr' then
        history۰at γ (S i) descr'
      else
        True
    }}}
      (#descr.(descriptor۰node)).{next}
    {{{
      res
    , RET res;
        ⌜res = §Null%V⌝ ∗
        ⌜odescr = None⌝
      ∨ ∃ descr',
        ⌜res = #descr'.(descriptor۰node)⌝ ∗
        descriptor۰model₂ γ descr' (S i) false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hhistory_at & Hodescr) HΦ".

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at") as %Hlookup.
    iDestruct (xtchainｰlookupｰacc i with "Hhist_chain") as "(_ & Hnode & Hhist_chain)".
    { rewrite list_lookup_fmap Hlookup //. }
    wp۰load.
    iDestruct ("Hhist_chain" with "Hnode") as "Hhist_chain".
    rewrite list_lookup_fmap.
    destruct (hist !! S i) as [descr' |] eqn:Hlookup'; simpl.

    - iDestruct (xtchainｰlookupｰheader (S i) with "Hhist_chain") as "#Hdescr'_header".
      { rewrite list_lookup_fmap Hlookup' //. }
      iDestruct (big_sepL_lookup with "Hhist_model") as "#(Hdescr'_queue & Hdescr'_queue_inv)"; first done.
      iDestruct (history۰atｰget (S i) with "Hhistory_auth") as "#Hhistory_at_descr'"; first done.
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!>".
      iApply "HΦ". iRight. iExists descr'. iFrameSteps.

    - destruct odescr as [descr' |].
      { iDestruct (history۰atｰlookup with "Hhistory_auth Hodescr") as %?. congruence. }
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!>".
      iApply "HΦ". iLeft. iSteps.
  Qed.

  #[local] Definition pop۰au γ (Ψ : option val → iProp Σ) : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(queue_mpmc_4۰name۰inv), ∅ <{
      model₁ γ (tail vs)
    , COMM
      Ψ (head vs)
    }>.

  #[local] Lemma nextｰspecｰpop {γ i descr} Ψ :
    {{{
      inv' γ ∗
      history۰at γ i descr ∗
      front۰lb γ i ∗
      descriptor۰model₁ γ descr ∗
      tqueue_mpmc_2۰finished descr.(descriptor۰queue) ∗
      pop۰au γ Ψ
    }}}
      (#descr.(descriptor۰node)).{next}
    {{{
      res
    , RET res;
        ⌜res = §Null%V⌝ ∗
        Ψ None
      ∨ ∃ descr',
        ⌜res = #descr'.(descriptor۰node)⌝ ∗
        descriptor۰model₂ γ descr' (S i) false ∗
        pop۰au γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hhistory_at & #Hfront_lb & (#Hdescr_queue & #Hdescr_queue_inv) & #Hfinished & HΨ) HΦ".

    iInv "Hinv" as "(:inv۰inner)".
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at") as %Hlookup.
    iDestruct (xtchainｰlookupｰacc i with "Hhist_chain") as "(_ & Hnode & Hhist_chain)".
    { rewrite list_lookup_fmap Hlookup //. }
    wp۰load.
    iDestruct ("Hhist_chain" with "Hnode") as "Hhist_chain".
    rewrite list_lookup_fmap.
    destruct (hist !! S i) as [descr' |] eqn:Hlookup'; simpl.

    - iDestruct (xtchainｰlookupｰheader (S i) with "Hhist_chain") as "#Hdescr'_header".
      { rewrite list_lookup_fmap Hlookup' //. }
      iDestruct (big_sepL_lookup with "Hhist_model") as "#(Hdescr'_queue & Hdescr'_queue_inv)"; first done.
      iDestruct (history۰atｰget (S i) with "Hhistory_auth") as "#Hhistory_at_descr'"; first done.
      iSplitR "HΨ HΦ". { iFrameSteps. }
      iIntros "!>".
      iApply "HΦ". iRight. iExists descr'. iFrameSteps.

    - iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb") as %Hi.
      opose proof* lengthｰlookupｰlast as Hlength; [done.. |].
      iDestruct (big_sepL2_length with "Hdescrs") as %Hvss_length.
      iDestruct (inv۰modelｰlookup with "Hpast_model Hdescrs") as "(%vs_descr & Hdescr_model & %Hvs_descr & (Hdescrs & _))".
      { rewrite -Hhist //. }
      iMod (tqueue_mpmc_2ｰmodelｰfinished with "Hdescr_queue_inv Hdescr_model Hfinished") as "(-> & Hdescr_model)"; first solve_ndisj.
      iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
      rewrite Hhist in Hlength.
      opose proof* inv۰lastｰfront as Hvs; [done.. |].

      iMod "HΨ" as "(%vs & Hmodel₁ & _ & HΨ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iRevert "Hmodel₁ HΨ". rewrite Hvs. iIntros "Hmodel₁ HΨ".
      iMod ("HΨ" with "Hmodel₁") as "HΨ".

      iSplitR "HΨ HΦ". { iFrameSteps. }
      iIntros "!>".
      iApply "HΦ". iLeft. iSteps.
  Qed.

  #[local] Lemma queue_mpmc_4٠fix_back₁ｰspec γ back descr j backoff :
    {{{
      inv' γ ∗
      descriptor۰model₂ γ descr j false ∗
      backoff۰model backoff
    }}}
      queue_mpmc_4٠fix_back₁ γ #back #descr.(descriptor۰node) backoff
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & ((#Hdescr_queue & #Hdescr_queue_inv) & #Hdescr_header & #Hhistory_at_descr & _) & Hbackoff) HΦ".

    iLöb as "HLöb" forall (back backoff).

    wp۰rec. wp۰match.

    wp۰bind (_ 𝗮𝗻𝗱 _)%E.
    wp۰apply (wpｰwand itype۰bool) as (res) "(%b & ->)".
    { wp۰apply+ (nextｰspec None with "[$]") as (res) "[(-> & _) | (%descr' & -> & _)]"; last iSteps.
      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰cas as _ | _; first iSteps.
      iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup%list_elem_of_lookup_2.
      iSteps.
    }

    destruct b; last iSteps.
    wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as "{% backoff} %backoff Hbackoff".
    wp۰apply+ (backｰspec with "Hinv") as (descr_back i) "_".
    iApply ("HLöb" with "Hbackoff HΦ").
  Qed.
  #[local] Lemma queue_mpmc_4٠fix_backｰspec γ back descr j :
    {{{
      inv' γ ∗
      descriptor۰model₂ γ descr j false
    }}}
      queue_mpmc_4٠fix_back γ #back #descr.(descriptor۰node)
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (Hinv & Hdescr) HΦ".

    wp۰rec.
    wp۰apply+ (queue_mpmc_4٠fix_back₁ｰspec with "[- HΦ] HΦ"). 1: iFrameSteps.
  Qed.

  Lemma queue_mpmc_4٠is_emptyｰspec γ ι :
    <<<
      queue_mpmc_4۰inv γ ι
    | ∀∀ vs,
      queue_mpmc_4۰model γ vs
    >>>
      queue_mpmc_4٠is_empty γ
      @ ↑ι
    <<<
      ∃∃ b,
      ⌜if b then vs = [] else True⌝ ∗
      queue_mpmc_4۰model γ vs
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply+ (frontｰspec with "Hinv") as (descr i) "((#Hdescr_queue & #Hdescr_queue_inv) & #Hdescr_header & #Hhistory_at_descr & #Hfront_lb_descr)".
    wp۰match.
    wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_bool₁ with "[//]") as (pid proph) "Hproph".
    wp۰pures. wp۰load.

    awp۰apply (tqueue_mpmc_2٠is_emptyｰspec with "Hdescr_queue_inv").
    iInv "Hinv" as "(:inv۰inner =1)".
    iApply (aaccｰaupdｰcommit with "HΦ"); first solve_ndisj.
    iIntros "%vs (:model)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup1.
    iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_descr") as %Hi.
    iDestruct (big_sepL2_length with "Hdescrs") as %Hvss1_length.
    iDestruct (inv۰modelｰlookup with "Hpast_model Hdescrs") as "(%vs_descr & Hdescr_model & %Hvs_descr & (Hdescrs & _))".
    { rewrite -Hhist1 //. }
    iAaccIntro with "Hdescr_model".
    { iIntros "Hdescr_model".
      iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
      iFrameSteps.
    }
    iIntros "%b (%Hb & Hdescr_model)".
    iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
    destruct (hist1 !! S i) as [descr' |] eqn:Hlookup1'.

    - iDestruct (history۰atｰget (S i) with "Hhistory_auth") as "#Hhistory_at_descr'"; first done.
      iExists false. iFrame "Hmodel₁".
      iIntros "!> HΦ !>".
      iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "_ {%}".

      destruct b; wp۰pures; last iSteps.
      wp۰apply+ (nextｰspec (Some descr') with "[$Hinv $Hhistory_at_descr $Hhistory_at_descr']") as (res) "[(_ & %) | (%descr'' & -> & _)]"; first done.
      wp۰pures.
      wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
      wp۰pures.
      iSteps.

    - opose proof* lengthｰlookupｰlast as Hlength; [done.. |].
      rewrite Hhist1 in Hlength.
      opose proof* inv۰lastｰfront as Hvs; [done.. |].
      iExists (b && proph). iFrame "Hmodel₁". iSplitR.
      { iModIntro. iPureIntro.
        destruct b, proph; try done.
        simpl in Hb. congruence.
      }
      iIntros "!> HΦ !>".
      iSplitR "Hproph HΦ". { iFrameSteps. }
      iIntros "_ {%}".

      destruct b; wp۰pures; last iSteps.
      wp۰apply+ (nextｰspec None with "[$Hinv $Hhistory_at_descr]") as (res) "[(-> & _) | (%descr' & -> & _)]".
      all: wp۰pures.
      all: wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
      all: wp۰pures.
      all: iSteps.
  Qed.

  #[local] Lemma queue_mpmc_4٠push₁ｰspec γ descr i v backoff :
    <<<
      inv' γ ∗
      descriptor۰model₂ γ descr i false ∗
      backoff۰model backoff
    | ∀∀ vs,
      queue_mpmc_4۰model γ vs
    >>>
      queue_mpmc_4٠push₁ γ #descr.(descriptor۰node) v backoff
      @ ↑γ.(queue_mpmc_4۰name۰inv)
    <<<
      queue_mpmc_4۰model γ (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & ((#Hdescr_queue & #Hdescr_queue_inv) & #Hdescr_header & #Hhistory_at_descr & _) & Hbackoff) HΦ".

    iLöb as "HLöb" forall (descr i backoff) "Hdescr_queue Hdescr_queue_inv Hdescr_header Hhistory_at_descr".

    wp۰rec. wp۰match.
    wp۰apply+ (nextｰspec None with "[$]") as (res) "[(-> & _) | (%descr' & -> & ((#Hdescr'_queue & #Hdescr'_queue_inv) & #Hdescr'_header & #Hhistory_at_descr' & _))]"; first last.
    { wp۰match.
      iApply ("HLöb" with "Hbackoff HΦ Hdescr'_queue Hdescr'_queue_inv Hdescr'_header Hhistory_at_descr'").
    }
    wp۰load.

    wp۰apply (tqueue_mpmc_2٠pushｰspec _ _ _ (⊤ ∖ ↑γ.(queue_mpmc_4۰name۰inv).@"queue" ∖ ↑γ.(queue_mpmc_4۰name۰inv).@"inv") with "Hdescr_queue_inv").
    iMod (inv_acc with "Hinv") as "((:inv۰inner =1) & Hclose)"; first solve_ndisj.
    iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup1.
    iDestruct (big_sepL2_length with "Hdescrs") as %Hvss1_length.
    iDestruct (inv۰modelｰlookup with "Hpast_model Hdescrs") as "(%vs_descr & Hdescr_model & %Hvs_descr & Hdescrs)".
    { rewrite -Hhist1 //. }
    iModIntro. iExists vs_descr. iFrame "Hdescr_model". iIntros ([]).

    - iIntros "(Hdescr_model & Hnonfull)".
      destruct (hist1 !! S i) as [descr' |] eqn:Hlookup1'.
      { iDestruct (inv۰fullｰlookup hist1 i descr with "Hhist_full") as "Hfull"; [done | eauto |].
        iDestruct (tqueue_mpmc_2ｰfullｰnonfull with "Hfull Hnonfull") as %[].
      }
      opose proof* lengthｰlookupｰlast as Hlength; [done.. |].
      rewrite Hhist1 length_app /= in Hlength.
      destruct Hvs_descr as [(? & _) | (Hi & Hvss1_lookup)]; first lia.
      iDestruct "Hdescrs" as "(_ & Hdescrs)".
      iDestruct ("Hdescrs" with "[//] Hdescr_model") as "(Hpast_model & Hdescrs)".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (<[i - length past1 := vs_descr ++ [v]]> vss1) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      rewrite concatｰinsertｰsnoc //; first (simpl in Hvss1_length; lia).
      iMod ("HΦ" with "Hmodel₁") as "HΦ".

      iFrame "Hnonfull". iModIntro.
      iMod ("Hclose" with "[- HΦ]") as "_". { iFrameSteps. }
      iModIntro.

      wp۰pures.
      iApply ("HΦ" with "[//]").

    - iIntros "(Hdescr_model & #Hfull)".
      iDestruct "Hdescrs" as "(Hdescrs & _)".
      iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
      iSplitR; first done. iModIntro.
      iMod ("Hclose" with "[- Hbackoff HΦ]") as "_". { iFrameSteps. }
      iModIntro. clear.

      wp۰pures.
      wp۰apply+ (nextｰspec None with "[$]") as (res) "[(-> & _) | (%descr' & -> & ((#Hdescr'_queue & #Hdescr'_queue_inv) & #Hdescr'_header & #Hhistory_at_descr' & _))]".

      + wp۰apply+ (tqueue_mpmc_2٠makeｰspec (γ.(queue_mpmc_4۰name۰inv).@"queue") with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)"; first done.
        wp۰block new_back as "Hnew_back_next #Hnew_back_queue" header:"#Hnew_back_header".
        wp۰match. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =2)".
        iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup2.
        iDestruct (xtchainｰlookup₁ i with "Hhist_chain") as "(Hhist_chain1 & _ & Hnode & Hhist_chain2)".
        { rewrite list_lookup_fmap Hlookup2 //. }
        rewrite list_lookup_fmap.
        destruct (hist2 !! S i) as [descr' |] eqn:Hlookup2'; simpl.

        * wp۰cas as _ | [=].
          iDestruct (xtchainｰlookup₂ with "Hhist_chain1 Hdescr_header Hnode Hhist_chain2") as "Hhist_chain".
          { rewrite list_lookup_fmap Hlookup2 //. }
          { rewrite list_lookup_fmap Hlookup2' //. }
          iSplitR "Hbackoff HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          wp۰pures.
          wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as "{% backoff} %backoff Hbackoff".
          iApply ("HLöb" with "Hbackoff HΦ Hdescr_queue Hdescr_queue_inv Hdescr_header Hhistory_at_descr").

        * wp۰cas as ? | _; first done.
          iDestruct (xtchainｰlookup₂ with "Hhist_chain1 Hdescr_header Hnode []") as "Hhist_chain".
          { rewrite list_lookup_fmap Hlookup2 //. }
          { rewrite list_lookup_fmap Hlookup2' //. }
          { assert (drop (S i) (descriptor۰node <$> hist2) = []) as ->.
            { apply dropｰlookupｰNone. rewrite list_lookup_fmap Hlookup2' //. }
            iApply xtchainｰnil.
          }
          iDestruct (xtchainｰsnoc₂ with "Hhist_chain Hnew_back_header Hnew_back_next") as "Hhist_chain".
          set descr_new :=
            {|descriptor۰node := new_back
            ; descriptor۰queue := queue
            |}.
          iMod (historyｰupdate descr_new with "Hhistory_auth") as "(Hhistory_auth & #Hhistory_at_new_back)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate (vss2 ++ [[v]]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          rewrite concat_app /=.
          iMod ("HΦ" with "Hmodel₁") as "HΦ".

          opose proof* lengthｰlookupｰlast as Hlength; [done.. |].
          assert (hist2 = removelast hist2 ++ [descr]) as Hhist2'.
          { apply lastｰremovelast. rewrite last_lookup Hlength //. }
          iDestruct (big_sepL_snoc (λ _ descr, tqueue_mpmc_2۰full descr.(descriptor۰queue)) (removelast hist2) descr with "[$Hhist_full $Hfull]") as "Hhist_full".
          rewrite -Hhist2'.

          iSplitR "HΦ".
          { iExists (hist2 ++ [descr_new]), past2, descr_front_2, (descrs2 ++ [descr_new]), descr_back_2, (vss2 ++ [[v]]).
            iFrame "Ht_front Ht_back Hhistory_auth Hfront_auth Hmodel₂ Hpast_model".
            rewrite fmap_app removelast_last.
            iFrame "Hhist_chain".
            iSplitR. { rewrite Hhist2 -app_assoc //. }
            iSplitR. { iPureIntro. set_solver. }
            iSplitL "Hhist_model". { rewrite big_sepL_snoc. iFrame "#∗". iSteps. }
            iSplitL "Hhist_full". { iFrame. iSteps. }
            rewrite app_comm_cons big_sepL2_snoc. iFrame "Hdescrs".
            iExact "Hqueue_model".
          }
          iIntros "!> {%}".

          wp۰pures.
          wp۰apply (queue_mpmc_4٠fix_backｰspec _ _ descr_new with "[]"); first iSteps.
          iSteps.

      + wp۰match. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =2)".
        wp۰cas as _ | _.

        * iSplitR "Hbackoff HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          wp۰pures.
          iApply ("HLöb" with "Hbackoff HΦ Hdescr'_queue Hdescr'_queue_inv Hdescr'_header Hhistory_at_descr'").

        * iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr'") as %Hlookup2'.
          iSplitR "Hbackoff HΦ".
          { iFrameSteps. iPureIntro.
            apply list_elem_of_lookup_2 in Hlookup2'. done.
          }
          iIntros "!> {%}".

          wp۰pures.
          iApply ("HLöb" with "Hbackoff HΦ Hdescr'_queue Hdescr'_queue_inv Hdescr'_header Hhistory_at_descr'").
  Qed.
  Lemma queue_mpmc_4٠pushｰspec γ ι v :
    <<<
      queue_mpmc_4۰inv γ ι
    | ∀∀ vs,
      queue_mpmc_4۰model γ vs
    >>>
      queue_mpmc_4٠push γ v
      @ ↑ι
    <<<
      queue_mpmc_4۰model γ (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply+ (backｰspec with "Hinv") as (descr i) "Hdescr".
    wp۰apply+ (queue_mpmc_4٠push₁ｰspec with "[$Hinv $Hdescr] HΦ"). 1: iSteps.
  Qed.

  #[local] Lemma queue_mpmc_4ｰpop_auxｰpop₁ｰspec γ :
    ⊢ (
      ∀ descr i backoff,
      <<<
        inv' γ ∗
        descriptor۰model₂ γ descr i true ∗
        backoff۰model backoff
      | ∀∀ vs,
        queue_mpmc_4۰model γ vs
      >>>
        queue_mpmc_4٠pop_aux γ #descr.(descriptor۰node) backoff
        @ ↑γ.(queue_mpmc_4۰name۰inv)
      <<<
        queue_mpmc_4۰model γ (tail vs)
      | RET head vs;
        True
      >>>
    ) ∧ (
      ∀ backoff,
      <<<
        inv' γ ∗
        backoff۰model backoff
      | ∀∀ vs,
        queue_mpmc_4۰model γ vs
      >>>
        queue_mpmc_4٠pop₁ γ backoff
        @ ↑γ.(queue_mpmc_4۰name۰inv)
      <<<
        queue_mpmc_4۰model γ (tail vs)
      | RET head vs;
        True
      >>>
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHpop_aux & IHpop₁)".
    iSplit.

    - iIntros "%descr %i %backoff %Φ (#Hinv & ((#Hdescr_queue & #Hdescr_queue_inv) & #Hdescr_header & #Hhistory_at_descr & #Hfront_lb_descr) & Hbackoff) HΦ".

      wp۰rec. wp۰match. wp۰load.

      awp۰apply (tqueue_mpmc_2٠popｰspec with "Hdescr_queue_inv").
      iInv "Hinv" as "(:inv۰inner =1)".
      iApply (aaccｰaupd with "HΦ"); first solve_ndisj.
      iIntros "%vs (:model)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup1.
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_descr") as %Hi.
      iDestruct (inv۰modelｰlookup with "Hpast_model Hdescrs") as "(%vs_descr & Hdescr_model & %Hvs_descr & Hdescrs)".
      { rewrite -Hhist1 //. }
      iAaccIntro with "Hdescr_model".
      { iIntros "Hdescr_model".
        iDestruct "Hdescrs" as "(Hdescrs & _)".
        iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
        iFrameSteps.
      }
      iIntros "%o %vs_descr' (Hdescr_model & %Ho)".
      destruct o as [| | v].

      + subst vs_descr'.
        iDestruct "Hdescrs" as "(Hdescrs & _)".
        iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
        iLeft. iFrame. iIntros "!> HΦ !>".
        iSplitR "Hbackoff HΦ". { iFrameSteps. }
        iIntros "_ {%}".

        wp۰pures.
        wp۰apply+ (backoff٠onceｰspec with "Hbackoff") as "{% backoff} %backoff Hbackoff".
        wp۰apply ("IHpop₁" with "[$Hinv $Hbackoff] HΦ").

      + destruct Ho as (-> & ->).
        iDestruct "Hdescrs" as "(Hdescrs & _)".
        iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
        iLeft. iFrame. iIntros "!> HΦ !>".
        iSplitR "Hbackoff HΦ". { iFrameSteps. }
        iIntros "#Hfinished {%}".

        wp۰pures.
        wp۰apply+ (nextｰspecｰpop (λ o, True -∗ Φ o)%I with "[$Hinv $Hhistory_at_descr $Hfront_lb_descr $Hdescr_queue $Hdescr_queue_inv $Hfinished $HΦ]") as (res) "[(-> & HΦ) | (%descr' & -> & ((#Hdescr'_queue & #Hdescr'_queue_inv) & #Hdescr'_header & #Hhistory_at_descr' & _) & HΦ)]".
        { iSteps. }
        wp۰match. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =2)".
        wp۰cas as _ | [= Hcas].

        * iSplitR "Hbackoff HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          wp۰pures.
          wp۰apply ("IHpop₁" with "[$Hinv $Hbackoff] HΦ").

        * iDestruct (xtchainｰNoDup with "Hhist_chain") as %Hnodup.
          iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup2.
          iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr'") as %Hlookup2'.
          assert (length past2 = i) as <-.
          { apply (NoDup_lookup (descriptor۰node <$> hist2) _ _ descr.(descriptor۰node)); first done.
            - rewrite list_lookup_fmap Hhist2 list_lookup_middle //=. congruence.
            - rewrite list_lookup_fmap Hlookup2 //.
          }
          rewrite Hhist2 list_lookup_middle in Hlookup2; first done. injection Hlookup2 as ->.
          rewrite Hhist2 (assoc _ _ [_]) lookup_app_r length_app /= in Hlookup2'; first lia.
          rewrite Nat.add_1_r Nat.sub_diag in Hlookup2'.
          destruct descrs2 as [| descr'' descrs2]; first done. injection Hlookup2' as ->.
          iDestruct (big_sepL2_cons_inv_l with "Hdescrs") as "(%vs_front & %vss2' & -> & Hdescr_model & Hdescrs)".
          iMod (tqueue_mpmc_2ｰmodelｰfinished with "Hdescr_queue_inv Hdescr_model Hfinished") as "(-> & Hdescr_model)"; first solve_ndisj.
          iMod (frontｰupdate (length (past2 ++ [descr])) with "Hfront_auth") as "Hfront_auth".
          { rewrite length_app /=. lia. }
          iDestruct (model₂ｰequiv _ vss2' with "Hmodel₂") as "Hmodel₂"; first done.
          iDestruct (big_sepL_snoc (λ _ descr, tqueue_mpmc_2۰model descr.(descriptor۰queue) []) past2 descr with "[$Hpast_model $Hdescr_model]") as "Hpast_model".

          iSplitR "Hbackoff HΦ".
          { iExists hist2, (past2 ++ [descr]), descr', descrs2, descr_back_2, vss2'.
            iFrame. iPureIntro.
            split; last done.
            rewrite Hhist2 -assoc //.
          }
          iIntros "!> {%}".

          wp۰pures.
          wp۰apply ("IHpop₁" with "[$Hinv $Hbackoff] HΦ").

      + subst vs_descr.
        destruct Hvs_descr as [(_ & ?) | (Hi' & Hvss1_lookup)]; first done.
        assert (i = length past1) as -> by lia.
        rewrite Nat.sub_diag in Hvss1_lookup.
        iDestruct "Hdescrs" as "(_ & Hdescrs)".
        iDestruct ("Hdescrs" with "[//] Hdescr_model") as "(Hpast_model & Hdescrs)".
        destruct vss1 as [| vs_front vss1]; first done. injection Hvss1_lookup as ->.
        iDestruct (big_sepL2_cons_inv_l with "Hdescrs") as "(%vs_front' & %vss1' & %Heq & Hdescr_front_model & Hdescrs)".
        rewrite Nat.sub_diag /= in Heq. injection Heq as <- <-.
        iMod (modelｰupdate (vs_descr' :: vss1) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iRight. iFrame "Hmodel₁". iIntros "!> HΦ !>".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "_ {%}".

        wp۰pures.
        iSteps.

    - iIntros "%backoff %Φ (#Hinv & Hbackoff) HΦ".

      wp۰rec.
      wp۰apply+ (frontｰspec with "Hinv") as (descr i) "((#Hdescr_queue & #Hdescr_queue_inv) & #Hdescr_header & #Hhistory_at_descr & #Hfront_lb_descr)".
      wp۰match.
      wp۰apply+ (prophet_typed₁ｰwpｰproph prophet_null with "[//]") as (pid proph) "Hproph".
      wp۰pures. wp۰load.

      awp۰apply (tqueue_mpmc_2٠is_emptyｰspec with "Hdescr_queue_inv").
      iInv "Hinv" as "(:inv۰inner =1)".
      iApply (aaccｰaupd with "HΦ"); first solve_ndisj.
      iIntros "%vs (:model)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iDestruct (history۰atｰlookup with "Hhistory_auth Hhistory_at_descr") as %Hlookup1.
      iDestruct (front۰lbｰvalid with "Hfront_auth Hfront_lb_descr") as %Hi.
      iDestruct (big_sepL2_length with "Hdescrs") as %Hvss1_length.
      iDestruct (inv۰modelｰlookup with "Hpast_model Hdescrs") as "(%vs_descr & Hdescr_model & %Hvs_descr & (Hdescrs & _))".
      { rewrite -Hhist1 //. }
      iAaccIntro with "Hdescr_model".
      { iIntros "Hdescr_model".
        iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
        iFrameSteps.
      }
      iIntros "%b (%Hb & Hdescr_model)".
      iDestruct ("Hdescrs" with "Hdescr_model") as "(Hpast_model & Hdescrs)".
      destruct (hist1 !! S i) as [descr' |] eqn:Hlookup1'.

      + iDestruct (history۰atｰget (S i) with "Hhistory_auth") as "#Hhistory_at_descr'"; first done.
        iLeft. iFrame. iIntros "!> HΦ !>".
        iSplitR "Hproph Hbackoff HΦ". { iFrameSteps. }
        iIntros "_ {%}".

        destruct b; wp۰pures; last first.
        { wp۰apply ("IHpop_aux" with "[- HΦ] HΦ"). iFrameSteps. }
        wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
        wp۰apply (nextｰspec (Some descr') with "[$Hinv $Hhistory_at_descr $Hhistory_at_descr']") as (res) "[(_ & %) | (%descr'' & -> & (_ & #Hdescr''_header & _))]"; first done.
        iExists _. iSplitR; first done. iIntros "_".
        wp۰match.
        wp۰apply ("IHpop_aux" with "[- HΦ] HΦ"). iFrameSteps.

      + opose proof* lengthｰlookupｰlast as Hlength; [done.. |].
        rewrite Hhist1 in Hlength.
        destruct_decide (b = true ∧ proph = true) as (-> & ->) | Hcase.

        * opose proof* inv۰lastｰfront as Hvs; [done.. |].
          simpl in Hb. subst vs_descr.
          rewrite Hvs.
          iRight. iFrame "Hmodel₁". iIntros "!> HΦ !>".
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "_ {%}".

          wp۰pures.
          wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
          wp۰apply (nextｰspec None with "[$Hinv $Hhistory_at_descr]") as (res) "[(-> & _) | (%descr' & -> & _)]".
          all: iExists _; iSplitR; first done.
          { iIntros "_". iSteps. }
          iIntros "%Hproph". exfalso.
          revert Hproph. case_bool_decide; congruence.

        * iLeft. iFrame. iIntros "!> HΦ !>".
          iSplitR "Hproph Hbackoff HΦ". { iFrameSteps. }
          iIntros "_ {%- Hcase}".

          destruct b; wp۰pures; last first.
          { wp۰apply ("IHpop_aux" with "[- HΦ] HΦ"). iFrameSteps. }
          wp۰apply+ (prophet_typed₁ｰwpｰresolve with "Hproph"); [done.. |].
          wp۰apply (nextｰspec None with "[$Hinv $Hhistory_at_descr]") as (res) "[(-> & _) | (%descr' & -> & (_ & #Hdescr'_header & _))]".
          all: iExists _; iSplitR; first done.
          { iIntros "%Hproph". exfalso.
            rewrite bool_decide_eq_true_2 // in Hproph. naive.
          }
          iIntros "_".
          wp۰match.
          wp۰apply ("IHpop_aux" with "[- HΦ] HΦ"). iFrameSteps.
  Qed.
  Lemma queue_mpmc_4٠popｰspec γ ι :
    <<<
      queue_mpmc_4۰inv γ ι
    | ∀∀ vs,
      queue_mpmc_4۰model γ vs
    >>>
      queue_mpmc_4٠pop γ
      @ ↑ι
    <<<
      queue_mpmc_4۰model γ (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.
    iDestruct queue_mpmc_4ｰpop_auxｰpop₁ｰspec as "(_ & Hpop₁)".
    wp۰apply ("Hpop₁" with "[$Hinv] HΦ"). 1: iSteps.
  Qed.
End queue_mpmc_4۰G.

Require zoo_saturn.queue_mpmc_4__opaque.

Please opacify.
