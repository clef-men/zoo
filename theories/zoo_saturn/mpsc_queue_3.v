Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.clist.
Require Export zoo_saturn.mpsc_queue_3__code.
Require Import zoo_saturn.mpsc_queue_3__types.
Require Import zoo.options.

Implicit Type b closed : bool.
Implicit Type l : location.
Implicit Type v t : val.
Implicit Type vs front back : list val.
Implicit Type ws : option (list val).

Class MpscQueue3G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpsc_queue_3۰G۰twins۰G :: TwinsG Σ (leibnizO (list val))
  ; #[local] mpsc_queue_3۰G۰lstate۰G :: OneshotG Σ () ()
  }.

Definition mpsc_queue_3۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ; oneshot۰Σ () ()
  ].
#[global] Instance subGｰmpsc_queue_3۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpsc_queue_3۰Σ Σ →
  MpscQueue3G Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_3۰G.
  Context `{mpsc_queue_3۰G : MpscQueue3G Σ}.

  Record metadata :=
    { metadata۰model : gname
    ; metadata۰front : gname
    ; metadata۰lstate : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata۰model) vs.

  #[local] Definition front₁' γ_front front :=
    twins۰twin₁ γ_front (DfracOwn 1) front.
  #[local] Definition front₁ γ front :=
    front₁' γ.(metadata۰front) front.
  #[local] Definition front₂' γ_model front :=
    twins۰twin₂ γ_model front.
  #[local] Definition front₂ γ front :=
    front₂' γ.(metadata۰front) front.

  #[local] Definition lstate۰open₁' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (1/2)) ().
  #[local] Definition lstate۰open₁ γ :=
    lstate۰open₁' γ.(metadata۰lstate).
  #[local] Definition lstate۰open₂' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (1/2)) ().
  #[local] Definition lstate۰open₂ γ :=
    lstate۰open₂' γ.(metadata۰lstate).
  #[local] Definition lstate۰closed γ :=
    oneshot۰shot γ.(metadata۰lstate) ().

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ front v_back,
    front₂ γ front ∗
    l.[back] ↦ v_back ∗
    ( ( lstate۰open₂ γ ∗
          ∃ back,
          ⌜v_back = list۰to_clist_open back⌝ ∗
          model₂ γ (front ++ reverse back)
      ) ∨ (
        lstate۰closed γ ∗
        ⌜v_back = §ClistClosed%V⌝
      )
    ).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %front{}
      & %v_back
      & >Hfront₂
      & >Hl_back
      & [(>Hopen₂ & %back{} & >-> & >Hmodel₂{_{suff}}) | (>Hclosed{_{suff}} & >->)]
      )
    ".
  Definition mpsc_queue_3۰inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    inv ι (inv۰inner l γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & #Hmeta
      & #Hinv
      )
    ".

  Definition mpsc_queue_3۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  Definition mpsc_queue_3۰consumer t ws : iProp Σ :=
    ∃ l γ v_front front,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[front] ↦ v_front ∗
    front₁ γ front ∗
    match ws with
    | None =>
        ⌜v_front = list۰to_clist_open front⌝ ∗
        lstate۰open₁ γ
    | Some ws =>
        ⌜ws = front⌝ ∗
        ⌜v_front = list۰to_clist_closed front⌝ ∗
        lstate۰closed γ ∗
        model₂ γ front
    end.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l_
      & %γ_
      & %v_front
      & %front
      & %Heq
      & Hmeta_
      & Hl_front
      & Hfront₁
      & {{open}(-> & Hopen₁);{closed}(-> & -> & Hclosed & Hmodel₂);Hlstate}
      )
    ".

  Definition mpsc_queue_3۰closed t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    lstate۰closed γ.
  #[local] Instance : CustomIpat "closed" :=
    " ( %l_
      & %γ_
      & %Heq
      & Hmeta_
      & Hclosed
      )
    ".

  #[global] Instance mpsc_queue_3۰modelｰtimeless t vs :
    Timeless (mpsc_queue_3۰model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_3۰consumerｰtimeless t ws :
    Timeless (mpsc_queue_3۰consumer t ws ).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_queue_3۰invｰpersistent t ι :
    Persistent (mpsc_queue_3۰inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_3۰closedｰpersistent t :
    Persistent (mpsc_queue_3۰closed t).
  Proof.
    apply _.
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

  #[local] Lemma frontｰalloc :
    ⊢ |==>
      ∃ γ_front,
      front₁' γ_front [] ∗
      front₂' γ_front [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma frontｰagree γ front1 front2 :
    front₁ γ front1 -∗
    front₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma frontｰupdate {γ front1 front2} front :
    front₁ γ front1 -∗
    front₂ γ front2 ==∗
      front₁ γ front ∗
      front₂ γ front.
  Proof.
    apply twinsｰupdate.
  Qed.

  #[local] Lemma lstateｰalloc :
    ⊢ |==>
      ∃ γ_lstate,
      lstate۰open₁' γ_lstate ∗
      lstate۰open₂' γ_lstate.
  Proof.
    iMod oneshotｰalloc as "(%γ_lstate & (Hopen₁ & Hopen₂))".
    iSteps.
  Qed.
  #[local] Lemma lstateｰopen₁ｰclosed γ :
    lstate۰open₁ γ -∗
    lstate۰closed γ -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma lstateｰopen₂ｰclosed γ :
    lstate۰open₂ γ -∗
    lstate۰closed γ -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma lstateｰupdate γ :
    lstate۰open₁ γ -∗
    lstate۰open₂ γ ==∗
    lstate۰closed γ.
  Proof.
    iIntros "Hopen₁ Hopen₂".
    iCombine "Hopen₁ Hopen₂" as "Hopen".
    iApply (oneshotｰupdateｰshot with "Hopen").
  Qed.

  Lemma mpsc_queue_3۰modelｰexclusive t vs1 vs2 :
    mpsc_queue_3۰model t vs1 -∗
    mpsc_queue_3۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpsc_queue_3۰consumerｰexclusive t ws1 ws2 :
    mpsc_queue_3۰consumer t ws1 -∗
    mpsc_queue_3۰consumer t ws2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma mpsc_queue_3ｰconsumerｰclosed t vs :
    mpsc_queue_3۰consumer t (Some vs) ⊢
    mpsc_queue_3۰closed t.
  Proof.
    iSteps.
  Qed.

  Lemma mpsc_queue_3٠createｰspec ι :
    {{{
      True
    }}}
      mpsc_queue_3٠create ()
    {{{
      t
    , RET t;
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰model t [] ∗
      mpsc_queue_3۰consumer t None
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰block l as "Hmeta" "(Hfront & Hback & _)".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod frontｰalloc as "(%γ_front & Hfront₁ & Hfront₂)".
    iMod lstateｰalloc as "(%γ_lstate & Hopen₁ & Hopen₂)".

    pose γ :=
      {|metadata۰model := γ_model
      ; metadata۰front := γ_front
      ; metadata۰lstate := γ_lstate
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hfront Hfront₁ Hopen₁"; last iSteps.
    iSteps. iExists []. iSteps.
  Qed.

  Lemma mpsc_queue_3٠is_emptyｰspecｰopen t ι :
    <<<
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t None
    | ∀∀ vs,
      mpsc_queue_3۰model t vs
    >>>
      mpsc_queue_3٠is_empty t @ ↑ι
    <<<
      mpsc_queue_3۰model t vs
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_3۰consumer t None
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer open=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    destruct front as [| v front]; wp۰pures.

    - wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner)"; last first.
      { iDestruct (lstateｰopen₁ｰclosed with "Hopen₁ Hclosed") as %[]. }
      wp۰load.
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      destruct back as [| v back].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ Hopen₁ HΦ".
        { iSteps. iExists []. iSteps. }
        iSteps.

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ Hopen₁ HΦ".
        { iSteps. iExists (v :: back). iSteps. }
        rewrite reverse_cons bool_decide_eq_false_2 /=; first intros (_ & [=])%app_nil.
        iSteps.

    - iInv "Hinv" as "(:inv۰inner =1)"; last first.
      { iDestruct (lstateｰopen₁ｰclosed with "Hopen₁ Hclosed") as %[]. }
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
  Lemma mpsc_queue_3٠is_emptyｰspecｰclosed t ι vs :
    {{{
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t (Some vs)
    }}}
      mpsc_queue_3٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      mpsc_queue_3۰consumer t (Some vs)
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer closed=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    destruct front as [| v front]; iSteps.
  Qed.

  Lemma mpsc_queue_3٠push_frontｰspecｰopen t ι v :
    <<<
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t None
    | ∀∀ vs,
      mpsc_queue_3۰model t vs
    >>>
      mpsc_queue_3٠push_front t v @ ↑ι
    <<<
      mpsc_queue_3۰model t (v :: vs)
    | RET false;
      mpsc_queue_3۰consumer t None
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer open=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    iApply wpｰmatchｰclistｰopen. wp۰store. wp۰pures.

    iInv "Hinv" as "(:inv۰inner =1)"; last first.
    { iDestruct (lstateｰopen₁ｰclosed with "Hopen₁ Hclosed") as %[]. }
    iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
    set front' := v :: front.
    iMod (frontｰupdate front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    set vs' := front' ++ reverse back1.
    iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSteps.
  Qed.
  Lemma mpsc_queue_3٠push_frontｰspecｰclosed t ι vs v :
    <<<
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t (Some vs)
    | ∀∀ vs',
      mpsc_queue_3۰model t vs'
    >>>
      mpsc_queue_3٠push_front t v @ ↑ι
    <<<
      ∃∃ b,
      ⌜b = bool_decide (vs = [])⌝ ∗
      ⌜vs' = vs⌝ ∗
      mpsc_queue_3۰model t (if b then [] else v :: vs)
    | RET #b;
      mpsc_queue_3۰consumer t (Some $ if b then [] else v :: vs)
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer closed=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    destruct front as [| v' front]; wp۰pures.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.

    - wp۰store. wp۰pures.

      iInv "Hinv" as "(:inv۰inner =1 suff=)".
      { iDestruct (lstateｰopen₂ｰclosed with "Hopen₂ Hclosed") as %[]. }
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      set front' := v :: v' :: front.
      iMod (frontｰupdate front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate front' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpsc_queue_3٠push_backｰspecｰopen closed t ι v :
    <<<
      mpsc_queue_3۰inv t ι
    | ∀∀ vs,
      mpsc_queue_3۰model t vs
    >>>
      mpsc_queue_3٠push_back t v @ ↑ι
    <<<
      ∃∃ closed,
      if closed then
        mpsc_queue_3۰model t vs
      else
        mpsc_queue_3۰model t (vs ++ [v])
    | RET #closed;
      if closed then
        mpsc_queue_3۰closed t
      else
        True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner =1)".

    - wp۰load.
      iSplitR "HΦ". { iFrameSteps. }
      iModIntro. clear.

      iApply wpｰmatchｰclistｰopen. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".

      + wp۰cas as _ | ->%(inj _)%(inj _); first iSteps.
        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        set back := v :: back1.
        set vs' := front2 ++ reverse back.
        iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! false with "[Hmodel₁]") as "HΦ".
        { iSteps. rewrite -assoc /vs' reverse_cons //. }
        iSplitR "HΦ". { iSteps. iExists back. iSteps. }
        iSteps.

      + wp۰cas as _ | []%(inj clist۰to_val ClistClosed)%list۰to_clist_openｰnotｰclosed'.
        iSteps.

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! true with "Hmodel") as "HΦ".
      iSteps.
  Qed.
  Lemma mpsc_queue_3٠push_backｰspecｰclosed closed t ι v :
    {{{
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰closed t
    }}}
      mpsc_queue_3٠push_back t v
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:closed)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner suff=)".
    { iDestruct (lstateｰopen₂ｰclosed with "Hopen₂ Hclosed") as %[]. }
    iSteps.
  Qed.

  Lemma mpsc_queue_3٠popｰspecｰopen t ι :
    <<<
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t None
    | ∀∀ vs,
      mpsc_queue_3۰model t vs
    >>>
      mpsc_queue_3٠pop t @ ↑ι
    <<<
      mpsc_queue_3۰model t (tail vs)
    | RET head vs;
      mpsc_queue_3۰consumer t None
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer open=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    destruct front as [| v front]; wp۰pures.

    - wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
      iInv "Hinv" as "(:inv۰inner)"; last first.
      { iDestruct (lstateｰopen₁ｰclosed with "Hopen₁ Hclosed") as %[]. }
      wp۰xchg.
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      destruct back as [| v back _] using rev_ind.

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ Hopen₂ HΦ".
        { iSteps. iExists []. iSteps. }
        iSteps.

      + set front := reverse back.
        iMod (frontｰupdate front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
        iMod (modelｰupdate front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        rewrite reverse_snoc /=.
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ Hopen₂ HΦ".
        { iSteps. iExists []. iSteps. rewrite right_id //. }
        iModIntro. clear.

        remember (back ++ [v]) as back' eqn:Hback.
        destruct back' as [| v' back']; first by eelim app_cons_not_nil.
        wp۰apply+ (clist٠rev_appｰspec (v' :: back') ClistOpen with "[//]") as "_"; [done.. |].
        rewrite clist۰appｰClistOpen {}Hback reverse_snoc.
        iSteps.

    - wp۰store. wp۰pures.

      iInv "Hinv" as "(:inv۰inner =1)"; last first.
      { iDestruct (lstateｰopen₁ｰclosed with "Hopen₁ Hclosed") as %[]. }
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod (frontｰupdate front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      set vs := front ++ reverse back1.
      iMod (modelｰupdate vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
  Lemma mpsc_queue_3٠popｰspecｰclosed t ι vs :
    <<<
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t (Some vs)
    | ∀∀ vs',
      mpsc_queue_3۰model t vs'
    >>>
      mpsc_queue_3٠pop t @ ↑ι
    <<<
      ⌜vs' = vs⌝ ∗
      mpsc_queue_3۰model t (tail vs)
    | RET head vs;
      mpsc_queue_3۰consumer t (Some $ tail vs)
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer closed=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    destruct front as [| v front]; wp۰pures.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.

    - wp۰store. wp۰pures.

      iInv "Hinv" as "(:inv۰inner =1 suff=)".
      { iDestruct (lstateｰopen₂ｰclosed with "Hopen₂ Hclosed") as %[]. }
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod (frontｰupdate front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpsc_queue_3٠closeｰspecｰopen t ι :
    <<<
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t None
    | ∀∀ vs,
      mpsc_queue_3۰model t vs
    >>>
      mpsc_queue_3٠close t @ ↑ι
    <<<
      mpsc_queue_3۰model t vs
    | RET false;
      mpsc_queue_3۰consumer t (Some vs)
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer open=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰pures.

    wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1)"; last first.
    { iDestruct (lstateｰopen₁ｰclosed with "Hopen₁ Hclosed") as %[]. }
    wp۰xchg.
    iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
    set front' := front ++ reverse back1.
    iMod (frontｰupdate front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
    iMod (lstateｰupdate with "Hopen₁ Hopen₂") as "#Hclosed".
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "Hl_front Hfront₁ Hmodel₂ HΦ". { iFrameSteps. }
    iModIntro. clear.

    iApply wpｰmatchｰclistｰopen. simpl.
    wp۰apply (clist٠rev_appｰspec _ ClistClosed with "[//]") as "_"; [done.. |].
    wp۰load.
    wp۰apply (clist٠appｰspec with "[//]") as "_"; [done.. |].
    wp۰store.

    iSteps. rewrite clist۰appｰClistClosed. erewrite clist۰appｰclosed => //.
  Qed.
  Lemma mpsc_queue_3٠closeｰspecｰclosed t ι vs :
    {{{
      mpsc_queue_3۰inv t ι ∗
      mpsc_queue_3۰consumer t (Some vs)
    }}}
      mpsc_queue_3٠close t
    {{{
      RET true;
      mpsc_queue_3۰consumer t (Some vs)
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer closed=)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰pures.

    wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1 suff=)".
    { iDestruct (lstateｰopen₂ｰclosed with "Hopen₂ Hclosed") as %[]. }
    iSteps.
  Qed.
End mpsc_queue_3۰G.

Require zoo_saturn.mpsc_queue_3__opaque.

#[global] Opaque mpsc_queue_3۰inv.
#[global] Opaque mpsc_queue_3۰model.
#[global] Opaque mpsc_queue_3۰consumer.
#[global] Opaque mpsc_queue_3۰closed.
