Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.list.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.glist.
Require Export zoo_saturn.mpsc_queue_2__code.
Require Import zoo_saturn.mpsc_queue_2__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v t : val.
Implicit Type vs front back : list val.
Implicit Type o : option val.

Class MpscQueue2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpsc_queue_2۰G۰twins۰G :: TwinsG Σ (leibnizO (list val))
  }.

Definition mpsc_queue_2۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ].
#[global] Instance subGｰmpsc_queue_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpsc_queue_2۰Σ Σ →
  MpscQueue2G Σ.
Proof.
  solve_inG.
Qed.

Section mpsc_queue_2۰G.
  Context `{mpsc_queue_2۰G : MpscQueue2G Σ}.

  Record metadata :=
    { metadata۰model : gname
    ; metadata۰front : gname
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

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ front back,
    front₂ γ front ∗
    l.[back] ↦ glist۰to_val back ∗
    model₂ γ (front ++ reverse back).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %front{}
      & %back{}
      & >Hfront₂
      & >Hl_back
      & >Hmodel₂
      )
    ".
  Definition mpsc_queue_2۰inv t ι : iProp Σ :=
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

  Definition mpsc_queue_2۰model t vs : iProp Σ :=
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

  Definition mpsc_queue_2۰consumer t : iProp Σ :=
    ∃ l γ front,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[front] ↦ glist۰to_val front ∗
    front₁ γ front.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l_
      & %γ_
      & %front
      & %Heq
      & Hmeta_
      & Hl_front
      & Hfront₁
      )
    ".

  #[global] Instance mpsc_queue_2۰modelｰtimeless t vs :
    Timeless (mpsc_queue_2۰model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_queue_2۰consumerｰtimeless t :
    Timeless (mpsc_queue_2۰consumer t ).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_queue_2۰invｰpersistent t ι :
    Persistent (mpsc_queue_2۰inv t ι).
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

  Lemma mpsc_queue_2۰modelｰexclusive t vs1 vs2 :
    mpsc_queue_2۰model t vs1 -∗
    mpsc_queue_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpsc_queue_2۰consumerｰexclusive t :
    mpsc_queue_2۰consumer t -∗
    mpsc_queue_2۰consumer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma mpsc_queue_2٠createｰspec ι :
    {{{
      True
    }}}
      mpsc_queue_2٠create ()
    {{{
      t
    , RET t;
      mpsc_queue_2۰inv t ι ∗
      mpsc_queue_2۰model t [] ∗
      mpsc_queue_2۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.

    wp۰block l as "Hmeta" "(Hfront & Hback & _)".

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod frontｰalloc as "(%γ_front & Hfront₁ & Hfront₂)".

    pose γ :=
      {|metadata۰model := γ_model
      ; metadata۰front := γ_front
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hfront Hfront₁".
    - iExists l, γ. iStep 2. iApply inv_alloc. iExists [], []. iSteps.
    - iSplitL "Hmodel₁"; first iSteps. iExists l, γ, []. iSteps.
  Qed.

  Lemma mpsc_queue_2٠is_emptyｰspec t ι :
    <<<
      mpsc_queue_2۰inv t ι ∗
      mpsc_queue_2۰consumer t
    | ∀∀ vs,
      mpsc_queue_2۰model t vs
    >>>
      mpsc_queue_2٠is_empty t @ ↑ι
    <<<
      mpsc_queue_2۰model t vs
    | RET #(bool_decide (vs = []%list));
      mpsc_queue_2۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    destruct front as [| v front]; wp۰pures.

    - wp۰bind (_.{back})%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      destruct back as [| v back].

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ HΦ". { iFrameSteps. }
        iSteps. iExists []. iSteps.

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ HΦ". { iFrameSteps. }
        rewrite reverse_cons bool_decide_eq_false_2 /=; first intros (_ & [=])%app_nil.
        iSteps. iExists []. iSteps.

    - iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps. iExists (v :: front). iSteps.
  Qed.

  Lemma mpsc_queue_2٠push_frontｰspec t ι v :
    <<<
      mpsc_queue_2۰inv t ι ∗
      mpsc_queue_2۰consumer t
    | ∀∀ vs,
      mpsc_queue_2۰model t vs
    >>>
      mpsc_queue_2٠push_front t v @ ↑ι
    <<<
      mpsc_queue_2۰model t (v :: vs)
    | RET ();
      mpsc_queue_2۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load. wp۰store.

    iInv "Hinv" as "(:inv۰inner =1)".
    iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
    set front' := v :: front.
    iMod (frontｰupdate front' with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    set vs' := front' ++ reverse back1.
    iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSteps. iExists (v :: front). iSteps.
  Qed.

  Lemma mpsc_queue_2٠push_backｰspec t ι v :
    <<<
      mpsc_queue_2۰inv t ι
    | ∀∀ vs,
      mpsc_queue_2۰model t vs
    >>>
      mpsc_queue_2٠push_back t v @ ↑ι
    <<<
      mpsc_queue_2۰model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (_.{back})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro. clear.

    wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %Hvs.
    iMod (modelｰupdate (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ".
    { iExists _, (v :: back1). iSteps.
      rewrite Hvs reverse_cons assoc //.
    }
    iSteps.
  Qed.

  Lemma mpsc_queue_2٠popｰspec t ι :
    <<<
      mpsc_queue_2۰inv t ι ∗
      mpsc_queue_2۰consumer t
    | ∀∀ vs,
      mpsc_queue_2۰model t vs
    >>>
      mpsc_queue_2٠pop t @ ↑ι
    <<<
      mpsc_queue_2۰model t (tail vs)
    | RET head vs;
      mpsc_queue_2۰consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    destruct front as [| v front]; wp۰pures.

    - wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰xchg.
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      destruct back as [| v back _] using rev_ind.

      + iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
        iSplitR "Hl_front Hfront₁ HΦ". { iFrameSteps. }
        iModIntro. clear.

        wp۰apply (glist٠revｰspec with "[//]") as "_"; first done.
        wp۰pures.

        iApply "HΦ".
        iExists l, γ, []. iSteps.

      + set front := reverse back.
        iMod (frontｰupdate front with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
        iMod (modelｰupdate front with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁]") as "HΦ".
        { rewrite reverse_snoc. iSteps. }
        iSplitR "Hl_front Hfront₁ HΦ".
        { iExists front, []. iSteps. rewrite right_id //. }
        iModIntro. clear.

        wp۰apply (glist٠revｰspec with "[//]") as "_"; first done.
        rewrite reverse_snoc. iSteps.

    - wp۰store.

      iApply fupdｰwp.
      iInv "Hinv" as "(:inv۰inner =1)".
      iDestruct (frontｰagree with "Hfront₁ Hfront₂") as %<-.
      iMod (frontｰupdate with "Hfront₁ Hfront₂") as "(Hfront₁ & Hfront₂)".
      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %Hvs.
      set vs' := front ++ reverse back1.
      iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      rewrite Hvs.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSteps.
  Qed.
End mpsc_queue_2۰G.

Require zoo_saturn.mpsc_queue_2__opaque.

#[global] Opaque mpsc_queue_2۰inv.
#[global] Opaque mpsc_queue_2۰model.
#[global] Opaque mpsc_queue_2۰consumer.
