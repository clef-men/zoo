Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.subpreds.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.ivar_1__code.
Require Import zoo_std.ivar_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v : val.
Implicit Type o state : option val.

Zoo name :=
  { self : location
  ; lstate : gname
  ; consumer : gname
  }.

Zoo global :=
  { state : oneshot unit val
  ; consumer : subpreds val
  }.

Section ivar_1۰G.
  Context `{ivar_1۰G : Ivar1G Σ}.

  Implicit Type Ψ Χ Ξ : val → iProp Σ.

  #[local] Definition lstate۰unset₁' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (1/3)) ().
  #[local] Definition lstate۰unset₁ γ :=
    lstate۰unset₁' γ.(ivar_1۰name۰lstate).
  #[local] Definition lstate۰unset₂' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (2/3)) ().
  #[local] Definition lstate۰unset₂ γ :=
    lstate۰unset₂' γ.(ivar_1۰name۰lstate).
  #[local] Definition lstate۰set' γ_lstate v :=
    oneshot۰shot γ_lstate v.
  #[local] Definition lstate۰set γ :=
    lstate۰set' γ.(ivar_1۰name۰lstate).

  #[local] Definition consumer۰auth' :=
    subpreds۰auth.
  #[local] Definition consumer۰auth γ :=
    consumer۰auth' γ.(ivar_1۰name۰consumer).
  #[local] Definition consumer۰frag' :=
    subpreds۰frag.
  #[local] Definition consumer۰frag γ :=
    consumer۰frag' γ.(ivar_1۰name۰consumer).

  #[local] Definition inv۰state۰unset γ :=
    lstate۰unset₁ γ.
  #[local] Instance : CustomIpat "inv۰state۰unset" :=
    " {>;}Hlstate_unset₁
    ".
  #[local] Definition inv۰state۰set γ Ξ v : iProp Σ :=
    lstate۰set γ v ∗
    □ Ξ v.
  #[local] Instance : CustomIpat "inv۰state۰set" :=
    " ( {>;}#Hlstate_set{_{}}
      & #HΞ{_{}}
      )
    ".
  #[local] Definition inv۰state γ Ξ state :=
    match state with
    | None =>
        inv۰state۰unset γ
    | Some v =>
        inv۰state۰set γ Ξ v
    end.

  #[local] Definition inv۰inner γ Ψ Ξ : iProp Σ :=
    ∃ state,
    γ.(ivar_1۰name۰self) ↦ᵣ state ∗
    consumer۰auth γ Ψ state ∗
    inv۰state γ Ξ state.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %state
      & Ht
      & Hconsumer_auth
      & Hstate
      )
    ".
  Please Definition ivar_1۰inv γ Ψ Ξ : iProp Σ :=
    inv nroot (inv۰inner γ Ψ Ξ).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Please Definition ivar_1۰producer :=
    lstate۰unset₂.
  #[local] Instance : CustomIpat "producer" :=
    " Hlstate_unset₂{_{}}
    ".

  Please Definition ivar_1۰consumer :=
    consumer۰frag.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer{}_frag
    ".

  Please Definition ivar_1۰result :=
    lstate۰set.
  #[local] Instance : CustomIpat "result" :=
    " #Hlstate_set{_{}}
    ".
  Definition ivar_1۰resolved γ : iProp Σ :=
    ∃ v,
    ivar_1۰result γ v.

  #[global] Instance ivar_1۰invｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_1۰inv γ).
  Proof.
    rewrite /ivar_1۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
    solve_contractive.
  Qed.
  #[global] Instance ivar_1۰invｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      pointwise_relation _ (≡) ==>
      (≡)
    ) (ivar_1۰inv γ).
  Proof.
    rewrite /ivar_1۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
    solve_proper.
  Qed.
  #[global] Instance ivar_1۰consumerｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_1۰consumer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_1۰consumerｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      (≡)
    ) (ivar_1۰consumer γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for ivar_1۰producer.
  Zoo derive Timeless for ivar_1۰result.

  Zoo derive Persistent for ivar_1۰inv.
  Zoo derive Persistent for ivar_1۰result.

  #[local] Lemma lstateｰalloc :
    ⊢ |==>
      ∃ γ_lstate,
      lstate۰unset₁' γ_lstate ∗
      lstate۰unset₂' γ_lstate.
  Proof.
    iMod oneshotｰalloc as "(%γ_lstate & Hpending)".
    assert (1 = 1/3 + 2/3)%Qp as -> by compute_done.
    iDestruct "Hpending" as "(Hpending₁ & Hpending₂)".
    iSteps.
  Qed.
  #[local] Lemma lstate۰unset₂ｰexclusive γ :
    lstate۰unset₂ γ -∗
    lstate۰unset₂ γ -∗
    False.
  Proof.
    iIntros "Hunset1 Hunset2".
    iDestruct (oneshot۰pendingｰvalidｰ2 with "Hunset1 Hunset2") as %(? & _). done.
  Qed.
  #[local] Lemma lstate۰setｰagree γ v1 v2 :
    lstate۰set γ v1 -∗
    lstate۰set γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply oneshot۰shotｰagree.
  Qed.
  #[local] Lemma lstateｰunset₁ｰset γ v :
    lstate۰unset₁ γ -∗
    lstate۰set γ v -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma lstateｰunset₂ｰset γ v :
    lstate۰unset₂ γ -∗
    lstate۰set γ v -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma lstateｰupdate {γ} v :
    lstate۰unset₁ γ -∗
    lstate۰unset₂ γ ==∗
    lstate۰set γ v.
  Proof.
    iIntros "Hpending₁ Hpending₂".
    iCombine "Hpending₁ Hpending₂" as "Hpending".
    assert (1/3 + 2/3 = 1)%Qp as -> by compute_done.
    iApply (oneshotｰupdateｰshot with "Hpending").
  Qed.

  #[local] Lemma consumerｰalloc Ψ :
    ⊢ |==>
      ∃ γ_consumer,
      consumer۰auth' γ_consumer Ψ None ∗
      consumer۰frag' γ_consumer Ψ.
  Proof.
    apply subpredsｰalloc.
  Qed.
  #[local] Lemma consumerｰwand {γ Ψ state Χ1} Χ2 E :
    ▷ consumer۰auth γ Ψ state -∗
    consumer۰frag γ Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={E}=∗
      ▷ consumer۰auth γ Ψ state ∗
      consumer۰frag γ Χ2.
  Proof.
    apply subpredsｰwand.
  Qed.
  #[local] Lemma consumerｰdivide {γ Ψ state} Χs E :
    ▷ consumer۰auth γ Ψ state -∗
    consumer۰frag γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={E}=∗
      ▷ consumer۰auth γ Ψ state ∗
      [∗ list] Χ ∈ Χs, consumer۰frag γ Χ.
  Proof.
    apply subpredsｰdivide.
  Qed.
  #[local] Lemma consumerｰproduce {γ Ψ} v :
    consumer۰auth γ Ψ None -∗
    Ψ v -∗
    consumer۰auth γ Ψ (Some v).
  Proof.
    apply subpredsｰproduce.
  Qed.
  #[local] Lemma consumerｰconsume γ Ψ v Χ E :
    ▷ consumer۰auth γ Ψ (Some v) -∗
    consumer۰frag γ Χ ={E}=∗
      ▷ consumer۰auth γ Ψ (Some v) ∗
      ▷^2 Χ v.
  Proof.
    apply subpredsｰconsume.
  Qed.

  Lemma ivar_1۰producerｰexclusive γ :
    ivar_1۰producer γ -∗
    ivar_1۰producer γ -∗
    False.
  Proof.
    apply lstate۰unset₂ｰexclusive.
  Qed.

  Lemma ivar_1۰consumerｰwand {γ Ψ Ξ Χ1} Χ2 :
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰consumer γ Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_1۰consumer γ Χ2.
  Proof.
    iIntros "(:inv) (:consumer) H".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (consumerｰwand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
    iFrameSteps.
  Qed.
  Lemma ivar_1۰consumerｰdivide {γ Ψ Ξ} Χs :
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_1۰consumer γ Χ.
  Proof.
    iIntros "(:inv) (:consumer)".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (consumerｰdivide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
    iFrameSteps.
  Qed.
  Lemma ivar_1۰consumerｰsplit {γ Ψ Ξ} Χ1 Χ2 :
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰consumer γ (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_1۰consumer γ Χ1 ∗
      ivar_1۰consumer γ Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (ivar_1۰consumerｰdivide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma ivar_1۰resultｰagree γ v1 v2 :
    ivar_1۰result γ v1 -∗
    ivar_1۰result γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply lstate۰setｰagree.
  Qed.

  Lemma ivar_1ｰproducerｰresult γ v :
    ivar_1۰producer γ -∗
    ivar_1۰result γ v -∗
    False.
  Proof.
    apply lstateｰunset₂ｰset.
  Qed.

  Lemma ivar_1ｰinvｰresult γ Ψ Ξ v :
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰result γ v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result)".
    iInv "Hinv" as "(:inv۰inner)".
    destruct state as [v_ |]; last first.
    { iDestruct "Hstate" as "(:inv۰state۰unset >)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-.
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma ivar_1ｰinvｰresult' γ Ψ Ξ v :
    £ 1 -∗
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰result γ v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (ivar_1ｰinvｰresult with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_1ｰinvｰresultｰconsumer γ Ψ Ξ v Χ :
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰result γ v -∗
    ivar_1۰consumer γ Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result) (:consumer)".
    iInv "Hinv" as "(:inv۰inner)".
    destruct state as [v_ |]; last first.
    { iDestruct "Hstate" as "(:inv۰state۰unset >)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-.
    iMod (consumerｰconsume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
    iSplitR "HΧ". { iFrameSteps. }
    iSteps.
  Qed.
  Lemma ivar_1ｰinvｰresultｰconsumer' γ Ψ Ξ v Χ :
    £ 2 -∗
    ivar_1۰inv γ Ψ Ξ -∗
    ivar_1۰result γ v -∗
    ivar_1۰consumer γ Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (ivar_1ｰinvｰresultｰconsumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_1٠createｰspec Ψ Ξ :
    {{{
      True
    }}}
      ivar_1٠create ()
    {{{
      γ
    , RET γ;
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰producer γ ∗
      ivar_1۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref t as "Ht" meta:"Hmeta".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

    pose γ :=
      {|ivar_1۰name۰self := t
      ; ivar_1۰name۰lstate := γ_lstate
      ; ivar_1۰name۰consumer := γ_consumer
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists None. iSteps.
  Qed.

  Lemma ivar_1٠makeｰspec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_1٠make v
    {{{
      γ
    , RET γ;
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰result γ v ∗
      ivar_1۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    wp۰rec.
    wp۰ref t as "Ht" meta:"Hmeta".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

    pose γ :=
      {|ivar_1۰name۰self := t
      ; ivar_1۰name۰lstate := γ_lstate
      ; ivar_1۰name۰consumer := γ_consumer
      |}.

    iMod (lstateｰupdate (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
    iDestruct (consumerｰproduce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists (Some v). iSteps.
  Qed.

  Lemma ivar_1٠try_getｰspec γ Ψ Ξ :
    {{{
      ivar_1۰inv γ Ψ Ξ
    }}}
      ivar_1٠try_get γ
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_1۰result γ v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iSpecialize ("HΦ" $! state).
    destruct state as [v |].

    - iDestruct "Hstate" as "(:inv۰state۰set)".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma ivar_1٠try_getｰspecｰresult γ Ψ Ξ v :
    {{{
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰result γ v
    }}}
      ivar_1٠try_get γ
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [v_ |]; last first.
    { iDestruct (lstateｰunset₁ｰset with "Hstate Hlstate_set") as %[]. }
    iDestruct "Hstate" as "(:inv۰state۰set =1)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
    iSplitR "H£ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma ivar_1٠is_unsetｰspec γ Ψ Ξ :
    {{{
      ivar_1۰inv γ Ψ Ξ
    }}}
      ivar_1٠is_unset γ
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_1۰resolved γ
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (ivar_1٠try_getｰspec with "Hinv") as ([v |]) "H".
    all: iSteps.
  Qed.
  Lemma ivar_1٠is_unsetｰspecｰresult γ Ψ Ξ v :
    {{{
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰result γ v
    }}}
      ivar_1٠is_unset γ
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresult) HΦ".

    wp۰rec.
    wp۰apply (ivar_1٠try_getｰspecｰresult with "[$Hinv $Hresult]").
    iSteps.
  Qed.

  Lemma ivar_1٠is_setｰspec γ Ψ Ξ :
    {{{
      ivar_1۰inv γ Ψ Ξ
    }}}
      ivar_1٠is_set γ
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_1۰resolved γ
      else
        True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (ivar_1٠is_unsetｰspec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.
  Lemma ivar_1٠is_setｰspecｰresult γ Ψ Ξ v :
    {{{
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰result γ v
    }}}
      ivar_1٠is_set γ
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresult) HΦ".

    wp۰rec.
    wp۰apply (ivar_1٠is_unsetｰspecｰresult with "[$]").
    iSteps.
  Qed.

  Lemma ivar_1٠getｰspec γ Ψ Ξ v :
    {{{
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰result γ v
    }}}
      ivar_1٠get γ
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hresult) HΦ".

    wp۰rec.
    wp۰apply (ivar_1٠try_getｰspecｰresult with "[$Hinv $Hresult]").
    iSteps.
  Qed.

  Lemma ivar_1٠setｰspec γ Ψ Ξ v :
    {{{
      ivar_1۰inv γ Ψ Ξ ∗
      ivar_1۰producer γ ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_1٠set γ v
    {{{
      RET ();
      ivar_1۰result γ v
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰store.
    destruct state.
    { iDestruct "Hstate" as "(:inv۰state۰set =1)".
      iDestruct (lstateｰunset₂ｰset with "Hlstate_unset₂ Hlstate_set_1") as %[].
    }
    iMod (lstateｰupdate with "Hstate Hlstate_unset₂") as "#Hlstate_set".
    iDestruct (consumerｰproduce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
    iSplitR "HΦ". { iFrameSteps. }
    iSteps.
  Qed.
End ivar_1۰G.

Require zoo_std.ivar_1__opaque.

Please opacify.
