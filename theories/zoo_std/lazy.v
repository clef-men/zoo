Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.subpreds.
Require Import zoo.base.
Require Export zoo_std.lazy__code.
Require Import zoo_std.lazy__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v fn mtx : val.

Zoo name :=
  { self : location
  ; thunk : val
  ; lstate : gname
  ; consumer : gname
  }.

Zoo global :=
  { mutex : mutex
  ; lstate : oneshot unit val
  ; consumer : subpreds val
  }.

Section lazy۰G.
  Context `{lazy۰G : LazyG Σ}.

  Implicit Type Ψ Χ Ξ : val → iProp Σ.

  Variant state :=
    | Unset
    | Setting mtx
    | Set_ v.
  Implicit Type state : state.

  #[local] Please derive Inhabited for state.

  #[local] Definition state۰to_bool state :=
    match state with
    | Set_ _ =>
        true
    | _ =>
        false
    end.
  #[local] Definition state۰to_option state :=
    match state with
    | Set_ v =>
        Some v
    | _ =>
        None
    end.
  #[local] Definition state۰to_val γ state :=
    match state with
    | Unset =>
        ‘Unset( γ.(lazy۰name۰thunk) )
    | Setting mtx =>
        ‘Setting( mtx )
    | Set_ v =>
        ‘Set( v )
    end%V.

  #[local] Definition lstate۰unset₁' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (1/3)) ().
  #[local] Definition lstate۰unset₁ γ :=
    lstate۰unset₁' γ.(lazy۰name۰lstate).
  #[local] Definition lstate۰unset₂' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (2/3)) ().
  #[local] Definition lstate۰unset₂ γ :=
    lstate۰unset₂' γ.(lazy۰name۰lstate).
  #[local] Definition lstate۰set' γ_lstate v :=
    oneshot۰shot γ_lstate v.
  #[local] Definition lstate۰set γ :=
    lstate۰set' γ.(lazy۰name۰lstate).

  #[local] Definition consumer۰auth' :=
    subpreds۰auth.
  #[local] Definition consumer۰auth γ :=
    consumer۰auth' γ.(lazy۰name۰consumer).
  #[local] Definition consumer۰frag' :=
    subpreds۰frag.
  #[local] Definition consumer۰frag γ :=
    consumer۰frag' γ.(lazy۰name۰consumer).

  Please Definition lazy۰result :=
    lstate۰set.
  #[local] Instance : CustomIpat "result" :=
    " #Hlstate_set{_{}}
    ".
  Definition lazy۰resolved γ : iProp Σ :=
    ∃ v,
    lazy۰result γ v.

  #[local] Definition inv۰state۰unset γ Ψ Ξ : iProp Σ :=
    lstate۰unset₁ γ ∗
    lstate۰unset₂ γ ∗
    WP γ.(lazy۰name۰thunk) () {{ v,
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}.
  #[local] Instance : CustomIpat "inv۰state۰unset" :=
    " ( {>;}Hlstate_unset₁{_{}}
      & {>;}Hlstate_unset₂{_{}}
      & Hthunk
      )
    ".
  #[local] Definition inv۰state۰setting γ mtx : iProp Σ :=
    lstate۰unset₁ γ ∗
    mutex۰inv mtx (lazy۰resolved γ).
  #[local] Instance : CustomIpat "inv۰state۰setting" :=
    " ( {>;}Hlstate_unset₁{_{}}
      & #Hmtx_inv{_{}}
      )
    ".
  #[local] Definition inv۰state۰set γ Ξ v : iProp Σ :=
    lstate۰set γ v ∗
    □ Ξ v.
  #[local] Instance : CustomIpat "inv۰state۰set" :=
    " ( {>;}#Hlstate_set{_{}}
      & #HΞ{_{}}
      )
    ".
  #[local] Definition inv۰state γ Ψ Ξ state :=
    match state with
    | Unset =>
        inv۰state۰unset γ Ψ Ξ
    | Setting mtx =>
        inv۰state۰setting γ mtx
    | Set_ v =>
        inv۰state۰set γ Ξ v
    end.

  #[local] Definition inv۰inner γ Ψ Ξ : iProp Σ :=
    ∃ state,
    γ.(lazy۰name۰self) ↦ᵣ state۰to_val γ state ∗
    consumer۰auth γ Ψ (state۰to_option state) ∗
    inv۰state γ Ψ Ξ state.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %state
      & Ht
      & Hconsumer_auth
      & Hstate
      )
    ".
  Please Definition lazy۰inv γ Ψ Ξ : iProp Σ :=
    inv nroot (inv۰inner γ Ψ Ξ).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Please Definition lazy۰consumer :=
    consumer۰frag.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer{}_frag
    ".

  #[global] Instance lazy۰invｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (lazy۰inv γ).
  Proof.
    rewrite /lazy۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰setting /inv۰state۰set.
    solve_proper_prepare. f_contractive. solve_proper.
  Qed.
  #[global] Instance lazy۰invｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      pointwise_relation _ (≡) ==>
      (≡)
    ) (lazy۰inv γ).
  Proof.
    rewrite /lazy۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰setting /inv۰state۰set.
    solve_proper.
  Qed.
  #[global] Instance lazy۰consumerｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (lazy۰consumer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance lazy۰consumerｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      (≡)
    ) (lazy۰consumer γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for lazy۰result.

  Zoo derive Persistent for lazy۰inv.
  Zoo derive Persistent for lazy۰result.

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
  #[local] Lemma consumerｰwand {γ Ψ} {state : option val} {Χ1} Χ2 E :
    ▷ consumer۰auth γ Ψ state -∗
    consumer۰frag γ Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={E}=∗
      ▷ consumer۰auth γ Ψ state ∗
      consumer۰frag γ Χ2.
  Proof.
    apply subpredsｰwand.
  Qed.
  #[local] Lemma consumerｰdivide {γ Ψ} {state : option val} Χs E :
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

  #[local] Lemma inv۰stateｰlstate۰set γ Ψ Ξ state v :
    ▷ inv۰state γ Ψ Ξ state -∗
    lstate۰set γ v -∗
    ◇ (
      ⌜state = Set_ v⌝ ∗
      ▷ inv۰state۰set γ Ξ v
    ).
  Proof.
    iIntros "Hstate Hlstate_set".
    destruct state as [| mtx | v_].
    - iDestruct "Hstate" as "(:inv۰state۰unset >)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    - iDestruct "Hstate" as "(:inv۰state۰setting >)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    - iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
      iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-.
      iFrame "#∗" => //.
  Qed.

  Lemma lazy۰consumerｰwand {γ Ψ Ξ Χ1} Χ2 :
    lazy۰inv γ Ψ Ξ -∗
    lazy۰consumer γ Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    lazy۰consumer γ Χ2.
  Proof.
    iIntros "(:inv) (:consumer) H".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (consumerｰwand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
    iFrameSteps.
  Qed.
  Lemma lazy۰consumerｰdivide {γ Ψ Ξ} Χs :
    lazy۰inv γ Ψ Ξ -∗
    lazy۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, lazy۰consumer γ Χ.
  Proof.
    iIntros "(:inv) (:consumer)".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (consumerｰdivide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
    iFrameSteps.
  Qed.
  Lemma lazy۰consumerｰsplit {γ Ψ Ξ} Χ1 Χ2 :
    lazy۰inv γ Ψ Ξ -∗
    lazy۰consumer γ (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      lazy۰consumer γ Χ1 ∗
      lazy۰consumer γ Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (lazy۰consumerｰdivide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma lazy۰resultｰagree γ v1 v2 :
    lazy۰result γ v1 -∗
    lazy۰result γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply lstate۰setｰagree.
  Qed.

  Lemma lazyｰinvｰresult γ Ψ Ξ v :
    lazy۰inv γ Ψ Ξ -∗
    lazy۰result γ v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result)".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (inv۰stateｰlstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1 >))".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma lazyｰinv_result' γ Ψ Ξ v :
    £ 1 -∗
    lazy۰inv γ Ψ Ξ -∗
    lazy۰result γ v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (lazyｰinvｰresult with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma lazyｰinvｰresultｰconsumer γ Ψ Ξ v Χ :
    lazy۰inv γ Ψ Ξ -∗
    lazy۰result γ v -∗
    lazy۰consumer γ Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result) (:consumer)".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (inv۰stateｰlstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1 >))".
    iMod (consumerｰconsume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
    iSplitR "HΧ". { iFrameSteps. }
    iSteps.
  Qed.
  Lemma lazyｰinvｰresultｰconsumer' γ Ψ Ξ v Χ :
    £ 2 -∗
    lazy۰inv γ Ψ Ξ -∗
    lazy۰result γ v -∗
    lazy۰consumer γ Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (lazyｰinvｰresultｰconsumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma lazy٠makeｰspec Ψ Ξ fn :
    {{{
      WP fn () {{ v,
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}
    }}}
      lazy٠make fn
    {{{
      γ
    , RET γ;
      lazy۰inv γ Ψ Ξ ∗
      lazy۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

    pose γ :=
      {|lazy۰name۰self := t
      ; lazy۰name۰thunk := fn
      ; lazy۰name۰lstate := γ_lstate
      ; lazy۰name۰consumer := γ_consumer
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists Unset. iSteps.
  Qed.

  Lemma lazy٠returnｰspec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      lazy٠return v
    {{{
      γ
    , RET γ;
      lazy۰inv γ Ψ Ξ ∗
      lazy۰result γ v ∗
      lazy۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

    pose γ :=
      {|lazy۰name۰self := t
      ; lazy۰name۰thunk := ()
      ; lazy۰name۰lstate := γ_lstate
      ; lazy۰name۰consumer := γ_consumer
      |}.

    iMod (lstateｰupdate (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
    iDestruct (consumerｰproduce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists (Set_ v). iSteps.
  Qed.

  Lemma lazy٠is_setｰspec γ Ψ Ξ :
    {{{
      lazy۰inv γ Ψ Ξ
    }}}
      lazy٠is_set γ
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        lazy۰resolved γ
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iSpecialize ("HΦ" $! (state۰to_bool state)).
    destruct state as [| mtx | v].

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰set)".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma lazy٠is_setｰspecｰresult γ Ψ Ξ v :
    {{{
      lazy۰inv γ Ψ Ξ ∗
      lazy۰result γ v
    }}}
      lazy٠is_set γ
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod (inv۰stateｰlstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1))".
    iSplitR "H£ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma lazy٠is_unsetｰspec γ Ψ Ξ :
    {{{
      lazy۰inv γ Ψ Ξ
    }}}
      lazy٠is_unset γ
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        lazy۰resolved γ
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (lazy٠is_setｰspec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.
  Lemma lazy٠is_unsetｰspecｰresult γ Ψ Ξ v :
    {{{
      lazy۰inv γ Ψ Ξ ∗
      lazy۰result γ v
    }}}
      lazy٠is_unset γ
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresult) HΦ".

    wp۰rec.
    wp۰apply (lazy٠is_setｰspecｰresult with "[$]").
    iSteps.
  Qed.

  Lemma lazy٠getｰspec γ Ψ Ξ :
    {{{
      lazy۰inv γ Ψ Ξ
    }}}
      lazy٠get γ
    {{{
      v
    , RET v;
      £ 2 ∗
      lazy۰result γ v
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb" forall (Φ).

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.
    iApply (wpｰframeｰwand with "[H£]"); first iAccu.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [| mtx | v_].

    - iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (mutex٠create_lockｰspecｰinit with "[//]") as (mtx) "(Hmtx_init & Hmtx_locked)".
      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰cas as Hcas.

      + iSplitR "Hmtx_init Hmtx_locked HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp۰apply+ (mutex٠unlockｰspecｰinit with "[$]") as "_".
        wp۰apply+ "HLöb".
        iSteps.

      + destruct state; zoo۰simp.
        iDestruct "Hstate" as "(:inv۰state۰unset)".
        iMod (mutex۰initｰtoｰinv (lazy۰resolved γ) with "Hmtx_init [//]") as "#Hmtx_inv".
        iSplitR "Hmtx_locked Hlstate_unset₂ Hthunk HΦ".
        { iExists (Setting mtx). iFrameSteps. }
        iIntros "!> {%}".

        wp۰apply+ (wpｰwand with "Hthunk") as (v) "(HΨ & #HΞ)".
        wp۰pures.

        wp۰bind (_ <- _)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰store.
        destruct state.

        * iDestruct "Hstate" as "(:inv۰state۰unset =1)".
          iDestruct (lstate۰unset₂ｰexclusive with "Hlstate_unset₂ Hlstate_unset₂_1") as %[].

        * iDestruct "Hstate" as "(:inv۰state۰setting =1)".
          iMod (lstateｰupdate with "Hlstate_unset₁_1 Hlstate_unset₂") as "#Hlstate_set".
          iDestruct (consumerｰproduce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
          iSplitR "Hmtx_locked HΦ". { iExists (Set_ v). iFrameSteps. }
          iIntros "!> {%}".

          wp۰apply+ (mutex٠unlockｰspec with "[$Hmtx_inv $Hmtx_locked]"); iSteps.

        * iDestruct "Hstate" as "(:inv۰state۰set =1)".
          iDestruct (lstateｰunset₂ｰset with "Hlstate_unset₂ Hlstate_set_1") as %[].

    - iDestruct "Hstate" as "(:inv۰state۰setting)".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ (mutex٠synchronizeｰspec with "[$]") as "_".
      wp۰apply+ "HLöb".
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰set)".
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma lazy٠getｰspecｰresult γ Ψ Ξ v :
    {{{
      lazy۰inv γ Ψ Ξ ∗
      lazy۰result γ v
    }}}
      lazy٠get γ
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod (inv۰stateｰlstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1))".
    iSplitR "H£ HΦ". { iFrameSteps. }
    iSteps.
  Qed.
End lazy۰G.

Require zoo_std.lazy__opaque.

Please opacify.
