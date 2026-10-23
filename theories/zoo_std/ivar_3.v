Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.mono_gmultiset.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.subpreds.
Require Import zoo.base.
Require Import zoo_std.list.
Require Import zoo_std.option.
Require Export zoo_std.ivar_3__code.
Require Import zoo_std.ivar_3__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v waiter ctx : val.
Implicit Type waiters : list val.
Implicit Type own : ownership.

Zoo name :=
  { self : location
  ; lstate : gname
  ; consumer : gname
  ; waiters : gname
  }.

Zoo global waiter۰name `{Countable waiter۰name} :=
  { lstate : oneshot unit val
  ; consumer : subpreds val
  ; waiters : mono_gmultiset (val * waiter۰name)
  }.

Variant state :=
  | Unset waiters
  | Set_ v.
Implicit Type state : state.

#[local] Please derive Inhabited for state.

#[local] Definition state۰to_bool state :=
  match state with
  | Unset _ =>
      false
  | Set_ _ =>
      true
  end.
#[local] Definition state۰to_option state :=
  match state with
  | Unset _ =>
      None
  | Set_ v =>
      Some v
  end.
#[local] Coercion state۰to_val state :=
  match state with
  | Unset waiters =>
      ‘Unset[ list۰to_val waiters ]
  | Set_ v =>
      ‘Set( v )
  end%V.

Section ivar_3۰G.
  Context `{ivar_3۰G : Ivar3G Σ waiter۰name}.

  Implicit Type ω : waiter۰name.
  Implicit Type ωs : list waiter۰name.
  Implicit Type Ψ Χ Ξ : val → iProp Σ.
  Implicit Type Ω : ivar_3۰name → val → waiter۰name → iProp Σ.

  #[local] Definition lstate۰unset₁' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (1/3)) ().
  #[local] Definition lstate۰unset₁ γ :=
    lstate۰unset₁' γ.(ivar_3۰name۰lstate).
  #[local] Definition lstate۰unset₂' γ_lstate :=
    oneshot۰pending γ_lstate (DfracOwn (2/3)) ().
  #[local] Definition lstate۰unset₂ γ :=
    lstate۰unset₂' γ.(ivar_3۰name۰lstate).
  #[local] Definition lstate۰set γ v :=
    oneshot۰shot γ.(ivar_3۰name۰lstate) v.

  #[local] Definition consumer۰auth' :=
    subpreds۰auth.
  #[local] Definition consumer۰auth γ :=
    consumer۰auth' γ.(ivar_3۰name۰consumer).
  #[local] Definition consumer۰frag' :=
    subpreds۰frag.
  #[local] Definition consumer۰frag γ :=
    consumer۰frag' γ.(ivar_3۰name۰consumer).

  #[local] Definition waiters۰auth' γ_waiters own waiters ωs : iProp Σ :=
    ∃ 𝑤𝑎𝑖𝑡𝑒𝑟𝑠,
    ⌜𝑤𝑎𝑖𝑡𝑒𝑟𝑠 = list_to_set_disj (zip waiters ωs)⌝ ∗
    mono_gmultiset۰auth γ_waiters own 𝑤𝑎𝑖𝑡𝑒𝑟𝑠.
  #[local] Definition waiters۰auth γ :=
    waiters۰auth' γ.(ivar_3۰name۰waiters).
  #[local] Instance : CustomIpat "waiters۰auth" :=
    " ( %𝑤𝑎𝑖𝑡𝑒𝑟𝑠
      & ->
      & Hauth
      )
    ".
  #[local] Definition waiters۰elem γ waiter ω :=
    mono_gmultiset۰elem γ.(ivar_3۰name۰waiters) (waiter, ω).

  #[local] Definition inv۰state۰unset γ Ω waiters : iProp Σ :=
    ∃ ωs,
    lstate۰unset₁ γ ∗
    waiters۰auth γ Own waiters ωs ∗
    [∗ list] waiter; ω ∈ waiters; ωs, Ω γ waiter ω.
  #[local] Instance : CustomIpat "inv۰state۰unset" :=
    " ( %ωs
      & {>;}Hlstate_unset₁
      & {>;}Hwaiters_auth
      & Hwaiters
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
  #[local] Definition inv۰state γ Ξ Ω state :=
    match state with
    | Unset waiters =>
        inv۰state۰unset γ Ω waiters
    | Set_ v =>
        inv۰state۰set γ Ξ v
    end.

  #[local] Definition inv۰inner γ Ψ Ξ Ω : iProp Σ :=
    ∃ state,
    γ.(ivar_3۰name۰self) ↦ᵣ state ∗
    consumer۰auth γ Ψ (state۰to_option state) ∗
    inv۰state γ Ξ Ω state.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %state
      & Hself
      & Hconsumer_auth
      & Hstate
      )
    ".
  Please Definition ivar_3۰inv γ Ψ Ξ Ω : iProp Σ :=
    inv nroot (inv۰inner γ Ψ Ξ Ω).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Please Definition ivar_3۰producer :=
    lstate۰unset₂.
  #[local] Instance : CustomIpat "producer" :=
    " Hlstate_unset₂{_{}}
    ".

  Please Definition ivar_3۰consumer :=
    consumer۰frag.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer{}_frag
    ".

  Please Definition ivar_3۰result :=
    lstate۰set.
  #[local] Instance : CustomIpat "result" :=
    " #Hlstate_set{_{}}
    ".
  Definition ivar_3۰resolved γ : iProp Σ :=
    ∃ v,
    ivar_3۰result γ v.

  Please Definition ivar_3۰waiters γ :=
    waiters۰auth γ Discard.

  Please Definition ivar_3۰waiter :=
    waiters۰elem.

  #[global] Instance ivar_3۰invｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_3۰inv γ).
  Proof.
    rewrite /ivar_3۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
    solve_contractive.
  Qed.
  #[global] Instance ivar_3۰invｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      pointwise_relation _ (≡) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_3۰inv γ).
  Proof.
    rewrite /ivar_3۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
    solve_proper.
  Qed.
  #[global] Instance ivar_3۰consumerｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_3۰consumer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰consumerｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      (≡)
    ) (ivar_3۰consumer γ).
  Proof.
    apply _.
  Qed.

  #[local] Zoo derive Timeless for waiters۰auth.
  Zoo derive Timeless for ivar_3۰producer.
  Zoo derive Timeless for ivar_3۰result.
  Zoo derive Timeless for ivar_3۰waiters.
  Zoo derive Timeless for ivar_3۰waiter.

  Zoo derive Persistent for ivar_3۰inv.
  Zoo derive Persistent for ivar_3۰result.
  Zoo derive Persistent for ivar_3۰waiters.
  Zoo derive Persistent for ivar_3۰waiter.

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
    iIntros "Hpending1 Hpending2".
    iDestruct (oneshot۰pendingｰvalidｰ2 with "Hpending1 Hpending2") as %(? & _). done.
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

  #[local] Lemma waitersｰalloc :
    ⊢ |==>
      ∃ γ_waiters,
      waiters۰auth' γ_waiters Own [] [].
  Proof.
    iMod (mono_gmultisetｰalloc ∅) as "(%γ_waiters & $)".
    iSteps.
  Qed.
  #[local] Lemma waiters۰elemｰvalid γ own waiters ωs waiter ω :
    waiters۰auth γ own waiters ωs -∗
    waiters۰elem γ waiter ω -∗
      ∃ i,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜ωs !! i = Some ω⌝.
  Proof.
    iIntros "(:waiters۰auth) Helem".
    iDestruct (mono_gmultiset۰elemｰvalid with "Hauth Helem") as %(i & (Hwaiters_lookup & Hωs_lookup)%lookup_zip_Some)%elem_of_list_to_set_disj%list_elem_of_lookup.
    iSteps.
  Qed.
  #[local] Lemma waitersｰinsert {γ waiters ωs} waiter ω :
    waiters۰auth γ Own waiters ωs ⊢ |==>
      waiters۰auth γ Own (waiter :: waiters) (ω :: ωs) ∗
      waiters۰elem γ waiter ω.
  Proof.
    iIntros "(:waiters۰auth)".
    iMod (mono_gmultisetｰinsert' (waiter, ω) with "Hauth") as "($ & $)".
    iSteps.
  Qed.
  #[local] Lemma waiters۰authｰdiscard γ waiters ωs :
    waiters۰auth γ Own waiters ωs ⊢ |==>
    waiters۰auth γ Discard waiters ωs.
  Proof.
    iIntros "(:waiters۰auth)".
    iMod (mono_gmultiset۰authｰpersist with "Hauth") as "$".
    iSteps.
  Qed.
  Opaque waiters۰auth'.

  Lemma ivar_3۰producerｰexclusive γ :
    ivar_3۰producer γ -∗
    ivar_3۰producer γ -∗
    False.
  Proof.
    apply lstate۰unset₂ｰexclusive.
  Qed.

  Lemma ivar_3۰consumerｰwand {γ Ψ Ξ Ω Χ1} Χ2 :
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰consumer γ Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_3۰consumer γ Χ2.
  Proof.
    iIntros "(:inv) (:consumer) H".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (consumerｰwand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
    iFrameSteps.
  Qed.
  Lemma ivar_3۰consumerｰdivide {γ Ψ Ξ Ω} Χs :
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_3۰consumer γ Χ.
  Proof.
    iIntros "(:inv) (:consumer)".
    iInv "Hinv" as "(:inv۰inner)".
    iMod (consumerｰdivide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
    iFrameSteps.
  Qed.
  Lemma ivar_3۰consumerｰsplit {γ Ψ Ξ Ω} Χ1 Χ2 :
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰consumer γ (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_3۰consumer γ Χ1 ∗
      ivar_3۰consumer γ Χ2.
  Proof.
    iIntros "#Hinv Hconsumer".
    iMod (ivar_3۰consumerｰdivide [Χ1; Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma ivar_3۰resultｰagree γ v1 v2 :
    ivar_3۰result γ v1 -∗
    ivar_3۰result γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply lstate۰setｰagree.
  Qed.

  Lemma ivar_3ｰproducerｰresult γ v :
    ivar_3۰producer γ -∗
    ivar_3۰result γ v -∗
    False.
  Proof.
    apply lstateｰunset₂ｰset.
  Qed.

  Lemma ivar_3ｰinvｰresult γ Ψ Ξ Ω v :
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰result γ v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result)".
    iInv "Hinv" as "(:inv۰inner)".
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(:inv۰state۰unset >)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-.
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma ivar_3ｰinvｰresult' γ Ψ Ξ Ω v :
    £ 1 -∗
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰result γ v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (ivar_3ｰinvｰresult with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_3ｰinvｰresultｰconsumer γ Ψ Ξ Ω v Χ :
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰result γ v -∗
    ivar_3۰consumer γ Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result) (:consumer)".
    iInv "Hinv" as "(:inv۰inner)".
    destruct state as [v_ |].
    { iDestruct "Hstate" as "(:inv۰state۰unset >)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-.
    iMod (consumerｰconsume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
    iSplitR "HΧ". { iFrameSteps. }
    iSteps.
  Qed.
  Lemma ivar_3ｰinvｰresultｰconsumer' γ Ψ Ξ Ω v Χ :
    £ 2 -∗
    ivar_3۰inv γ Ψ Ξ Ω -∗
    ivar_3۰result γ v -∗
    ivar_3۰consumer γ Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (ivar_3ｰinvｰresultｰconsumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_3۰waiterｰvalid γ waiters ωs waiter ω :
    ivar_3۰waiters γ waiters ωs -∗
    ivar_3۰waiter γ waiter ω -∗
      ∃ i,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜ωs !! i = Some ω⌝.
  Proof.
    apply waiters۰elemｰvalid.
  Qed.

  Lemma ivar_3٠createｰspec Ψ Ξ Ω :
    {{{
      True
    }}}
      ivar_3٠create ()
    {{{
      γ
    , RET γ;
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰producer γ ∗
      ivar_3۰consumer γ Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ :=
      {|ivar_3۰name۰self := t
      ; ivar_3۰name۰lstate := γ_lstate
      ; ivar_3۰name۰consumer := γ_consumer
      ; ivar_3۰name۰waiters := γ_waiters
      |}.

    iApply ("HΦ" $! γ).
    iFrame.
    iApply inv_alloc.
    iSteps. iExists (Unset []). iSteps.
    iApply (big_sepL2_nil with "[//]").
  Qed.

  Lemma ivar_3٠makeｰspec Ψ Ξ Ω v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_3٠make v
    {{{
      γ
    , RET γ;
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰consumer γ Ψ ∗
      ivar_3۰result γ v ∗
      ivar_3۰waiters γ [] []
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".
    iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

    pose γ :=
      {|ivar_3۰name۰self := t
      ; ivar_3۰name۰lstate := γ_lstate
      ; ivar_3۰name۰consumer := γ_consumer
      ; ivar_3۰name۰waiters := γ_waiters
      |}.

    iMod (lstateｰupdate (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
    iDestruct (consumerｰproduce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".
    iMod (waiters۰authｰdiscard γ with "Hwaiters_auth") as "#Hwaiters_auth".

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists (Set_ v). iSteps.
  Qed.

  Lemma ivar_3٠is_unsetｰspec γ Ψ Ξ Ω :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω
    }}}
      ivar_3٠is_unset γ
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_3۰resolved γ
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iSpecialize ("HΦ" $! (￢ state۰to_bool state)).
    destruct state as [waiters | v].

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰set)".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iStep 5. iExists v. iSteps.
  Qed.
  Lemma ivar_3٠is_unsetｰspecｰresult γ Ψ Ξ Ω v :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰result γ v
    }}}
      ivar_3٠is_unset γ
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(:inv۰state۰unset)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
    iSplitR "H£ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma ivar_3٠is_setｰspec γ Ψ Ξ Ω :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω
    }}}
      ivar_3٠is_set γ
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_3۰resolved γ
      else
        True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (ivar_3٠is_unsetｰspec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.
  Lemma ivar_3٠is_setｰspecｰresult γ Ψ Ξ Ω v :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰result γ v
    }}}
      ivar_3٠is_set γ
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresult) HΦ".

    wp۰rec.
    wp۰apply (ivar_3٠is_unsetｰspecｰresult with "[$]").
    iSteps.
  Qed.

  Lemma ivar_3٠try_getｰspec γ Ψ Ξ Ω :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω
    }}}
      ivar_3٠try_get γ
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_3۰result γ v
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
    iSpecialize ("HΦ" $! (state۰to_option state)).
    destruct state as [waiters | v].

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰set)".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma ivar_3٠try_getｰspecｰresult γ Ψ Ξ Ω v :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰result γ v
    }}}
      ivar_3٠try_get γ
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ".

    wp۰rec credits:"H£".
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(:inv۰state۰unset)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
    iSplitR "H£ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma ivar_3٠getｰspec γ Ψ Ξ Ω v :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰result γ v
    }}}
      ivar_3٠get γ
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
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(:inv۰state۰unset)".
      iDestruct (lstateｰunset₁ｰset with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰set =1)".
    iDestruct (lstate۰setｰagree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
    iSplitR "H£ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma ivar_3٠waitｰspec ω P γ Ψ Ξ Ω waiter :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω ∗
      P ∗
      (P -∗ Ω γ waiter ω)
    }}}
      ivar_3٠wait γ waiter
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_3۰result γ v ∗
        P
      else
        ivar_3۰waiter γ waiter ω
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HP & HΩ) HΦ".
    iLöb as "HLöb".

    wp۰rec credits:"H£". wp۰pures.
    iApply (lc_weaken 2) in "H£"; first done.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [waiters | v].

    - iSplitR "HP HΩ H£ HΦ". { iFrameSteps. }
      iModIntro.

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰cas as Hcas.

      + iSplitR "HP HΩ HΦ". { iFrameSteps. }
        iModIntro.

        wp۰apply+ ("HLöb" with "HP HΩ HΦ").

      + destruct state as [waiters' | v]; zoo۰simp.
        iDestruct "Hstate" as "(:inv۰state۰unset)".
        iMod (waitersｰinsert waiter with "Hwaiters_auth") as "(Hwaiters_auth & #Hwaiters_elem)".
        iDestruct (big_sepL2_cons₂' _ waiter ω with "[HP HΩ H£] Hwaiters") as "Hwaiters". 1: iSteps.
        iSplitR "HΦ". { iExists (Unset (waiter :: waiters)). iFrameSteps. }
        iSpecialize ("HΦ" $! None).
        iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰set)".
      iSplitR "HP HΩ H£ HΦ". { iFrameSteps. }
      iSpecialize ("HΦ" $! (Some v)).
      iSteps.
  Qed.

  Lemma ivar_3٠setｰspec γ Ψ Ξ Ω v :
    {{{
      ivar_3۰inv γ Ψ Ξ Ω ∗
      ivar_3۰producer γ ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_3٠set γ v
    {{{
      waiters ωs
    , RET list۰to_val waiters;
      ivar_3۰result γ v ∗
      ivar_3۰waiters γ waiters ωs ∗
      [∗ list] waiter; ω ∈ waiters; ωs, Ω γ waiter ω
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰xchg.
    destruct state; last first.
    { iDestruct "Hstate" as "(:inv۰state۰set =1)".
      iDestruct (lstateｰunset₂ｰset with "Hlstate_unset₂ Hlstate_set_1") as %[].
    }
    iDestruct "Hstate" as "(:inv۰state۰unset)".
    iMod (lstateｰupdate with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
    iDestruct (consumerｰproduce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
    iMod (waiters۰authｰdiscard with "Hwaiters_auth") as "#Hwaiters_auth".
    iSplitR "Hwaiters HΦ". { iExists (Set_ v). iSteps. }
    iSteps.
  Qed.
End ivar_3۰G.

Require zoo_std.ivar_3__opaque.

Please opacify.
