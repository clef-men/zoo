Require Import zoo.prelude.
Require Import zoo.common.countable.
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

Class Ivar3G Σ `{zoo۰G : !ZooG Σ} waiter۰name `{Countable waiter۰name} :=
  { #[local] ivar_3۰G۰lstate۰G :: OneshotG Σ unit val
  ; #[local] ivar_3۰G۰consumer۰G :: SubpredsG Σ val
  ; #[local] ivar_3۰G۰waiters۰G :: MonoGmultisetG Σ (val * waiter۰name)
  }.

Definition ivar_3۰Σ waiter۰name `{Countable waiter۰name} :=
  #[oneshot۰Σ unit val
  ; subpreds۰Σ val
  ; mono_gmultiset۰Σ (val * waiter۰name)
  ].
#[global] Instance subGｰivar_3۰Σ Σ `{zoo۰G : !ZooG Σ} waiter۰name `{Countable waiter۰name} :
  subG (ivar_3۰Σ waiter۰name) Σ →
  Ivar3G Σ waiter۰name.
Proof.
  solve_inG.
Qed.

Module base.
  Variant state :=
    | Unset waiters
    | Set_ v.
  Implicit Type state : state.

  #[local] Instance stateｰinhabited : Inhabited state :=
    populate (Unset []).

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

    Implicit Type t : location.
    Implicit Type ω : waiter۰name.
    Implicit Type ωs : list waiter۰name.
    Implicit Type Ψ Χ Ξ : val → iProp Σ.
    Implicit Type Ω : val → val → waiter۰name → iProp Σ.

    Record ivar_3۰name :=
      { ivar_3۰name۰lstate : gname
      ; ivar_3۰name۰consumer : gname
      ; ivar_3۰name۰waiters : gname
      }.
    Implicit Type γ : ivar_3۰name.

    #[global] Instance ivar_3۰nameｰeq_dec : EqDecision ivar_3۰name :=
      ltac:(solve_decision).
    #[global] Instance ivar_3۰nameｰcountable :
      Countable ivar_3۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition lstate۰unset₁' γ_lstate :=
      oneshot۰pending γ_lstate (DfracOwn (1/3)) ().
    #[local] Definition lstate۰unset₁ γ :=
      lstate۰unset₁' γ.(ivar_3۰name۰lstate).
    #[local] Definition lstate۰unset₂' γ_lstate :=
      oneshot۰pending γ_lstate (DfracOwn (2/3)) ().
    #[local] Definition lstate۰unset₂ γ :=
      lstate۰unset₂' γ.(ivar_3۰name۰lstate).
    #[local] Definition lstate۰set γ :=
      oneshot۰shot γ.(ivar_3۰name۰lstate).

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

    #[local] Definition inv۰state۰unset t γ Ω waiters : iProp Σ :=
      ∃ ωs,
      lstate۰unset₁ γ ∗
      waiters۰auth γ Own waiters ωs ∗
      [∗ list] waiter; ω ∈ waiters; ωs, Ω #t waiter ω.
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
    #[local] Definition inv۰state t γ Ξ Ω state :=
      match state with
      | Unset waiters =>
          inv۰state۰unset t γ Ω waiters
      | Set_ v =>
          inv۰state۰set γ Ξ v
      end.

    #[local] Definition inv۰inner t γ Ψ Ξ Ω : iProp Σ :=
      ∃ state,
      t ↦ᵣ state ∗
      consumer۰auth γ Ψ (state۰to_option state) ∗
      inv۰state t γ Ξ Ω state.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state
        & Ht
        & Hconsumer_auth
        & Hstate
        )
      ".
    Definition ivar_3۰inv t γ Ψ Ξ Ω : iProp Σ :=
      inv nroot (inv۰inner t γ Ψ Ξ Ω).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition ivar_3۰producer :=
      lstate۰unset₂.
    #[local] Instance : CustomIpat "producer" :=
      " Hlstate_unset₂{_{}}
      ".

    Definition ivar_3۰consumer :=
      consumer۰frag.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{}_frag
      ".

    Definition ivar_3۰result :=
      lstate۰set.
    #[local] Instance : CustomIpat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition ivar_3۰resolved γ : iProp Σ :=
      ∃ v,
      ivar_3۰result γ v.

    Definition ivar_3۰waiters γ :=
      waiters۰auth γ Discard.

    Definition ivar_3۰waiter :=
      waiters۰elem.

    #[global] Instance ivar_3۰invｰcontractive t γ n :
      Proper (
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
        (≡{n}≡)
      ) (ivar_3۰inv t γ).
    Proof.
      rewrite /ivar_3۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
      intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ Ω1 Ω2 HΩ.
      repeat (apply HΩ || f_contractive || f_equiv). done.
    Qed.
    #[global] Instance ivar_3۰invｰproper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_3۰inv t γ).
    Proof.
      intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ Ω1 Ω2 HΩ.
      apply equiv_dist => n.
      apply ivar_3۰invｰcontractive.
      - intros v.
        apply dist_dist_later, equiv_dist, HΨ.
      - intros v.
        apply dist_dist_later, equiv_dist, HΞ.
      - clear t. intros t waiter ω.
        apply dist_dist_later, equiv_dist, HΩ.
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
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_3۰consumer γ).
    Proof.
      apply _.
    Qed.

    #[local] Instance waiters۰authｰtimeless γ own waiters ωs :
      Timeless (waiters۰auth γ own waiters ωs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰producerｰtimeless γ :
      Timeless (ivar_3۰producer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰resultｰtimeless γ v :
      Timeless (ivar_3۰result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰waitersｰtimeless γ waiters ωs :
      Timeless (ivar_3۰waiters γ waiters ωs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰waiterｰtimeless γ waiter ω :
      Timeless (ivar_3۰waiter γ waiter ω).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_3۰invｰpersistent t γ Ψ Ξ Ω :
      Persistent (ivar_3۰inv t γ Ψ Ξ Ω).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰resultｰpersistent γ v :
      Persistent (ivar_3۰result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰waitersｰpersistent γ waiters ωs :
      Persistent (ivar_3۰waiters γ waiters ωs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3۰waiterｰpersistent γ waiter ω :
      Persistent (ivar_3۰waiter γ waiter ω).
    Proof.
      apply _.
    Qed.

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

    Lemma ivar_3۰consumerｰwand {t γ Ψ Ξ Ω Χ1} Χ2 :
      ivar_3۰inv t γ Ψ Ξ Ω -∗
      ivar_3۰consumer γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
      ivar_3۰consumer γ Χ2.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (consumerｰwand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma ivar_3۰consumerｰdivide {t γ Ψ Ξ Ω} Χs :
      ivar_3۰inv t γ Ψ Ξ Ω -∗
      ivar_3۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, ivar_3۰consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer)".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (consumerｰdivide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
      iFrameSteps.
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

    Lemma ivar_3ｰinvｰresult t γ Ψ Ξ Ω v :
      ivar_3۰inv t γ Ψ Ξ Ω -∗
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
    Lemma ivar_3ｰinvｰresultｰconsumer t γ Ψ Ξ Ω v Χ :
      ivar_3۰inv t γ Ψ Ξ Ω -∗
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
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰producer γ ∗
        ivar_3۰consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".
      iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ :=
        {|ivar_3۰name۰lstate := γ_lstate
        ; ivar_3۰name۰consumer := γ_consumer
        ; ivar_3۰name۰waiters := γ_waiters
        |}.

      iApply ("HΦ" $! t γ).
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
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰consumer γ Ψ ∗
        ivar_3۰result γ v ∗
        ivar_3۰waiters γ [] []
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumerｰalloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".
      iMod waitersｰalloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ :=
        {|ivar_3۰name۰lstate := γ_lstate
        ; ivar_3۰name۰consumer := γ_consumer
        ; ivar_3۰name۰waiters := γ_waiters
        |}.

      iMod (lstateｰupdate (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumerｰproduce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".
      iMod (waiters۰authｰdiscard γ with "Hwaiters_auth") as "#Hwaiters_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Set_ v). iSteps.
    Qed.

    Lemma ivar_3٠is_unsetｰspec t γ Ψ Ξ Ω :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω
      }}}
        ivar_3٠is_unset #t
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
    Lemma ivar_3٠is_unsetｰspecｰresult t γ Ψ Ξ Ω v :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰result γ v
      }}}
        ivar_3٠is_unset #t
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

    Lemma ivar_3٠is_setｰspec t γ Ψ Ξ Ω :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω
      }}}
        ivar_3٠is_set #t
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
    Lemma ivar_3٠is_setｰspecｰresult t γ Ψ Ξ Ω v :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰result γ v
      }}}
        ivar_3٠is_set #t
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

    Lemma ivar_3٠try_getｰspec t γ Ψ Ξ Ω :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω
      }}}
        ivar_3٠try_get #t
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
    Lemma ivar_3٠try_getｰspecｰresult t γ Ψ Ξ Ω v :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰result γ v
      }}}
        ivar_3٠try_get #t
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

    Lemma ivar_3٠getｰspec t γ Ψ Ξ Ω v :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰result γ v
      }}}
        ivar_3٠get #t
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

    Lemma ivar_3٠waitｰspec ω P t γ Ψ Ξ Ω waiter :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        P ∗
        (P -∗ Ω #t waiter ω)
      }}}
        ivar_3٠wait #t waiter
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

        + destruct state as [waiters' | v]; zoo_simp.
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

    Lemma ivar_3٠setｰspec t γ Ψ Ξ Ω v :
      {{{
        ivar_3۰inv t γ Ψ Ξ Ω ∗
        ivar_3۰producer γ ∗
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_3٠set #t v
      {{{
        waiters ωs
      , RET list۰to_val waiters;
        ivar_3۰result γ v ∗
        ivar_3۰waiters γ waiters ωs ∗
        [∗ list] waiter; ω ∈ waiters; ωs, Ω #t waiter ω
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

  #[global] Opaque ivar_3۰inv.
  #[global] Opaque ivar_3۰producer.
  #[global] Opaque ivar_3۰consumer.
  #[global] Opaque ivar_3۰result.
  #[global] Opaque ivar_3۰waiter.
  #[global] Opaque ivar_3۰waiters.
End base.

Require zoo_std.ivar_3__opaque.

Section ivar_3۰G.
  Context `{ivar_3۰G : Ivar3G Σ waiter۰name}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type Ψ Χ Ξ : val → iProp Σ.
  Implicit Type Ω : val → val → waiter۰name → iProp Σ.

  Definition ivar_3۰inv t Ψ Ξ Ω : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_3۰inv 𝑡 γ Ψ Ξ Ω.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ivar_3۰producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_3۰producer γ.
  #[local] Instance : CustomIpat "producer" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hproducer{_{}}
      )
    ".

  Definition ivar_3۰consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_3۰consumer γ Χ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition ivar_3۰result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_3۰result γ v.
  #[local] Instance : CustomIpat "result" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresult{_{}}
      )
    ".
  Definition ivar_3۰resolved t : iProp Σ :=
    ∃ v,
    ivar_3۰result t v.

  Definition ivar_3۰waiters t waiters ωs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_3۰waiters γ waiters ωs.
  #[local] Instance : CustomIpat "waiters" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hwaiters{_{}}
      )
    ".

  Definition ivar_3۰waiter t waiter ω : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_3۰waiter γ waiter ω.
  #[local] Instance : CustomIpat "waiter" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hwaiter{_{}}
      )
    ".

  #[global] Instance ivar_3۰invｰcontractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_3۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_3۰invｰproper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_3۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_3۰consumerｰcontractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_3۰consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_3۰consumerｰproper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_3۰consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_3۰producerｰtimeless t :
    Timeless (ivar_3۰producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰resultｰtimeless t v :
    Timeless (ivar_3۰result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰waitersｰtimeless t waiters ωs :
    Timeless (ivar_3۰waiters t waiters ωs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰waiterｰtimeless t waiter ω :
    Timeless (ivar_3۰waiter t waiter ω).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_3۰invｰpersistent t Ψ Ξ Ω :
    Persistent (ivar_3۰inv t Ψ Ξ Ω).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰resultｰpersistent t v :
    Persistent (ivar_3۰result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰waitersｰpersistent t waiters ωs :
    Persistent (ivar_3۰waiters t waiters ωs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3۰waiterｰpersistent t waiter ω :
    Persistent (ivar_3۰waiter t waiter ω).
  Proof.
    apply _.
  Qed.

  Lemma ivar_3۰producerｰexclusive t :
    ivar_3۰producer t -∗
    ivar_3۰producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3۰producerｰexclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma ivar_3۰consumerｰwand {t Ψ Ξ Ω Χ1} Χ2 :
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_3۰consumer t Χ2.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_3۰consumerｰwand with "Hinv_1 Hconsumer_2 H") as "H".
    iSteps.
  Qed.
  Lemma ivar_3۰consumerｰdivide {t Ψ Ξ Ω} Χs :
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_3۰consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_3۰consumerｰdivide with "Hinv_1 Hconsumer_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma ivar_3۰consumerｰsplit {t Ψ Ξ Ω} Χ1 Χ2 :
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_3۰consumer t Χ1 ∗
      ivar_3۰consumer t Χ2.
  Proof.
    iIntros "#Hinv Hconsumer".
    iMod (ivar_3۰consumerｰdivide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma ivar_3۰resultｰagree t v1 v2 :
    ivar_3۰result t v1 -∗
    ivar_3۰result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3۰resultｰagree with "Hresult_1 Hresult_2").
  Qed.

  Lemma ivar_3ｰproducerｰresult t v :
    ivar_3۰producer t -∗
    ivar_3۰result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3ｰproducerｰresult with "Hproducer_1 Hresult_2").
  Qed.

  Lemma ivar_3ｰinvｰresult t Ψ Ξ Ω v :
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %<-.
    iApply (base.ivar_3ｰinvｰresult with "Hinv_1 Hresult_2").
  Qed.
  Lemma ivar_3ｰinvｰresult' t Ψ Ξ Ω v :
    £ 1 -∗
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (ivar_3ｰinvｰresult with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_3ｰinvｰresultｰconsumer t Ψ Ξ Ω v Χ :
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰result t v -∗
    ivar_3۰consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:consumer =3)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (metaｰagree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.ivar_3ｰinvｰresultｰconsumer with "Hinv_1 Hresult_2 Hconsumer_3").
  Qed.
  Lemma ivar_3ｰinvｰresultｰconsumer' t Ψ Ξ Ω v Χ :
    £ 2 -∗
    ivar_3۰inv t Ψ Ξ Ω -∗
    ivar_3۰result t v -∗
    ivar_3۰consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (ivar_3ｰinvｰresultｰconsumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_3۰waiterｰvalid t waiters ωs waiter ω :
    ivar_3۰waiters t waiters ωs -∗
    ivar_3۰waiter t waiter ω -∗
      ∃ i,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜ωs !! i = Some ω⌝.
  Proof.
    iIntros "(:waiters =1) (:waiter =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3۰waiterｰvalid with "Hwaiters_1 Hwaiter_2").
  Qed.

  Lemma ivar_3٠createｰspec Ψ Ξ Ω :
    {{{
      True
    }}}
      ivar_3٠create ()
    {{{
      t
    , RET t;
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰producer t ∗
      ivar_3۰consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.ivar_3٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_3٠makeｰspec Ψ Ξ Ω v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_3٠make v
    {{{
      t
    , RET t;
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰consumer t Ψ ∗
      ivar_3۰result t v ∗
      ivar_3۰waiters t [] []
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    iApply wpｰfupd.
    wp۰apply (base.ivar_3٠makeｰspec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_3٠is_unsetｰspec t Ψ Ξ Ω :
    {{{
      ivar_3۰inv t Ψ Ξ Ω
    }}}
      ivar_3٠is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_3۰resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_3٠is_unsetｰspec with "[$]") as (b) "Hb".
    rewrite /ivar_3۰resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_3٠is_unsetｰspecｰresult t Ψ Ξ Ω v :
    {{{
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰result t v
    }}}
      ivar_3٠is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_3٠is_unsetｰspecｰresult with "[$] HΦ").
  Qed.

  Lemma ivar_3٠is_setｰspec t Ψ Ξ Ω :
    {{{
      ivar_3۰inv t Ψ Ξ Ω
    }}}
      ivar_3٠is_set t
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_3۰resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_3٠is_setｰspec with "[$]") as (b) "Hb".
    rewrite /ivar_3۰resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_3٠is_setｰspecｰresult t Ψ Ξ Ω v :
    {{{
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰result t v
    }}}
      ivar_3٠is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_3٠is_setｰspecｰresult with "[$] HΦ").
  Qed.

  Lemma ivar_3٠try_getｰspec t Ψ Ξ Ω :
    {{{
      ivar_3۰inv t Ψ Ξ Ω
    }}}
      ivar_3٠try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_3۰result t v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_3٠try_getｰspec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma ivar_3٠try_getｰspecｰresult t Ψ Ξ Ω v :
    {{{
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰result t v
    }}}
      ivar_3٠try_get t
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_3٠try_getｰspecｰresult with "[$] HΦ").
  Qed.

  Lemma ivar_3٠getｰspec t Ψ Ξ Ω v :
    {{{
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰result t v
    }}}
      ivar_3٠get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_3٠getｰspec with "[$] HΦ").
  Qed.

  Lemma ivar_3٠waitｰspec ω P t Ψ Ξ Ω waiter :
    {{{
      ivar_3۰inv t Ψ Ξ Ω ∗
      P ∗
      (P -∗ Ω t waiter ω)
    }}}
      ivar_3٠wait t waiter
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_3۰result t v ∗
        P
      else
        ivar_3۰waiter t waiter ω
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HP & HΩ) HΦ".

    wp۰apply (base.ivar_3٠waitｰspec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.

  Lemma ivar_3٠setｰspec t Ψ Ξ Ω v :
    {{{
      ivar_3۰inv t Ψ Ξ Ω ∗
      ivar_3۰producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_3٠set t v
    {{{
      waiters ωs
    , RET list۰to_val waiters;
      ivar_3۰result t v ∗
      ivar_3۰waiters t waiters ωs ∗
      [∗ list] waiter; ω ∈ waiters; ωs, Ω t waiter ω
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:producer =2) & HΨ & HΞ) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_3٠setｰspec _ _ Ψ with "[$]").
    iSteps.
  Qed.
End ivar_3۰G.

#[global] Opaque ivar_3۰inv.
#[global] Opaque ivar_3۰producer.
#[global] Opaque ivar_3۰consumer.
#[global] Opaque ivar_3۰result.
#[global] Opaque ivar_3۰waiter.
#[global] Opaque ivar_3۰waiters.
