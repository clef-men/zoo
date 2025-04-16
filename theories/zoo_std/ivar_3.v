From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.oneshot
  lib.excl.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  ivar_3__code.
From zoo_std Require Import
  ivar_3__types
  option
  lst.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types v waiter : val.
Implicit Types waiters : list val.

Class Ivar3G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ivar_3_G_lstate_G :: OneshotG Σ unit val ;
  #[local] ivar_3_G_excl_G :: ExclG Σ unitO ;
}.

Definition ivar_3_Σ := #[
  oneshot_Σ unit val ;
  excl_Σ unitO
].
#[global] Instance subG_ivar_3_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ivar_3_Σ Σ →
  Ivar3G Σ .
Proof.
  solve_inG.
Qed.

Inductive state :=
  | Unset waiters
  | Set_ v.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate (Unset []).

#[local] Definition state_to_bool state :=
  match state with
  | Unset _ =>
      false
  | Set_ _ =>
      true
  end.
#[local] Definition state_to_option state :=
  match state with
  | Unset _ =>
      None
  | Set_ v =>
      Some v
  end.
#[local] Coercion state_to_val state :=
  match state with
  | Unset waiters =>
      ‘Unset[ lst_to_val waiters ]
  | Set_ v =>
      ‘Set( v )
  end%V.

Section ivar_3_G.
  Context `{ivar_3_G : Ivar3G Σ}.

  Implicit Types Ψ Χ : val → iProp Σ.

  Record metadata := {
    metadata_lstate : gname ;
    metadata_consumer : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition lstate_unset₁' γ_lstate :=
    oneshot_pending γ_lstate (DfracOwn (1/3)) ().
  #[local] Definition lstate_unset₁ γ :=
    lstate_unset₁' γ.(metadata_lstate).
  #[local] Definition lstate_unset₂' γ_lstate :=
    oneshot_pending γ_lstate (DfracOwn (2/3)) ().
  #[local] Definition lstate_unset₂ γ :=
    lstate_unset₂' γ.(metadata_lstate).
  #[local] Definition lstate_set γ :=
    oneshot_shot γ.(metadata_lstate).

  #[local] Definition consumer' γ_consumer :=
    excl γ_consumer ().
  #[local] Definition consumer γ :=
    consumer' γ.(metadata_consumer).

  #[local] Definition inv_inner l γ Ψ Χ : iProp Σ :=
    ∃ state,
    l.[contents] ↦ state ∗
    match state with
    | Unset waiters =>
        lstate_unset₁ γ ∗
        [∗ list] waiter ∈ waiters,
          ∀ v,
          lstate_set γ v -∗
          WP waiter v {{ _, True }}
    | Set_ v =>
        lstate_set γ v ∗
        (Ψ v ∗ £ 1 ∨ consumer γ) ∗
        □ Χ v
    end.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %state &
      Hl &
      Hstate
    )".
  Definition ivar_3_inv t Ψ Χ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv nroot (inv_inner l γ Ψ Χ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition ivar_3_producer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    lstate_unset₂ γ.
  #[local] Instance : CustomIpatFormat "producer" :=
    "(
      %l{=_} &
      %γ{=_} &
      %Heq{} &
      #Hmeta{=_} &
      Hlstate{}_unset₂
    )".

  Definition ivar_3_consumer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    consumer γ.
  #[local] Instance : CustomIpatFormat "consumer" :=
    "(
      %l{=_} &
      %γ{=_} &
      %Heq{} &
      #Hmeta{=_} &
      Hconsumer{}
    )".

  Definition ivar_3_result t v : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    lstate_set γ v.
  #[local] Instance : CustomIpatFormat "result" :=
    "(
      %l{=_} &
      %γ{=_} &
      %Heq{} &
      #Hmeta{=_} &
      #Hlstate{}_set
    )".
  Definition ivar_3_result' t : iProp Σ :=
    ∃ v,
    ivar_3_result t v.

  Definition ivar_3_waiter t waiter : iProp Σ :=
    ∀ v,
    £ 1 -∗
    ivar_3_result t v -∗
    WP waiter v {{ _, True }}.

  #[global] Instance ivar_3_inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_3_inv t).
  Proof.
    rewrite /ivar_3_inv /inv_inner.
    solve_contractive.
  Qed.
  #[global] Instance ivar_3_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_3_inv t).
  Proof.
    intros Ψ1 Ψ2 HΨ Χ1 Χ2 HΧ.
    apply equiv_dist => n.
    apply ivar_3_inv_contractive => v.
    all: dist_later_intro.
    all: apply equiv_dist; done.
  Qed.

  #[global] Instance ivar_3_producer_timeless t :
    Timeless (ivar_3_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_consumer_timeless t :
    Timeless (ivar_3_consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_result_timeless t v :
    Timeless (ivar_3_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_inv_persistent t Ψ Χ :
    Persistent (ivar_3_inv t Ψ Χ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_result_persistent t v :
    Persistent (ivar_3_result t v).
  Proof.
    apply _.
  Qed.

  #[local] Lemma lstate_alloc :
    ⊢ |==>
      ∃ γ_lstate,
      lstate_unset₁' γ_lstate ∗
      lstate_unset₂' γ_lstate.
  Proof.
    iMod oneshot_alloc as "(%γ_lstate & Hunset)".
    assert (1 = 1/3 + 2/3)%Qp as -> by compute_done.
    iDestruct "Hunset" as "(Hunset₁ & Hunset₂)".
    iSteps.
  Qed.
  #[local] Lemma lstate_unset₂_exclusive γ :
    lstate_unset₂ γ -∗
    lstate_unset₂ γ -∗
    False.
  Proof.
    iIntros "Hunset1 Hunset2".
    iDestruct (oneshot_pending_valid_2 with "Hunset1 Hunset2") as %(? & _). done.
  Qed.
  #[local] Lemma lstate_set_agree γ v1 v2 :
    lstate_set γ v1 -∗
    lstate_set γ v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply oneshot_shot_agree.
  Qed.
  #[local] Lemma lstate_unset₁_set γ v :
    lstate_unset₁ γ -∗
    lstate_set γ v -∗
    False.
  Proof.
    apply oneshot_pending_shot.
  Qed.
  #[local] Lemma lstate_unset₂_set γ v :
    lstate_unset₂ γ -∗
    lstate_set γ v -∗
    False.
  Proof.
    apply oneshot_pending_shot.
  Qed.
  #[local] Lemma lstate_update {γ} v :
    lstate_unset₁ γ -∗
    lstate_unset₂ γ ==∗
    lstate_set γ v.
  Proof.
    iIntros "Hunset₁ Hunset₂".
    iCombine "Hunset₁ Hunset₂" as "Hunset".
    assert (1/3 + 2/3 = 1)%Qp as -> by compute_done.
    iApply (oneshot_update_shot with "Hunset").
  Qed.

  #[local] Lemma consumer_alloc :
    ⊢ |==>
      ∃ γ_consumer,
      consumer' γ_consumer.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma consumer_exclusive γ :
    consumer γ -∗
    consumer γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  Lemma ivar_3_producer_exclusive t :
    ivar_3_producer t -∗
    ivar_3_producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (lstate_unset₂_exclusive with "Hlstate1_unset₂ Hlstate2_unset₂").
  Qed.

  Lemma ivar_3_consumer_exclusive t :
    ivar_3_consumer t -∗
    ivar_3_consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (consumer_exclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma ivar_3_result_agree t v1 v2 :
    ivar_3_result t v1 -∗
    ivar_3_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (lstate_set_agree with "Hlstate1_set Hlstate2_set").
  Qed.

  Lemma ivar_3_producer_result t v :
    ivar_3_producer t -∗
    ivar_3_result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (lstate_unset₂_set with "Hlstate1_unset₂ Hlstate2_set").
  Qed.

  Lemma ivar_3_inv_result t Ψ Χ v :
    ivar_3_inv t Ψ Χ -∗
    ivar_3_result t v ={⊤}=∗
    ▷ □ Χ v.
  Proof.
    iIntros "(:inv) (:result)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iInv "Hinv" as "(:inv_inner)".
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(>Hlstate_unset₁ & _)".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(Hlstate_set_ & HΨ & #HΧ)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as "><-".
    iSplitL. { iFrameSteps 2. }
    iSteps.
  Qed.
  Lemma ivar_3_inv_result' t Ψ Χ v :
    £ 1 -∗
    ivar_3_inv t Ψ Χ -∗
    ivar_3_result t v ={⊤}=∗
    □ Χ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (ivar_3_inv_result with "Hinv Hresult") as "HΧ".
    iApply (lc_fupd_elim_later with "H£ HΧ").
  Qed.
  Lemma ivar_3_inv_result_consumer t Ψ Χ v :
    ivar_3_inv t Ψ Χ -∗
    ivar_3_result t v -∗
    ivar_3_consumer t ={⊤}=∗
      Ψ v ∗
      ▷ □ Χ v.
  Proof.
    iIntros "(:inv) (:result)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iIntros "(:consumer)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iInv "Hinv" as "(:inv_inner)".
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(>Hlstate_unset₁ & _)".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(Hlstate_set_ & [(HΨ & >H£) | >Hconsumer_] & #HΧ)"; last first.
    { iDestruct (consumer_exclusive with "Hconsumer Hconsumer_") as %[]. }
    iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as "><-".
    iSplitR "HΨ". { iFrameSteps 2. }
    iSteps.
  Qed.
  Lemma ivar_3_inv_result_consumer' t Ψ Χ v :
    £ 1 -∗
    ivar_3_inv t Ψ Χ -∗
    ivar_3_result t v -∗
    ivar_3_consumer t ={⊤}=∗
      Ψ v ∗
      □ Χ v.
  Proof.
    iIntros "H£ Hinv Hresult Hconsumer".
    iMod (ivar_3_inv_result_consumer with "Hinv Hresult Hconsumer") as "($ & HΧ)".
    iApply (lc_fupd_elim_later with "H£ HΧ").
  Qed.

  Lemma ivar_3_create_spec Ψ Χ :
    {{{
      True
    }}}
      ivar_3_create ()
    {{{ t,
      RET t;
      ivar_3_inv t Ψ Χ ∗
      ivar_3_producer t ∗
      ivar_3_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_ref l as "Hmeta" "Hl".

    iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumer_alloc as "(%γ_consumer & Hconsumer)".

    pose γ := {|
      metadata_lstate := γ_lstate ;
      metadata_consumer := γ_consumer ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hconsumer Hlstate_unset₂"; last iFrameSteps.
    iSteps. iExists (Unset []). iSteps.
  Qed.

  Lemma ivar_3_is_set_spec t Ψ Χ :
    {{{
      ivar_3_inv t Ψ Χ
    }}}
      ivar_3_is_set t
    {{{ b,
      RET #b;
      if b then
        £ 1 ∗
        ivar_3_result' t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iSpecialize ("HΦ" $! (state_to_bool state)).
    destruct state as [waiters | v].

    - iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct "Hstate" as "(#Hlstate_set & Hstate)".
      iSplitR "H£ HΦ". { iFrameSteps 2. }
      iStep 5. iExists v. iSteps.
  Qed.
  Lemma ivar_3_is_set_spec_result t Ψ Χ v :
    {{{
      ivar_3_inv t Ψ Χ ∗
      ivar_3_result t v
    }}}
      ivar_3_is_set t
    {{{
      RET #true;
      £ 1
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(Hlstate_unset₁ & _)".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(#Hlstate_set_ & Hstate)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as %<-. iClear "Hlstate_set_".
    iSplitR "H£ HΦ". { iFrameSteps 2. }
    iSteps.
  Qed.

  Lemma ivar_3_try_get_spec t Ψ Χ :
    {{{
      ivar_3_inv t Ψ Χ
    }}}
      ivar_3_try_get t
    {{{ o,
      RET o : val;
      if o is Some v then
        £ 1 ∗
        ivar_3_result t v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iSpecialize ("HΦ" $! (state_to_option state)).
    destruct state as [waiters | v].

    - iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct "Hstate" as "(#Hlstate_set & Hstate)".
      iSplitR "H£ HΦ". { iFrameSteps 2. }
      iSteps.
  Qed.
  Lemma ivar_3_try_get_spec_result t Ψ Χ v :
    {{{
      ivar_3_inv t Ψ Χ ∗
      ivar_3_result t v
    }}}
      ivar_3_try_get t
    {{{
      RET Some v : val;
      £ 1
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(Hlstate_unset₁ & _)".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(#Hlstate_set_ & Hstate)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as %<-. iClear "Hlstate_set_".
    iSplitR "H£ HΦ". { iFrameSteps 2. }
    iSteps.
  Qed.

  Lemma ivar_3_get_spec t Ψ Χ v :
    {{{
      ivar_3_inv t Ψ Χ ∗
      ivar_3_result t v
    }}}
      ivar_3_get t
    {{{
      RET v;
      £ 1
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [waiters | v_].
    { iDestruct "Hstate" as "(Hlstate_unset₁ & _)".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(#Hlstate_set_ & Hstate)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as %<-. iClear "Hlstate_set_".
    iSplitR "H£ HΦ". { iFrameSteps 2. }
    iSteps.
  Qed.

  Lemma ivar_3_wait_spec t Ψ Χ waiter :
    {{{
      ivar_3_inv t Ψ Χ ∗
      ivar_3_waiter t waiter
    }}}
      ivar_3_wait t waiter
    {{{ o,
      RET o : val;
      if o is Some v then
        £ 1 ∗
        ivar_3_result t v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hwaiter) HΦ".
    iLöb as "HLöb".

    wp_rec credit:"H£". wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [waiters | v].

    - iSplitR "Hwaiter H£ HΦ". { iFrameSteps 2. }
      iModIntro.

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner)".
      wp_cas as Hcas.

      + iSplitR "Hwaiter HΦ". { iFrameSteps 2. }
        iModIntro.

        wp_smart_apply ("HLöb" with "Hwaiter HΦ").

      + destruct state as [waiters' | v]; zoo_simpl.
        iDestruct "Hstate" as "(Hlstate_unset₁ & Hwaiters)".
        iDestruct (big_sepL_cons_2' _ waiter with "[Hwaiter H£] Hwaiters") as "Hwaiters"; first iSteps.
        iSplitR "HΦ". { iExists (Unset (waiter :: waiters)). iFrameSteps. }
        iSpecialize ("HΦ" $! None).
        iSteps.

    - iDestruct "Hstate" as "(#Hlstate_set & Hstate)".
      iSplitR "H£ HΦ". { iFrameSteps 2. }
      iSpecialize ("HΦ" $! (Some v)).
      iSteps.
  Qed.

  Lemma ivar_3_set_spec t Ψ Χ v :
    {{{
      ivar_3_inv t Ψ Χ ∗
      ivar_3_producer t ∗
      Ψ v ∗
      □ Χ v
    }}}
      ivar_3_set t v
    {{{ waiters,
      RET lst_to_val waiters;
      ivar_3_result t v ∗
      [∗ list] waiter ∈ waiters,
        ivar_3_waiter t waiter
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΧ) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec credit:"H£". wp_pures.

    wp_bind (Xchg _ _).
    iInv "Hinv" as "(:inv_inner)".
    wp_xchg.
    destruct state; last first.
    { iDestruct "Hstate" as "(#Hlstate_set & _)".
      iDestruct (lstate_unset₂_set with "Hlstate_unset₂ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(Hlstate_unset₁ & Hwaiters)".
    iMod (lstate_update with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
    iSplitR "Hwaiters HΦ". { iExists (Set_ v). iSteps. }
    iSteps.
    iApply (big_sepL_impl with "Hwaiters"). iIntros "!> !> %k %waiter %Hlookup Hwaiter %v_ H£ (:result =1)". injection Heq1 as <-.
    iDestruct (meta_agree with "Hmeta Hmeta1") as %<-. iClear "Hmeta1".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate1_set") as %?.
    iSteps.
  Qed.
End ivar_3_G.

#[global] Opaque ivar_3_create.
#[global] Opaque ivar_3_is_set.
#[global] Opaque ivar_3_try_get.
#[global] Opaque ivar_3_get.
#[global] Opaque ivar_3_wait.
#[global] Opaque ivar_3_set.

#[global] Opaque ivar_3_inv.
#[global] Opaque ivar_3_producer.
#[global] Opaque ivar_3_consumer.
#[global] Opaque ivar_3_result.
