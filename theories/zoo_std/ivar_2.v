From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.oneshot
  lib.subpreds.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  ivar_2__code.
From zoo_std Require Import
  ivar_2__types
  option
  condition.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types t : val.
Implicit Types o state : option val.

Class Ivar2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ivar_2_G_mutex_G :: MutexG Σ ;
  #[local] ivar_2_G_lstate_G :: OneshotG Σ unit val ;
  #[local] ivar_2_G_consumer_G :: SubpredsG Σ val ;
}.

Definition ivar_2_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit val ;
  subpreds_Σ val
].
#[global] Instance subG_ivar_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ivar_2_Σ Σ →
  Ivar2G Σ .
Proof.
  solve_inG.
Qed.

Section ivar_2_G.
  Context `{ivar_2_G : Ivar2G Σ}.

  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Record metadata := {
    metadata_mutex : val ;
    metadata_condition : val ;
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

  #[local] Definition consumer_auth' :=
    subpreds_auth.
  #[local] Definition consumer_auth γ :=
    consumer_auth' γ.(metadata_consumer).
  #[local] Definition consumer_frag' :=
    subpreds_frag.
  #[local] Definition consumer_frag γ :=
    consumer_frag' γ.(metadata_consumer).

  #[local] Definition inv_inner l γ Ψ Ξ : iProp Σ :=
    ∃ state,
    l.[result] ↦ state ∗
    consumer_auth γ Ψ state ∗
    match state with
    | None =>
        lstate_unset₁ γ
    | Some v =>
        lstate_set γ v ∗
        □ Ξ v
    end.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %state &
      Hl_result &
      Hconsumer_auth &
      Hstate
    )".
  Definition ivar_2_inv t Ψ Ξ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ γ.(metadata_mutex) ∗
    mutex_inv γ.(metadata_mutex) True ∗
    l.[condition] ↦□ γ.(metadata_condition) ∗
    condition_inv γ.(metadata_condition) ∗
    inv nroot (inv_inner l γ Ψ Ξ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hl_mutex &
      #Hmutex_inv &
      #Hl_condition &
      #Hcondition_inv &
      #Hinv
    )".

  Definition ivar_2_producer t : iProp Σ :=
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

  Definition ivar_2_consumer t Χ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    consumer_frag γ Χ.
  #[local] Instance : CustomIpatFormat "consumer" :=
    "(
      %l{=_} &
      %γ{=_} &
      %Heq{} &
      #Hmeta{=_} &
      Hconsumer{}_frag
    )".

  Definition ivar_2_result t v : iProp Σ :=
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
  Definition ivar_2_result' t : iProp Σ :=
    ∃ v,
    ivar_2_result t v.

  Definition ivar_2_synchronized t : iProp Σ :=
    True.

  #[global] Instance ivar_2_inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_2_inv t).
  Proof.
    rewrite /ivar_2_inv /inv_inner.
    solve_contractive.
  Qed.
  #[global] Instance ivar_2_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_2_inv t).
  Proof.
    rewrite /ivar_2_inv /inv_inner.
    solve_proper.
  Qed.
  #[global] Instance ivar_2_consumer_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_2_consumer t).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance ivar_2_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_2_consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_2_producer_timeless t :
    Timeless (ivar_2_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_result_timeless t v :
    Timeless (ivar_2_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_synchronized_timeless t :
    Timeless (ivar_2_synchronized t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_inv_persistent t Ψ Ξ :
    Persistent (ivar_2_inv t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_result_persistent t v :
    Persistent (ivar_2_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_synchronized_persistent t :
    Persistent (ivar_2_synchronized t).
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

  #[local] Lemma consumer_alloc Ψ :
    ⊢ |==>
      ∃ γ_consumer,
      consumer_auth' γ_consumer Ψ None ∗
      consumer_frag' γ_consumer Ψ.
  Proof.
    apply subpreds_alloc.
  Qed.
  #[local] Lemma consumer_divide {γ Ψ state Χ} Χs E :
    ▷ consumer_auth γ Ψ state -∗
    consumer_frag γ Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={E}=∗
      ▷ consumer_auth γ Ψ state ∗
      [∗ list] Χ ∈ Χs, consumer_frag γ Χ.
  Proof.
    apply subpreds_divide.
  Qed.
  #[local] Lemma consumer_produce {γ Ψ} v :
    consumer_auth γ Ψ None -∗
    Ψ v -∗
    consumer_auth γ Ψ (Some v).
  Proof.
    apply subpreds_produce.
  Qed.
  #[local] Lemma consumer_consume γ Ψ v Χ E :
    ▷ consumer_auth γ Ψ (Some v) -∗
    consumer_frag γ Χ ={E}=∗
      ▷ consumer_auth γ Ψ (Some v) ∗
      ▷^2 Χ v.
  Proof.
    apply subpreds_consume.
  Qed.

  Lemma ivar_2_producer_exclusive t :
    ivar_2_producer t -∗
    ivar_2_producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (lstate_unset₂_exclusive with "Hlstate1_unset₂ Hlstate2_unset₂").
  Qed.

  Lemma ivar_2_consumer_divide {t Ψ Ξ Χ} Χs :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_consumer t Χ -∗
    (∀ x, Χ x -∗ [∗ list] Χ ∈ Χs, Χ x) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_2_consumer t Χ.
  Proof.
    iIntros "(:inv) (:consumer) H". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iInv "Hinv" as "(:inv_inner)".
    iMod (consumer_divide with "Hconsumer_auth Hconsumer_frag H") as "(Hconsumer_auth & H)".
    iSplitR "H". { iFrameSteps. }
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma ivar_2_consumer_split {t Ψ Χ Ξ} Χ1 Χ2 :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_consumer t Χ -∗
    (∀ v, Χ v -∗ Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_2_consumer t Χ1 ∗
      ivar_2_consumer t Χ2.
  Proof.
    iIntros "#Hinv Hconsumer H".
    iMod (ivar_2_consumer_divide [Χ1;Χ2] with "Hinv Hconsumer [H]") as "($ & $ & _)"; iSteps.
  Qed.

  Lemma ivar_2_result_agree t v1 v2 :
    ivar_2_result t v1 -∗
    ivar_2_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (lstate_set_agree with "Hlstate1_set Hlstate2_set").
  Qed.

  Lemma ivar_2_producer_result t v :
    ivar_2_producer t -∗
    ivar_2_result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iApply (lstate_unset₂_set with "Hlstate1_unset₂ Hlstate2_set").
  Qed.

  Lemma ivar_2_inv_result t Ψ Ξ v :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result) _". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iInv "Hinv" as "(:inv_inner)".
    destruct state as [v_ |]; last first.
    { iDestruct "Hstate" as ">Hlstate_unset₁".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(Hlstate_set_ & #HΞ)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as "><-".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma ivar_2_inv_result' t Ψ Ξ v :
    £ 1 -∗
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult Hsynchronized".
    iMod (ivar_2_inv_result with "Hinv Hresult Hsynchronized") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_2_inv_result_consumer t Ψ Ξ v Χ :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t -∗
    ivar_2_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv) (:result) _". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iIntros "(:consumer)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iInv "Hinv" as "(:inv_inner)".
    destruct state as [v_ |]; last first.
    { iDestruct "Hstate" as ">Hlstate_unset₁".
      iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
    }
    iDestruct "Hstate" as "(Hlstate_set_ & #HΞ)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as "><-".
    iMod (consumer_consume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
    iSplitR "HΧ". { iFrameSteps. }
    iSteps.
  Qed.
  Lemma ivar_2_inv_result_consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t -∗
    ivar_2_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hsynchronized Hconsumer".
    iMod (ivar_2_inv_result_consumer with "Hinv Hresult Hsynchronized Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_2_create_spec Ψ Ξ :
    {{{
      True
    }}}
      ivar_2_create ()
    {{{ t,
      RET t;
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_producer t ∗
      ivar_2_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcondition_inv".
    wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmutex_inv".
    wp_block l as "Hmeta" "(Hl_result & Hl_mutex & Hl_condition & _)".
    iMod (pointsto_persist with "Hl_mutex") as "Hl_mutex".
    iMod (pointsto_persist with "Hl_condition") as "Hl_condition".

    iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
    iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

    pose γ := {|
      metadata_mutex := mtx ;
      metadata_condition := cond ;
      metadata_lstate := γ_lstate ;
      metadata_consumer := γ_consumer ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hconsumer_frag Hlstate_unset₂"; last iFrameSteps.
    iSteps. iExists None. iSteps.
  Qed.

  Lemma ivar_2_try_get_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_try_get t
    {{{ o,
      RET o : val;
      if o is Some v then
        £ 2 ∗
        ivar_2_result t v ∗
        ivar_2_synchronized t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec credits:"H£".
    iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iSpecialize ("HΦ" $! state).
    destruct state as [v |].

    - iDestruct "Hstate" as "(#Hlstate_set & Hstate)".
      iSplitR "H£ HΦ". { iFrameSteps 2. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.
  Qed.
  Lemma ivar_2_try_get_spec_result t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v
    }}}
      ivar_2_try_get t
    {{{
      RET Some v : val;
      £ 2 ∗
      ivar_2_synchronized t
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:result)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec credits:"H£".
    iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [v_ |]; last first.
    { iDestruct (lstate_unset₁_set with "Hstate Hlstate_set") as %[]. }
    iDestruct "Hstate" as "(#Hlstate_set_ & Hstate)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as %<-. iClear "Hlstate_set_".
    iSplitR "H£ HΦ". { iFrameSteps 2. }
    iSteps.
  Qed.

  Lemma ivar_2_is_set_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_is_set t
    {{{ b,
      RET #b;
      if b then
        £ 2 ∗
        ivar_2_result' t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_apply (ivar_2_try_get_spec with "Hinv") as ([v |]) "H".
    all: wp_pures.
    2: iSteps.
    iDestruct "H" as "(H£ & Hresult & Hsynchronized)".
    iApply "HΦ". iFrameSteps.
  Qed.
  Lemma ivar_2_is_set_spec_result t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v
    }}}
      ivar_2_is_set t
    {{{
      RET #true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresult) HΦ".

    wp_rec.
    wp_apply (ivar_2_try_get_spec_result with "[$Hinv $Hresult]").
    iSteps.
  Qed.

  Lemma ivar_2_get_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_get t
    {{{ v,
      RET v;
      £ 2 ∗
      ivar_2_result t v ∗
      ivar_2_synchronized t
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec credits:"H£".
    iDestruct (lc_weaken 2 with "H£") as "H£"; first done.
    wp_apply (ivar_2_try_get_spec with "Hinv") as (state) "H".
    iDestruct "Hinv" as "(:inv)".
    destruct state; first iStepFrameSteps 13.
    do 2 wp_load.

    pose Ψ_mutex (_ : val) := (
      ∃ v,
      lstate_set γ v
    )%I.
    wp_smart_apply (mutex_protect_spec Ψ_mutex with "[$Hmutex_inv]") as (res) "(%v & #Hlstate_set)".
    { iIntros "Hmutex_locked _".
      pose (Ψ_condition b := (
        if b then
          True
        else
          ∃ v,
          lstate_set γ v
      )%I).
      wp_smart_apply (condition_wait_while_spec Ψ_condition with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked]") as "(Hmutex_locked & _ & Hlstate_set)"; last iFrameSteps.
      iStep. iIntros "{%} !> %Φ (Hmutex_locked & _ & _) HΦ".
      wp_pures.

      wp_bind (_.{result})%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [v |].

      - iDestruct "Hstate" as "(#Hlstate_set & Hstate)".
        iSplitR "Hmutex_locked HΦ". { iFrameSteps 2. }
        iSteps.

      - iSplitR "Hmutex_locked HΦ". { iFrameSteps 2. }
        iSteps.
    }
    wp_pures.

    wp_bind (_.{result})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [v_ |]; last first.
    { iDestruct (lstate_unset₁_set with "Hstate Hlstate_set") as %[]. }
    iDestruct "Hstate" as "(Hlstate_set_ & Hstate)".
    iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_") as %<-. iClear "Hlstate_set_".
    iSplitR "H£ HΦ". { iFrameSteps 2. }
    iSteps.
  Qed.
  Lemma ivar_2_get_spec_result t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v
    }}}
      ivar_2_get t
    {{{
      RET v;
      £ 2 ∗
      ivar_2_synchronized t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresult) HΦ".

    wp_apply (ivar_2_get_spec with "Hinv") as (v_) "(H£ & Hresult_ & Hsynchronized)".
    iDestruct (ivar_2_result_agree with "Hresult Hresult_")as %<-.
    iSteps.
  Qed.

  Lemma ivar_2_set_spec t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_producer t ∗
      Ψ v ∗
      □ Ξ v
    }}}
      ivar_2_set t v
    {{{
      RET ();
      ivar_2_result t v
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    pose Ψ_mutex (_ : val) :=
      lstate_set γ v.
    wp_apply (mutex_protect_spec Ψ_mutex with "[$Hmutex_inv Hlstate_unset₂ HΨ]") as (res) "#Hlstate_set"; last iSteps.
    iIntros "Hmutex_locked _".
    wp_pures.

    iInv "Hinv" as "(:inv_inner)".
    wp_store.
    destruct state.
    { iDestruct "Hstate" as "(#Hlstate_set & _)".
      iDestruct (lstate_unset₂_set with "Hlstate_unset₂ Hlstate_set") as %[].
    }
    iMod (lstate_update with "Hstate Hlstate_unset₂") as "#Hlstate_set".
    iDestruct (consumer_produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
    iSplitR "Hmutex_locked". { iExists (Some v). iSteps. }
    iSteps.
  Qed.
End ivar_2_G.

#[global] Opaque ivar_2_create.
#[global] Opaque ivar_2_is_set.
#[global] Opaque ivar_2_try_get.
#[global] Opaque ivar_2_get.
#[global] Opaque ivar_2_set.

#[global] Opaque ivar_2_inv.
#[global] Opaque ivar_2_producer.
#[global] Opaque ivar_2_consumer.
#[global] Opaque ivar_2_result.
#[global] Opaque ivar_2_synchronized.
