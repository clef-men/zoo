From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.oneshot
  lib.excl.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  spsc_waiter__code.
From zoo_std Require Import
  condition
  spsc_waiter__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.

Class SpscWaiterG Σ `{zoo_G : !ZooG Σ} := {
  #[local] spsc_waiter_G_mutex_G :: MutexG Σ ;
  #[local] spsc_waiter_G_lstate_G :: OneshotG Σ unit unit ;
  #[local] spsc_waiter_G_excl_G :: ExclG Σ unitO ;
}.

Definition spsc_waiter_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit unit ;
  excl_Σ unitO
].
#[global] Instance subG_spsc_waiter_Σ Σ `{zoo_G : !ZooG Σ} :
  subG spsc_waiter_Σ Σ →
  SpscWaiterG Σ .
Proof.
  solve_inG.
Qed.

Section spsc_waiter_G.
  Context `{spsc_waiter_G : SpscWaiterG Σ}.

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

  #[local] Definition inv_inner l γ P : iProp Σ :=
    ∃ b,
    l.[flag] ↦ #b ∗
    if b then
      oneshot_shot γ.(metadata_lstate) () ∗
      (P ∨ excl γ.(metadata_consumer) ())
    else
      oneshot_pending γ.(metadata_lstate) (DfracOwn (1/3)) ().
  Definition spsc_waiter_inv t P : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ γ.(metadata_mutex) ∗
    mutex_inv γ.(metadata_mutex) True ∗
    l.[condition] ↦□ γ.(metadata_condition) ∗
    condition_inv γ.(metadata_condition) ∗
    inv nroot (inv_inner l γ P).

  Definition spsc_waiter_producer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_pending γ.(metadata_lstate) (DfracOwn (2/3)) ().

  Definition spsc_waiter_consumer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    excl γ.(metadata_consumer) ().

  Definition spsc_waiter_notified t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_shot γ.(metadata_lstate) ().

  #[global] Instance spsc_waiter_inv_contractive t :
    Contractive (spsc_waiter_inv t).
  Proof.
    rewrite /spsc_waiter_inv /inv_inner. solve_contractive.
  Qed.
  #[global] Instance spsc_waiter_inv_ne t :
    NonExpansive (spsc_waiter_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter_inv_proper t :
    Proper ((≡) ==> (≡)) (spsc_waiter_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_waiter_inv_persistent t P :
    Persistent (spsc_waiter_inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter_notified_persistent t :
    Persistent (spsc_waiter_notified t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter_producer_timeless t :
    Timeless (spsc_waiter_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter_consumer_timeless t :
    Timeless (spsc_waiter_consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter_notified_timeless t :
    Timeless (spsc_waiter_notified t).
  Proof.
    apply _.
  Qed.

  Lemma spsc_waiter_producer_exclusive t :
    spsc_waiter_producer t -∗
    spsc_waiter_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hpending1) (%_l & %_γ & %Heq & _Hmeta & Hpending2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (oneshot_pending_valid_2 with "Hpending1 Hpending2") as %(? & _). done.
  Qed.

  Lemma spsc_waiter_consumer_exclusive t :
    spsc_waiter_consumer t -∗
    spsc_waiter_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hconsumer1) (%_l & %_γ & %Heq & _Hmeta & Hconsumer2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (excl_exclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma spsc_waiter_create_spec P :
    {{{
      True
    }}}
      spsc_waiter_create ()
    {{{ t,
      RET t;
      spsc_waiter_inv t P ∗
      spsc_waiter_producer t ∗
      spsc_waiter_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcond_inv".
    wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmtx_inv".
    wp_block l as "Hmeta" "(Hflag & Hmtx & Hcond & _)".
    iMod (pointsto_persist with "Hmtx") as "Hmtx".
    iMod (pointsto_persist with "Hcond") as "Hcond".

    iMod (oneshot_alloc ()) as "(%γ_lstate & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (excl_alloc (excl_G := spsc_waiter_G_excl_G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ := {|
      metadata_mutex := mtx ;
      metadata_condition := cond ;
      metadata_lstate := γ_lstate ;
      metadata_consumer := γ_consumer ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.

  Lemma spsc_waiter_notify_spec t P :
    {{{
      spsc_waiter_inv t P ∗
      spsc_waiter_producer t ∗
      P
    }}}
      spsc_waiter_notify t
    {{{
      RET ();
      spsc_waiter_notified t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hpending) & HP) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.
    pose (Ψ_mtx (_ : val) := (
      oneshot_shot γ.(metadata_lstate)  ()
    )%I).
    wp_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv Hpending HP]") as (res) "#Hshot".
    { iIntros "Hmtx_locked _".
      wp_pures.
      wp_bind (_ <- _)%E.
      iInv "Hinv" as "(%b & Hflag & Hb)".
      wp_store.
      destruct b.
      { iDestruct "Hb" as "(Hshot & _)".
        iDestruct (oneshot_pending_shot with "Hpending Hshot") as %[].
      }
      iCombine "Hpending Hb" as "Hpending".
      assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
      iMod (oneshot_update_shot with "Hpending") as "#Hshot".
      iSteps.
    }
    wp_load.
    wp_apply (condition_notify_spec with "Hcond_inv").
    iSteps.
  Qed.

  Lemma spsc_waiter_try_wait_spec t P :
    {{{
      spsc_waiter_inv t P ∗
      spsc_waiter_consumer t
    }}}
      spsc_waiter_try_wait t
    {{{ b,
      RET #b;
      if b then
        P
      else
        spsc_waiter_consumer t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hconsumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
  Lemma spsc_waiter_try_wait_spec_notified t P :
    {{{
      spsc_waiter_inv t P ∗
      spsc_waiter_consumer t ∗
      spsc_waiter_notified t
    }}}
      spsc_waiter_try_wait t
    {{{
      RET #true;
      P
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l1 & %_γ1 & %Heq1 & _Hmeta1 & Hconsumer) & (%_l2 & %_γ2 & %Heq2 & _Hmeta2 & #Hshot)) HΦ". injection Heq1 as <-. injection Heq2 as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta1") as %<-. iClear "_Hmeta1".
    iDestruct (meta_agree with "Hmeta _Hmeta2") as %<-. iClear "_Hmeta2".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; last first.
    { iDestruct (oneshot_pending_shot with "Hb Hshot") as %[]. }
    iDestruct "Hb" as "(_ & [HP | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.

  Lemma spsc_waiter_wait_spec t P :
    {{{
      spsc_waiter_inv t P ∗
      spsc_waiter_consumer t
    }}}
      spsc_waiter_wait t
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp_rec.
    wp_apply (spsc_waiter_try_wait_spec with "[$Hinv $Hconsumer]") as ([]) "Hconsumer"; first iSteps.

    iDestruct "Hinv" as "(%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv)".
    iDestruct "Hconsumer" as "(%_l & %_γ & %Heq & _Hmeta & Hconsumer)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    do 2 wp_load.
    pose Ψ_mtx res := (
      ⌜res = ()%V⌝ ∗
      P
    )%I.
    wp_smart_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv Hconsumer]"); last iSteps.
    iIntros "Hmtx_locked _".
    pose (Ψ_cond b := (
      if b then
        P
      else
        excl γ.(metadata_consumer) ()
    )%I).
    wp_smart_apply (condition_wait_until_spec Ψ_cond with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $Hconsumer]"); last iSteps.

    clear. iIntros "!> %Φ (Hmtx_locked & _ & Hconsumer) HΦ".
    wp_pures.

    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
End spsc_waiter_G.

#[global] Opaque spsc_waiter_create.
#[global] Opaque spsc_waiter_notify.
#[global] Opaque spsc_waiter_try_wait.
#[global] Opaque spsc_waiter_wait.

#[global] Opaque spsc_waiter_inv.
#[global] Opaque spsc_waiter_producer.
#[global] Opaque spsc_waiter_consumer.
#[global] Opaque spsc_waiter_notified.
