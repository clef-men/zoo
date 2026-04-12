From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  condition
  mutex.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Export
  base
  waiter__code.
From zoo_parabs Require Import
  base
  waiter__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types 𝑡 : location.
Implicit Types v t mtx cond : val.

Class WaiterG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] waiter_G_mutex_G :: MutexG Σ
  }.

Definition waiter_Σ := #[
  mutex_Σ
].
#[global] Instance subG_ws_hub_Σ Σ `{zoo_G : !ZooG Σ} :
  subG waiter_Σ Σ →
  WaiterG Σ.
Proof.
  solve_inG.
Qed.

Section waiter_G.
  Context `{waiter_G : WaiterG Σ}.

  #[local] Definition waiter_inv_inner 𝑡 : iProp Σ :=
    ∃ b,
    𝑡.[flag] ↦ #b.
  #[local] Instance : CustomIpat "inv_inner" :=
    " ( %b
      & H𝑡_flag
      )
    ".
  Definition waiter_inv t : iProp Σ :=
    ∃ 𝑡 mtx cond,
    ⌜t = #𝑡⌝ ∗
    𝑡.[mutex] ↦□ mtx ∗
    mutex_inv mtx True ∗
    𝑡.[condition] ↦□ cond ∗
    condition_inv cond ∗
    inv nroot (waiter_inv_inner 𝑡).
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡
      & %mtx
      & %cond
      & ->
      & #H𝑡_mutex
      & #Hmutex_inv
      & #H𝑡_condition
      & #Hcondition_inv
      & #Hinv
      )
    ".

  #[global] Instance waiter_inv_persistent t :
    Persistent (waiter_inv t).
  Proof.
    apply _.
  Qed.

  Lemma waiter_create_spec :
    {{{
      True
    }}}
      waiter_create ()
    {{{
      t
    , RET t;
      waiter_inv t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply+ (condition_create_spec with "[//]") as "%cond #Hcondition_inv".
    wp_apply+ (mutex_create_spec True with "[//]") as "%mtx #Hmutex_inv".

    iSteps.
  Qed.

  Lemma waiter_notify_spec t :
    {{{
      waiter_inv t
    }}}
      waiter_notify t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.

    wp_bind (_.{flag})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct b. 1: iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro.

    wp_load.
    wp_apply (mutex_lock_spec with "Hmutex_inv") as "(Hmutex_locked & _)".
    wp_pures.

    wp_bind (_.{flag})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    iSplitR "Hmutex_locked HΦ". { iFrameSteps. }
    iModIntro.

    destruct b; wp_pures.

    - wp_load.
      wp_apply (mutex_unlock_spec with "[$Hmutex_inv $Hmutex_locked //]") as "_".
      iSteps.

    - wp_bind (_ <-{flag} _)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_store.
      iSplitR "Hmutex_locked HΦ". { iFrameSteps. }
      iModIntro.

      wp_load.
      wp_apply (mutex_unlock_spec with "[$Hmutex_inv $Hmutex_locked //]") as "_".
      wp_load.
      wp_apply (condition_notify_spec with "Hcondition_inv").
      iSteps.
  Qed.

  Lemma waiter_prepare_wait_spec t :
    {{{
      waiter_inv t
    }}}
      waiter_prepare_wait t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma waiter_cancel_wait_spec t :
    {{{
      waiter_inv t
    }}}
      waiter_cancel_wait t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma waiter_commit_wait_spec t :
    {{{
      waiter_inv t
    }}}
      waiter_commit_wait t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.

    wp_bind (_.{flag})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct b. 1: iSteps.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro.

    wp_load.
    wp_apply+ (mutex_protect_spec (λ res,
      ⌜res = ()%V⌝
    )%I with "[$Hmutex_inv]").
    { iIntros "Hmutex_locked _".
      do 2 wp_load.
      wp_apply (condition_wait_until_spec (λ _, True)%I with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked]").
      all: iSteps.
    }
    iSteps.
  Qed.
End waiter_G.

From zoo_parabs Require
  waiter__opaque.

#[global] Opaque waiter_inv.
