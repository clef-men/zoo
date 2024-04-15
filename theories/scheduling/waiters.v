From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  mpsc_waiter.
From zebre.saturn Require Import
  mpmc_queue_1.
From zebre.scheduling Require Export
  base.
From zebre Require Import
  options.

Implicit Types v t : val.

Definition waiters_create : val :=
  mpmc_queue_create.

Definition waiters_notify : val :=
  rec: "waiters_notify" "t" :=
    match: mpmc_queue_pop "t" with
    | None =>
        ()
    | Some "waiter" =>
        if: mpsc_waiter_notify "waiter" then
          "waiters_notify" "t"
    end.

Definition waiters_prepare_wait : val :=
  λ: "t",
    let: "waiter" := mpsc_waiter_create () in
    mpmc_queue_push "t" "waiter" ;;
    "waiter".

Definition waiters_cancel_wait : val :=
  λ: "t" "waiter",
    if: mpsc_waiter_notify "waiter" then
      waiters_notify "t".

Definition waiters_commit_wait : val :=
  λ: "t" "waiter",
    mpsc_waiter_wait "waiter".

Class WaitersG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] waiters_G_queue_G :: MpmcQueueG Σ ;
  #[local] waiters_G_waiter_G :: MpscWaiterG Σ ;
}.

Definition waiters_Σ := #[
  mpmc_queue_Σ ;
  mpsc_waiter_Σ
].
#[global] Instance subG_ws_hub_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG waiters_Σ Σ →
  WaitersG Σ.
Proof.
  solve_inG.
Qed.

Section waiters_G.
  Context `{waiters_G : WaitersG Σ}.

  #[local] Definition waiters_inv_inner t : iProp Σ :=
    ∃ waiters,
    mpmc_queue_model t waiters ∗
    [∗ list] waiter ∈ waiters,
      mpsc_waiter_inv waiter True.
  Definition waiters_inv t : iProp Σ :=
    mpmc_queue_inv t (nroot.@"queue") ∗
    inv (nroot.@"inv") (waiters_inv_inner t).

  Definition waiters_waiter t waiter : iProp Σ :=
    mpsc_waiter_inv waiter True ∗
    mpsc_waiter_consumer waiter.

  #[global] Instance waiters_inv_persistent t :
    Persistent (waiters_inv t).
  Proof.
    apply _.
  Qed.

  Lemma waiters_waiter_exclusive t1 t2 waiter :
    waiters_waiter t1 waiter -∗
    waiters_waiter t2 waiter -∗
    False.
  Proof.
    iIntros "(_ & Hwaiter_consumer1) (_ & Hwaiter_consumer2)".
    iApply (mpsc_waiter_consumer_exclusive with "Hwaiter_consumer1 Hwaiter_consumer2").
  Qed.

  Lemma waiters_create_spec :
    {{{ True }}}
      waiters_create ()
    {{{ t,
      RET t;
      waiters_inv t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (mpmc_queue_create_spec with "[//]") as (t) "(#Hqueue_inv & Hmodel)".
    iSteps.
  Qed.

  Lemma waiters_notify_spec t :
    {{{
      waiters_inv t
    }}}
      waiters_notify t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Hqueue_inv & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_apply (mpmc_queue_pop_spec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(%waiters & >Hmodel & Hwaiters)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    destruct waiters as [| waiter waiters]; first iSteps.
    iDestruct "Hwaiters" as "(Hwaiter & Hwaiters)".
    iSplitR "Hwaiter"; first iSteps.
    iIntros "_ HΦ".

    wp_smart_apply (mpsc_waiter_notify_spec with "[$Hwaiter //]") as ([]) "_"; last iSteps.
    wp_smart_apply ("HLöb" with "HΦ").
  Qed.

  Lemma waiters_prepare_wait_spec t :
    {{{
      waiters_inv t
    }}}
      waiters_prepare_wait t
    {{{ waiter,
      RET waiter;
      waiters_waiter t waiter
    }}}.
  Proof.
    iIntros "%Φ (#Hqueue_inv & #Hinv) HΦ".

    wp_rec.
    wp_apply (mpsc_waiter_create_spec with "[//]") as (waiter) "(#Hwaiter_inv & Hwaiter_consumer)".

    awp_smart_apply (mpmc_queue_push_spec with "Hqueue_inv") without "Hwaiter_consumer HΦ".
    iInv "Hinv" as "(%waiters & >Hmodel & Hwaiters)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iSplitL. { iSteps. iApply big_sepL_snoc. iSteps. }
    iSteps.
  Qed.

  Lemma waiters_cancel_wait_spec t waiter :
    {{{
      waiters_inv t ∗
      waiters_waiter t waiter
    }}}
      waiters_cancel_wait t waiter
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & (#Hwaiter_inv & Hwaiter_consumer)) HΦ".

    wp_rec.
    wp_smart_apply (mpsc_waiter_notify_spec with "[$Hwaiter_inv //]") as ([]) "_"; last iSteps.
    wp_smart_apply (waiters_notify_spec with "Hinv HΦ").
  Qed.

  Lemma waiters_commit_wait_spec t waiter :
    {{{
      waiters_inv t ∗
      waiters_waiter t waiter
    }}}
      waiters_commit_wait t waiter
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & (#Hwaiter_inv & Hwaiter_consumer)) HΦ".

    wp_rec.
    wp_smart_apply (mpsc_waiter_wait_spec with "[$Hwaiter_inv $Hwaiter_consumer] HΦ").
  Qed.
End waiters_G.

#[global] Opaque waiters_create.
#[global] Opaque waiters_notify.
#[global] Opaque waiters_prepare_wait.
#[global] Opaque waiters_cancel_wait.
#[global] Opaque waiters_commit_wait.

#[global] Opaque waiters_inv.
#[global] Opaque waiters_waiter.
