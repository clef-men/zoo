From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  mpsc_waiter.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Export
  base
  waiters__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v t : val.

Class WaitersG Σ `{zoo_G : !ZooG Σ} := {
  #[local] waiters_G_queue_G :: MpmcQueue1G Σ ;
  #[local] waiters_G_waiter_G :: MpscWaiterG Σ ;
}.

Definition waiters_Σ := #[
  mpmc_queue_1_Σ ;
  mpsc_waiter_Σ
].
#[global] Instance subG_ws_hub_Σ Σ `{zoo_G : !ZooG Σ} :
  subG waiters_Σ Σ →
  WaitersG Σ.
Proof.
  solve_inG.
Qed.

Section waiters_G.
  Context `{waiters_G : WaitersG Σ}.

  #[local] Definition waiters_inv_inner t : iProp Σ :=
    ∃ waiters,
    mpmc_queue_1_model t waiters ∗
    [∗ list] waiter ∈ waiters,
      mpsc_waiter_inv waiter True.
  Definition waiters_inv t : iProp Σ :=
    mpmc_queue_1_inv t (nroot.@"queue") ∗
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
    {{{
      True
    }}}
      waiters_create ()
    {{{ t,
      RET t;
      waiters_inv t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (mpmc_queue_1_create_spec with "[//]") as (t) "(#Hqueue_inv & Hmodel)".
    iSteps.
  Qed.

  #[local] Lemma waiters_notify'_spec t :
    {{{
      waiters_inv t
    }}}
      waiters_notify' t
    {{{ b,
      RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hqueue_inv & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_apply (mpmc_queue_1_pop_spec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(%waiters & >Hmodel & Hwaiters)".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    destruct waiters as [| waiter waiters]; first iSteps.
    iDestruct "Hwaiters" as "(Hwaiter & Hwaiters)".
    iSplitR "Hwaiter"; first iSteps.
    iIntros "_ HΦ".

    wp_smart_apply (mpsc_waiter_notify_spec with "[$Hwaiter //]") as ([]) "_"; last iSteps.
    wp_smart_apply ("HLöb" with "HΦ").
  Qed.

  Lemma waiters_notify_spec t :
    {{{
      waiters_inv t
    }}}
      waiters_notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_apply (waiters_notify'_spec with "Hinv").
    iSteps.
  Qed.

  Lemma waiters_notify_many_spec t n :
    (0 ≤ n)%Z →
    {{{
      waiters_inv t
    }}}
      waiters_notify_many t #n
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hn %Φ #Hinv HΦ".

    iLöb as "HLöb" forall (n Hn).

    wp_rec. wp_pures.
    case_bool_decide; last iSteps.
    wp_smart_apply (waiters_notify'_spec with "Hinv") as ([]) "_"; last iSteps.
    wp_smart_apply ("HLöb" with "[] HΦ"); first iSteps.
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

    awp_smart_apply (mpmc_queue_1_push_spec with "Hqueue_inv") without "Hwaiter_consumer HΦ".
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
      RET ();
      True
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
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & (#Hwaiter_inv & Hwaiter_consumer)) HΦ".

    wp_rec.
    wp_smart_apply (mpsc_waiter_wait_spec with "[$Hwaiter_inv $Hwaiter_consumer] HΦ").
  Qed.
End waiters_G.

#[global] Opaque waiters_create.
#[global] Opaque waiters_notify.
#[global] Opaque waiters_notify_many.
#[global] Opaque waiters_prepare_wait.
#[global] Opaque waiters_cancel_wait.
#[global] Opaque waiters_commit_wait.

#[global] Opaque waiters_inv.
#[global] Opaque waiters_waiter.
