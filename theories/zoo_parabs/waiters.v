From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  array.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Export
  base
  waiters__code.
From zoo_parabs Require Import
  waiter
  waiters__types.
From zoo Require Import
  options.

Implicit Types v t waiters queue : val.
Implicit Types 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 𝑞𝑢𝑒𝑢𝑒 : list val.

Class WaitersG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] waiters_G_queue_G :: MpmcQueue1G Σ
  ; #[local] waiters_G_waiter_G :: WaiterG Σ
  }.

Definition waiters_Σ := #[
  mpmc_queue_1_Σ ;
  waiter_Σ
].
#[global] Instance subG_ws_hub_Σ Σ `{zoo_G : !ZooG Σ} :
  subG waiters_Σ Σ →
  WaitersG Σ.
Proof.
  solve_inG.
Qed.

Section waiters_G.
  Context `{waiters_G : WaitersG Σ}.

  #[local] Definition waiters_inv_inner queue : iProp Σ :=
    ∃ 𝑞𝑢𝑒𝑢𝑒,
    mpmc_queue_1_model queue 𝑞𝑢𝑒𝑢𝑒 ∗
    [∗ list] 𝑤𝑎𝑖𝑡𝑒𝑟 ∈ 𝑞𝑢𝑒𝑢𝑒,
      waiter_inv 𝑤𝑎𝑖𝑡𝑒𝑟.
  #[local] Instance : CustomIpat "inv_inner" :=
    " ( %𝑞𝑢𝑒𝑢𝑒
      & >Hqueue_model
      & H𝑞𝑢𝑒𝑢𝑒
      )
    ".
  Definition waiters_inv t sz : iProp Σ :=
    ∃ waiters 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 queue,
    ⌜t = (waiters, queue)%V⌝ ∗
    array_model waiters Discard 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ∗
    ⌜length 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 = sz⌝ ∗
    ([∗ list] 𝑤𝑎𝑖𝑡𝑒𝑟 ∈ 𝑤𝑎𝑖𝑡𝑒𝑟𝑠, waiter_inv 𝑤𝑎𝑖𝑡𝑒𝑟) ∗
    mpmc_queue_1_inv queue (nroot.@"queue") ∗
    inv (nroot.@"inv") (waiters_inv_inner queue).
  #[local] Instance : CustomIpat "inv" :=
    " ( %waiters
      & %𝑤𝑎𝑖𝑡𝑒𝑟𝑠
      & %queue
      & ->
      & #Hwaiters
      & %H𝑤𝑎𝑖𝑡𝑒𝑟s
      & #H𝑤𝑎𝑖𝑡𝑒𝑟𝑠
      & #Hqueue_inv
      & #Hinv
      )
    ".

  #[global] Instance waiters_inv_persistent t sz :
    Persistent (waiters_inv t sz).
  Proof.
    apply _.
  Qed.

  Lemma waiters_create𑁒spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      waiters_create #sz
    {{{
      t
    , RET t;
      waiters_inv t ₊sz
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_apply (mpmc_queue_1_create𑁒spec with "[//]") as (t) "(#Hqueue_inv & Hmodel)".

    wp_apply (array_unsafe_init𑁒spec_disentangled (λ _ 𝑤𝑎𝑖𝑡𝑒𝑟,
      waiter_inv 𝑤𝑎𝑖𝑡𝑒𝑟
    )%I) as (waiters 𝑤𝑎𝑖𝑡𝑒𝑟𝑠) "(%H𝑤𝑎𝑖𝑡𝑒𝑟𝑠 & Hwaiters & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠)". 1: done.
    { iIntros "!> %i %Hi".
      wp_apply (waiter_create𑁒spec with "[//]").
      iSteps.
    }
    iMod (array_model_persist with "Hwaiters") as "#Hwaiters".

    iSteps.
  Qed.

  Lemma waiters_notify𑁒spec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters_inv t sz
    }}}
      waiters_notify t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp_rec.
    wp_apply+ (array_unsafe_get𑁒spec with "Hwaiters") as "_". 1-3: done || lia.
    wp_apply+ (waiter_notify_strong𑁒spec with "H𝑤𝑎𝑖𝑡𝑒𝑟 HΦ").
  Qed.

  Lemma waiters_notify_one𑁒spec t sz :
    {{{
      waiters_inv t sz
    }}}
      waiters_notify_one t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_apply+ (mpmc_queue_1_pop𑁒spec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model !>".
    destruct 𝑞𝑢𝑒𝑢𝑒 as [| 𝑤𝑎𝑖𝑡𝑒𝑟 𝑞𝑢𝑒𝑢𝑒]. 1: iSteps.
    iDestruct "H𝑞𝑢𝑒𝑢𝑒" as "(H𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑞𝑢𝑒𝑢𝑒)".
    iSplitR "H𝑤𝑎𝑖𝑡𝑒𝑟". { iFrame. }
    iIntros "_ HΦ".

    wp_apply+ (waiter_notify𑁒spec with "H𝑤𝑎𝑖𝑡𝑒𝑟") as ([]) "_". 1: iSteps.
    wp_apply+ ("HLöb" with "HΦ").
  Qed.

  Lemma waiters_notify_all𑁒spec t sz :
    {{{
      waiters_inv t sz
    }}}
      waiters_notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_apply+ (mpmc_queue_1_pop𑁒spec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model !>".
    destruct 𝑞𝑢𝑒𝑢𝑒 as [| 𝑤𝑎𝑖𝑡𝑒𝑟 𝑞𝑢𝑒𝑢𝑒]. 1: iSteps.
    iDestruct "H𝑞𝑢𝑒𝑢𝑒" as "(H𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑞𝑢𝑒𝑢𝑒)".
    iSplitR "H𝑤𝑎𝑖𝑡𝑒𝑟". { iFrame. }
    iIntros "_ HΦ".

    wp_apply+ (waiter_notify𑁒spec with "H𝑤𝑎𝑖𝑡𝑒𝑟") as (res) "_".
    wp_apply+ ("HLöb" with "HΦ").
  Qed.

  Lemma waiters_prepare_wait𑁒spec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters_inv t sz
    }}}
      waiters_prepare_wait t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp_rec.
    wp_apply+ (array_unsafe_get𑁒spec with "Hwaiters") as "_". 1-3: done || lia.
    wp_apply+ (waiter_prepare_wait𑁒spec with "H𝑤𝑎𝑖𝑡𝑒𝑟") as "_".

    awp_apply+ (mpmc_queue_1_push𑁒spec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(:inv_inner)".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model !>".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.

  Lemma waiters_cancel_wait𑁒spec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters_inv t sz
    }}}
      waiters_cancel_wait t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp_rec.
    wp_apply+ (array_unsafe_get𑁒spec with "Hwaiters") as "_". 1-3: done || lia.
    wp_apply+ (waiter_cancel_wait𑁒spec with "H𝑤𝑎𝑖𝑡𝑒𝑟 HΦ").
  Qed.

  Lemma waiters_commit_wait𑁒spec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters_inv t sz
    }}}
      waiters_commit_wait t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp_rec.
    wp_apply+ (array_unsafe_get𑁒spec with "Hwaiters") as "_". 1-3: done || lia.
    wp_apply+ (waiter_commit_wait𑁒spec with "H𝑤𝑎𝑖𝑡𝑒𝑟 HΦ").
  Qed.
End waiters_G.

From zoo_parabs Require
  waiters__opaque.

#[global] Opaque waiters_inv.
