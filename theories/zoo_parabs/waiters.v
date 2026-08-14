Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_parabs.base.
Require Export zoo_parabs.waiters__code.
Require Import zoo_parabs.waiters__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v t waiters queue : val.
Implicit Type 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 𝑞𝑢𝑒𝑢𝑒 : list val.

Class WaitersG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] waiters۰G۰queue۰G :: QueueMpmc1G Σ
  ; #[local] waiters۰G۰waiter۰G :: WaiterG Σ
  }.

Definition waiters۰Σ :=
  #[queue_mpmc_1۰Σ
  ; waiter۰Σ
  ].
#[global] Instance subGｰws_hub_Σ Σ `{zoo۰G : !ZooG Σ} :
  subG waiters۰Σ Σ →
  WaitersG Σ.
Proof.
  solve_inG.
Qed.

Section waiters۰G.
  Context `{waiters۰G : WaitersG Σ}.

  #[local] Definition waiters۰inv۰inner queue : iProp Σ :=
    ∃ 𝑞𝑢𝑒𝑢𝑒,
    queue_mpmc_1۰model queue 𝑞𝑢𝑒𝑢𝑒 ∗
    [∗ list] 𝑤𝑎𝑖𝑡𝑒𝑟 ∈ 𝑞𝑢𝑒𝑢𝑒,
      waiter۰inv 𝑤𝑎𝑖𝑡𝑒𝑟.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %𝑞𝑢𝑒𝑢𝑒
      & >Hqueue_model
      & H𝑞𝑢𝑒𝑢𝑒
      )
    ".
  Definition waiters۰inv t sz : iProp Σ :=
    ∃ waiters 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 queue,
    ⌜t = (waiters, queue)%V⌝ ∗
    array۰model waiters Discard 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ∗
    ⌜length 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 = sz⌝ ∗
    ([∗ list] 𝑤𝑎𝑖𝑡𝑒𝑟 ∈ 𝑤𝑎𝑖𝑡𝑒𝑟𝑠, waiter۰inv 𝑤𝑎𝑖𝑡𝑒𝑟) ∗
    queue_mpmc_1۰inv queue (nroot.@"queue") ∗
    inv (nroot.@"inv") (waiters۰inv۰inner queue).
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

  #[global] Instance waiters۰invｰpersistent t sz :
    Persistent (waiters۰inv t sz).
  Proof.
    apply _.
  Qed.

  Lemma waiters٠createｰspec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      waiters٠create #sz
    {{{
      t
    , RET t;
      waiters۰inv t ₊sz
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.
    wp۰apply (queue_mpmc_1٠createｰspec with "[//]") as (t) "(#Hqueue_inv & Hmodel)".

    wp۰apply (array٠unsafe_initｰspecｰdisentangled (λ _ 𝑤𝑎𝑖𝑡𝑒𝑟,
      waiter۰inv 𝑤𝑎𝑖𝑡𝑒𝑟
    )%I) as (waiters 𝑤𝑎𝑖𝑡𝑒𝑟𝑠) "(%H𝑤𝑎𝑖𝑡𝑒𝑟𝑠 & Hwaiters & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠)". 1: done.
    { iIntros "!> %i %Hi".
      wp۰apply (waiter٠createｰspec with "[//]").
      iSteps.
    }
    iMod (array۰modelｰpersist with "Hwaiters") as "#Hwaiters".

    iSteps.
  Qed.

  Lemma waiters٠notifyｰspec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters۰inv t sz
    }}}
      waiters٠notify t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspec with "Hwaiters") as "_". 1-3: done || lia.
    wp۰apply+ (waiter٠notifyｰspec with "H𝑤𝑎𝑖𝑡𝑒𝑟").
    iSteps.
  Qed.

  Lemma waiters٠notify_oneｰspec t sz :
    {{{
      waiters۰inv t sz
    }}}
      waiters٠notify_one t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec.

    awp۰apply+ (queue_mpmc_1٠popｰspec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(:inv۰inner)".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model !>".
    destruct 𝑞𝑢𝑒𝑢𝑒 as [| 𝑤𝑎𝑖𝑡𝑒𝑟 𝑞𝑢𝑒𝑢𝑒]. 1: iSteps.
    iDestruct "H𝑞𝑢𝑒𝑢𝑒" as "(H𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑞𝑢𝑒𝑢𝑒)".
    iSplitR "H𝑤𝑎𝑖𝑡𝑒𝑟". { iFrame. }
    iIntros "_ HΦ".

    wp۰apply+ (waiter٠notifyｰspec with "H𝑤𝑎𝑖𝑡𝑒𝑟") as ([]) "_". 1: iSteps.
    wp۰apply+ ("HLöb" with "HΦ").
  Qed.

  Lemma waiters٠notify_allｰspec t sz :
    {{{
      waiters۰inv t sz
    }}}
      waiters٠notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec.

    awp۰apply+ (queue_mpmc_1٠popｰspec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(:inv۰inner)".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model !>".
    destruct 𝑞𝑢𝑒𝑢𝑒 as [| 𝑤𝑎𝑖𝑡𝑒𝑟 𝑞𝑢𝑒𝑢𝑒]. 1: iSteps.
    iDestruct "H𝑞𝑢𝑒𝑢𝑒" as "(H𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑞𝑢𝑒𝑢𝑒)".
    iSplitR "H𝑤𝑎𝑖𝑡𝑒𝑟". { iFrame. }
    iIntros "_ HΦ".

    wp۰apply+ (waiter٠notifyｰspec with "H𝑤𝑎𝑖𝑡𝑒𝑟") as (res) "_".
    wp۰apply+ ("HLöb" with "HΦ").
  Qed.

  Lemma waiters٠prepare_waitｰspec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters۰inv t sz
    }}}
      waiters٠prepare_wait t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspec with "Hwaiters") as "_". 1-3: done || lia.
    wp۰apply+ (waiter٠prepare_waitｰspec with "H𝑤𝑎𝑖𝑡𝑒𝑟") as "_".

    awp۰apply+ (queue_mpmc_1٠pushｰspec with "Hqueue_inv") without "HΦ".
    iInv "Hinv" as "(:inv۰inner)".
    iAaccIntro with "Hqueue_model". 1: iSteps. iIntros "Hqueue_model !>".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.

  Lemma waiters٠cancel_waitｰspec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters۰inv t sz
    }}}
      waiters٠cancel_wait t #i
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspec with "Hwaiters") as "_". 1-3: done || lia.
    wp۰apply+ (waiter٠cancel_waitｰspec with "H𝑤𝑎𝑖𝑡𝑒𝑟 HΦ").
  Qed.

  Lemma waiters٠commit_waitｰspec t (sz : nat) i :
    (0 ≤ i < sz)%Z →
    {{{
      waiters۰inv t sz
    }}}
      waiters٠commit_wait t #i
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Hi %Φ (:inv) HΦ".

    destruct (lookup_lt_is_Some_2 𝑤𝑎𝑖𝑡𝑒𝑟𝑠 ₊i) as (𝑤𝑎𝑖𝑡𝑒𝑟 & H𝑤𝑎𝑖𝑡𝑒𝑟𝑠_lookup). 1: lia.
    iDestruct (big_sepL_lookup with "H𝑤𝑎𝑖𝑡𝑒𝑟𝑠") as "H𝑤𝑎𝑖𝑡𝑒𝑟". 1: done.

    wp۰rec.
    wp۰apply+ (array٠unsafe_getｰspec with "Hwaiters") as "_". 1-3: done || lia.
    wp۰apply+ (waiter٠commit_waitｰspec with "H𝑤𝑎𝑖𝑡𝑒𝑟 HΦ").
  Qed.
End waiters۰G.

Require zoo_parabs.waiters__opaque.

#[global] Opaque waiters۰inv.
