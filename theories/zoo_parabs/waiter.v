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

Definition waiter_Σ :=
  #[mutex_Σ
  ].
#[global] Instance subG_ws_hub_Σ Σ `{zoo_G : !ZooG Σ} :
  subG waiter_Σ Σ →
  WaiterG Σ.
Proof.
  solve_inG.
Qed.

Section waiter_G.
  Context `{waiter_G : WaiterG Σ}.

  #[local] Definition inv_inner 𝑡 : iProp Σ :=
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
    mutex_inv mtx (inv_inner 𝑡) ∗
    𝑡.[condition] ↦□ cond ∗
    condition_inv cond.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡
      & %mtx
      & %cond
      & ->
      & #H𝑡_mutex
      & #Hmtx_inv
      & #H𝑡_condition
      & #Hcond_inv
      )
    ".

  #[global] Instance waiter_inv_persistent t :
    Persistent (waiter_inv t).
  Proof.
    apply _.
  Qed.

  Lemma waiter_create𑁒spec :
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
    wp_apply (condition_create𑁒spec with "[//]") as "%cond #Hcond_inv".
    wp_apply (mutex_create𑁒spec_init with "[//]") as "%mtx Hmtx_init".
    wp_block 𝑡 as "(H𝑡_mutex & H𝑡_condition & H𝑡_flag & _)".

    iMod (mutex_init_to_inv (inv_inner 𝑡) with "Hmtx_init [$H𝑡_flag]").
    iSteps.
  Qed.

  Lemma waiter_notify𑁒spec t :
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

    wp_rec. wp_load.
    wp_apply (mutex_lock𑁒spec with "Hmtx_inv") as "(Hmtx_locked & (:inv_inner))".
    wp_load.
    destruct b; wp_pures.

    - wp_load.
      wp_apply (mutex_unlock𑁒spec with "[$Hmtx_inv $Hmtx_locked $H𝑡_flag]").
      iSteps.

    - wp_bind (_ <-{flag} _)%E.
      wp_store. wp_load.
      wp_apply (mutex_unlock𑁒spec with "[$Hmtx_inv $Hmtx_locked $H𝑡_flag]").
      iSteps.
  Qed.

  Lemma waiter_prepare_wait𑁒spec t :
    {{{
      waiter_inv t
    }}}
      waiter_prepare_wait t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect𑁒spec itype_unit with "[$Hmtx_inv]"). 1: iSteps.
    iSteps.
  Qed.

  Lemma waiter_cancel_wait𑁒spec t :
    {{{
      waiter_inv t
    }}}
      waiter_cancel_wait t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect𑁒spec itype_bool with "[$Hmtx_inv]"). 2: iSteps.
    { iIntros "Hmtx_locked (:inv_inner)".
      wp_load.
      destruct b; iSteps.
    }
  Qed.

  Lemma waiter_commit_wait𑁒spec t :
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

    wp_rec. wp_load.
    wp_apply (mutex_protect𑁒spec itype_unit with "[$Hmtx_inv]"). 2: iSteps.
    iIntros "Hmtx_locked (:inv_inner)".
    do 2 wp_load.
    wp_apply (condition_wait_until𑁒spec (λ _, True)%I with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $H𝑡_flag]"). 1: iSteps.
    iSteps.
  Qed.
End waiter_G.

From zoo_parabs Require
  waiter__opaque.

#[global] Opaque waiter_inv.
