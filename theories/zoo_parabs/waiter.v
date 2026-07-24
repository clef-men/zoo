Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.condition.
Require Import zoo_std.mutex.
Require Import zoo_saturn.mpmc_queue_1.
Require Export zoo_parabs.base.
Require Export zoo_parabs.waiter__code.
Require Import zoo_parabs.base.
Require Import zoo_parabs.waiter__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type 𝑡 : location.
Implicit Type v t mtx cond : val.

Class WaiterG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] waiter۰G۰mutex۰G :: MutexG Σ
  }.

Definition waiter۰Σ :=
  #[mutex۰Σ
  ].
#[global] Instance subG𑁒ws_hub_Σ Σ `{zoo۰G : !ZooG Σ} :
  subG waiter۰Σ Σ →
  WaiterG Σ.
Proof.
  solve_inG.
Qed.

Section waiter۰G.
  Context `{waiter۰G : WaiterG Σ}.

  #[local] Definition inv۰inner 𝑡 : iProp Σ :=
    ∃ b,
    𝑡.[flag] ↦ #b.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %b
      & H𝑡_flag
      )
    ".
  Definition waiter۰inv t : iProp Σ :=
    ∃ 𝑡 mtx cond,
    ⌜t = #𝑡⌝ ∗
    𝑡.[mutex] ↦□ mtx ∗
    mutex۰inv mtx (inv۰inner 𝑡) ∗
    𝑡.[condition] ↦□ cond ∗
    condition۰inv cond.
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

  #[global] Instance waiter۰inv𑁒persistent t :
    Persistent (waiter۰inv t).
  Proof.
    apply _.
  Qed.

  Lemma waiter٠create𑁒spec :
    {{{
      True
    }}}
      waiter٠create ()
    {{{
      t
    , RET t;
      waiter۰inv t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply (condition٠create𑁒spec with "[//]") as "%cond #Hcond_inv".
    wp۰apply (mutex٠create𑁒spec𑁒init with "[//]") as "%mtx Hmtx_init".
    wp۰block 𝑡 as "(H𝑡_mutex & H𝑡_condition & H𝑡_flag & _)".

    iMod (mutex۰init𑁒to𑁒inv (inv۰inner 𝑡) with "Hmtx_init [$H𝑡_flag]").
    iSteps.
  Qed.

  Lemma waiter٠notify𑁒spec t :
    {{{
      waiter۰inv t
    }}}
      waiter٠notify t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠lock𑁒spec with "Hmtx_inv") as "(Hmtx_locked & (:inv۰inner))".
    wp۰load.
    destruct b; wp۰pures.

    - wp۰load.
      wp۰apply (mutex٠unlock𑁒spec with "[$Hmtx_inv $Hmtx_locked $H𝑡_flag]").
      iSteps.

    - wp۰bind (_ <-{flag} _)%E.
      wp۰store. wp۰load.
      wp۰apply (mutex٠unlock𑁒spec with "[$Hmtx_inv $Hmtx_locked $H𝑡_flag]").
      iSteps.
  Qed.

  Lemma waiter٠prepare_wait𑁒spec t :
    {{{
      waiter۰inv t
    }}}
      waiter٠prepare_wait t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protect𑁒spec itype۰unit with "[$Hmtx_inv]"). 1: iSteps.
    iSteps.
  Qed.

  Lemma waiter٠cancel_wait𑁒spec t :
    {{{
      waiter۰inv t
    }}}
      waiter٠cancel_wait t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protect𑁒spec itype۰bool with "[$Hmtx_inv]"). 2: iSteps.
    { iIntros "Hmtx_locked (:inv۰inner)".
      wp۰load.
      destruct b; iSteps.
    }
  Qed.

  Lemma waiter٠commit_wait𑁒spec t :
    {{{
      waiter۰inv t
    }}}
      waiter٠commit_wait t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protect𑁒spec itype۰unit with "[$Hmtx_inv]"). 2: iSteps.
    iIntros "Hmtx_locked (:inv۰inner)".
    do 2 wp۰load.
    wp۰apply (condition٠wait_until𑁒spec (λ _, True)%I with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $H𝑡_flag]"). 1: iSteps.
    iSteps.
  Qed.
End waiter۰G.

Require zoo_parabs.waiter__opaque.

#[global] Opaque waiter۰inv.
