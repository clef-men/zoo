From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  mutex
  condition__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types t pred : val.

Section mutex_G.
  Context `{mutex_G : MutexG Σ}.

  Definition condition_inv t : iProp Σ :=
    True.

  #[global] Instance condition_inv_persistent t :
    Persistent (condition_inv t).
  Proof.
    apply _.
  Qed.

  Lemma condition_create_spec :
    {{{
      True
    }}}
      condition_create ()
    {{{ t,
      RET t;
      condition_inv t
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_wait_spec t mtx P :
    {{{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P
    }}}
      condition_wait t mtx
    {{{
      RET ();
      mutex_locked mtx ∗
      P
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_notify_spec t :
    {{{
      condition_inv t
    }}}
      condition_notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_notify_all_spec t :
    {{{
      condition_inv t
    }}}
      condition_notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_wait_until_spec Ψ t mtx pred P :
    {{{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P ∗
      Ψ false ∗
      {{{
        mutex_locked mtx ∗
        P ∗
        Ψ false
      }}}
        pred ()
      {{{ b,
        RET #b;
        mutex_locked mtx ∗
        P ∗
        Ψ b
      }}}
    }}}
      condition_wait_until t mtx pred
    {{{
      RET ();
      mutex_locked mtx ∗
      P ∗
      Ψ true
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hlocked & HP & HΨ & #Hpred) HΦ".
    wp_rec. wp_pures.
    iLöb as "HLöb".
    wp_rec.
    wp_smart_apply ("Hpred" with "[$]") as "%b (Hlocked & HP & HΨ)".
    destruct b; first iSteps.
    wp_smart_apply (condition_wait_spec _ _ P with "[$]") as "(Hlocked & HP)".
    wp_smart_apply ("HLöb" with "Hlocked HP HΨ HΦ").
  Qed.

  Lemma condition_wait_while_spec Ψ t mtx pred P :
    {{{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P ∗
      Ψ true ∗
      {{{
        mutex_locked mtx ∗
        P ∗
        Ψ true
      }}}
        pred ()
      {{{ b,
        RET #b;
        mutex_locked mtx ∗
        P ∗
        Ψ b
      }}}
    }}}
      condition_wait_while t mtx pred
    {{{
      RET ();
      mutex_locked mtx ∗
      P ∗
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hlocked & HP & HΨ & #Hpred) HΦ".
    wp_rec.
    wp_smart_apply (condition_wait_until_spec (λ b, Ψ (negb b)) _ _ _ P with "[$Hlocked $HP $HΨ]"); last iSteps.
    iFrame "#∗". clear. iIntros "%Φ !> (Hlocked & HP & HΨ) HΦ".
    wp_smart_apply ("Hpred" with "[$]") as "%b (Hlocked & HP & HΨ)".
    destruct b; iSteps.
  Qed.
End mutex_G.

#[global] Opaque condition_create.
#[global] Opaque condition_wait.
#[global] Opaque condition_notify.
#[global] Opaque condition_notify_all.
#[global] Opaque condition_wait_until.
#[global] Opaque condition_wait_while.

#[global] Opaque condition_inv.
