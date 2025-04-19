From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
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
  Lemma condition_create_diaspec :
    DIASPEC
    {{
      True
    }}
      condition_create ()
    {{ t,
      RET t;
      condition_inv t
    }}.
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
  Lemma condition_wait_diaspec t mtx P :
    DIASPEC
    {{
      condition_inv t ∗
      mutex_inv mtx P ∗
      mutex_locked mtx ∗
      P
    }}
      condition_wait t mtx
    {{
      RET ();
      mutex_locked mtx ∗
      P
    }}.
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
  Lemma condition_notify_diaspec t :
    DIASPEC
    {{
      condition_inv t
    }}
      condition_notify t
    {{
      RET ();
      True
    }}.
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
  #[global] Instance condition_notify_all_diaspec t :
    DIASPEC
    {{
      condition_inv t
    }}
      condition_notify_all t
    {{
      RET ();
      True
    }}.
  Proof.
    iSteps.
  Qed.

  Lemma condition_wait_until_spec' Ψ t mtx pred P :
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
        (if b then True else P) ∗
        Ψ b
      }}}
    }}}
      condition_wait_until t mtx pred
    {{{
      RET ();
      mutex_locked mtx ∗
      Ψ true
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp_rec. wp_pures.
    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply ("Hpred" with "[$]") as ([]) "(Hmutex_locked & HΨ)"; first iSteps.
    iDestruct "HΨ" as "(HP & HΨ)".
    wp_smart_apply (condition_wait_spec _ _ P with "[$]") as "(Hmutex_locked & HP)".
    wp_smart_apply ("HLöb" with "Hmutex_locked HP HΨ HΦ").
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
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp_apply (condition_wait_until_spec' (λ b,
      (if b then P else True) ∗
      Ψ b
    )%I with "[$Hinv $Hmutex_inv $Hmutex_locked $HP $HΨ] HΦ").
    iIntros "{%} !> %Φ (Hmutex_locked & HP & (_ & HΨ)) HΦ".
    wp_apply ("Hpred" with "[$Hmutex_locked $HP $HΨ]") as ([]) ""; iSteps.
  Qed.

  Lemma condition_wait_while_spec' Ψ t mtx pred P :
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
        (if b then P else True) ∗
        Ψ b
      }}}
    }}}
      condition_wait_while t mtx pred
    {{{
      RET ();
      mutex_locked mtx ∗
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp_rec.
    wp_smart_apply (condition_wait_until_spec' (λ b, Ψ (negb b)) _ _ _ P with "[$Hmutex_locked $HP $HΨ]"); last iSteps.
    iFrame "#∗". iIntros "{%} %Φ !> (Hmutex_locked & HP & HΨ) HΦ".
    wp_smart_apply ("Hpred" with "[$]") as ([]) ""; iSteps.
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
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp_apply (condition_wait_while_spec' (λ b,
      (if b then True else P) ∗
      Ψ b
    )%I with "[$Hinv $Hmutex_inv $Hmutex_locked $HP $HΨ] HΦ").
    iIntros "{%} !> %Φ (Hmutex_locked & HP & (_ & HΨ)) HΦ".
    wp_apply ("Hpred" with "[$Hmutex_locked $HP $HΨ]") as ([]) ""; iSteps.
  Qed.
End mutex_G.

#[global] Opaque condition_create.
#[global] Opaque condition_wait.
#[global] Opaque condition_notify.
#[global] Opaque condition_notify_all.
#[global] Opaque condition_wait_until.
#[global] Opaque condition_wait_while.

#[global] Opaque condition_inv.
