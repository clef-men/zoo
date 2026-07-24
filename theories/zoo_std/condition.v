Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.mutex.
Require Export zoo_std.condition__code.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type t pred : val.

Section mutex۰G.
  Context `{mutex۰G : MutexG Σ}.

  Definition condition۰inv t : iProp Σ :=
    True.

  #[global] Instance condition۰inv𑁒persistent t :
    Persistent (condition۰inv t).
  Proof.
    apply _.
  Qed.

  Lemma condition٠create𑁒spec :
    {{{
      True
    }}}
      condition٠create ()
    {{{
      t
    , RET t;
      condition۰inv t
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma condition٠create𑁒diaspec :
    DIASPEC
    {{
      True
    }}
      condition٠create ()
    {{ t,
      RET t;
      condition۰inv t
    }}.
  Proof.
    iSteps.
  Qed.

  Lemma condition٠notify𑁒spec t :
    {{{
      condition۰inv t
    }}}
      condition٠notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma condition٠notify𑁒diaspec t :
    DIASPEC
    {{
      condition۰inv t
    }}
      condition٠notify t
    {{
      RET ();
      True
    }}.
  Proof.
    iSteps.
  Qed.

  Lemma condition٠notify_all𑁒spec t :
    {{{
      condition۰inv t
    }}}
      condition٠notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.
  #[global] Instance condition٠notify_all𑁒diaspec t :
    DIASPEC
    {{
      condition۰inv t
    }}
      condition٠notify_all t
    {{
      RET ();
      True
    }}.
  Proof.
    iSteps.
  Qed.

  Lemma condition٠wait𑁒spec t mtx P :
    {{{
      condition۰inv t ∗
      mutex۰inv mtx P ∗
      mutex۰locked mtx ∗
      P
    }}}
      condition٠wait t mtx
    {{{
      RET ();
      mutex۰locked mtx ∗
      P
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma condition٠wait𑁒diaspec t mtx P :
    DIASPEC
    {{
      condition۰inv t ∗
      mutex۰inv mtx P ∗
      mutex۰locked mtx ∗
      P
    }}
      condition٠wait t mtx
    {{
      RET ();
      mutex۰locked mtx ∗
      P
    }}.
  Proof.
    iSteps.
  Qed.

  Lemma condition٠wait_until𑁒spec' Ψ t mtx pred P :
    {{{
      condition۰inv t ∗
      mutex۰inv mtx P ∗
      mutex۰locked mtx ∗
      P ∗
      Ψ false ∗
      □ (
        mutex۰locked mtx -∗
        P -∗
        Ψ false -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          mutex۰locked mtx ∗
          (if b then True else P) ∗
          Ψ b
        }}
      )
    }}}
      condition٠wait_until t mtx pred
    {{{
      RET ();
      mutex۰locked mtx ∗
      Ψ true
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰apply (wp𑁒wand with "(Hpred Hmutex_locked HP HΨ)") as (res) "(%b & -> & Hmutex_locked & HΨ)".
    destruct b; first iSteps.
    iDestruct "HΨ" as "(HP & HΨ)".
    wp۰apply+ (condition٠wait𑁒spec _ _ P with "[$]") as "(Hmutex_locked & HP)".
    wp۰apply+ ("HLöb" with "Hmutex_locked HP HΨ HΦ").
  Qed.
  Lemma condition٠wait_until𑁒spec Ψ t mtx pred P :
    {{{
      condition۰inv t ∗
      mutex۰inv mtx P ∗
      mutex۰locked mtx ∗
      P ∗
      Ψ false ∗
      □ (
        mutex۰locked mtx -∗
        P -∗
        Ψ false -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          mutex۰locked mtx ∗
          P ∗
          Ψ b
        }}
      )
    }}}
      condition٠wait_until t mtx pred
    {{{
      RET ();
      mutex۰locked mtx ∗
      P ∗
      Ψ true
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp۰apply (condition٠wait_until𑁒spec' (λ b,
      (if b then P else True) ∗
      Ψ b
    )%I with "[$Hinv $Hmutex_inv $Hmutex_locked $HP $HΨ] HΦ").
    iSteps. case_match; iSteps.
  Qed.

  Lemma condition٠wait_while𑁒spec' Ψ t mtx pred P :
    {{{
      condition۰inv t ∗
      mutex۰inv mtx P ∗
      mutex۰locked mtx ∗
      P ∗
      Ψ true ∗
      □ (
        mutex۰locked mtx -∗
        P -∗
        Ψ true -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          mutex۰locked mtx ∗
          (if b then P else True) ∗
          Ψ b
        }}
      )
    }}}
      condition٠wait_while t mtx pred
    {{{
      RET ();
      mutex۰locked mtx ∗
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp۰rec.
    wp۰apply+ (condition٠wait_until𑁒spec' (λ b, Ψ (￢ b)) _ _ _ P with "[$Hmutex_locked $HP $HΨ]"); last iSteps.
    iSteps. case_match; iSteps.
  Qed.
  Lemma condition٠wait_while𑁒spec Ψ t mtx pred P :
    {{{
      condition۰inv t ∗
      mutex۰inv mtx P ∗
      mutex۰locked mtx ∗
      P ∗
      Ψ true ∗
      □ (
        mutex۰locked mtx -∗
        P -∗
        Ψ true -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          mutex۰locked mtx ∗
          P ∗
          Ψ b
        }}
      )
    }}}
      condition٠wait_while t mtx pred
    {{{
      RET ();
      mutex۰locked mtx ∗
      P ∗
      Ψ false
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hmutex_inv & Hmutex_locked & HP & HΨ & #Hpred) HΦ".

    wp۰apply (condition٠wait_while𑁒spec' (λ b,
      (if b then True else P) ∗
      Ψ b
    )%I with "[$Hinv $Hmutex_inv $Hmutex_locked $HP $HΨ] HΦ").
    iSteps. case_match; iSteps.
  Qed.
End mutex۰G.

Require zoo_std.condition__opaque.

#[global] Opaque condition۰inv.
