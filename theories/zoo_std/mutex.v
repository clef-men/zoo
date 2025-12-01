From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  excl.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  mutex__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types t fn : val.

Class MutexG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mutex_G :: ExclG Σ unitO ;
}.

Definition mutex_Σ := #[
  excl_Σ unitO
].
#[global] Instance subG_mutex_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mutex_Σ Σ →
  MutexG Σ.
Proof.
  solve_inG.
Qed.

Section mutex_G.
  Context `{mutex_G : MutexG Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

  #[local] Definition locked γ :=
    excl γ ().

  Definition mutex_init t b : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l ↦ᵣ #b ∗
    if b then True else locked γ.

  #[local] Definition inv_inner l γ P : iProp Σ :=
    ∃ b,
    l ↦ᵣ #b ∗
    match b with
    | true =>
        True
    | false =>
        locked γ ∗
        P
    end.
  Definition mutex_inv t P : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv nroot (inv_inner l γ P).

  Definition mutex_locked t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    locked γ.

  #[global] Instance mutex_inv_contractive t :
    Contractive (mutex_inv t).
  Proof.
    rewrite /mutex_inv /inv_inner.
    solve_contractive.
  Qed.
  #[global] Instance mutex_inv_ne t :
    NonExpansive (mutex_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex_inv_proper t :
    Proper ((≡) ==> (≡)) (mutex_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mutex_init_timeless t b :
    Timeless (mutex_init t b).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex_locked_timeless t :
    Timeless (mutex_locked t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mutex_inv_persistent t P :
    Persistent (mutex_inv t P).
  Proof.
    apply _.
  Qed.

  Lemma mutex_init_exclusive t b1 b2 :
    mutex_init t b1 -∗
    mutex_init t b2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma mutex_init_to_inv {t b} P E :
    mutex_init t b -∗
    (if b then True else ▷ P) ={E}=∗
    mutex_inv t P.
  Proof.
    destruct b; iSteps.
  Qed.

  Lemma mutex_locked_exclusive t :
    mutex_locked t -∗
    mutex_locked t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hlocked1) (%_l & %_γ & %Heq & _Hmeta & Hlocked2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (excl_exclusive with "Hlocked1 Hlocked2") as %[].
  Qed.

  Lemma mutex_create_spec_init :
    {{{
      True
    }}}
      mutex_create ()
    {{{ t,
      RET t;
      mutex_init t false
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    wp_rec.
    wp_ref l as "Hmeta" "Hl".

    iMod excl_alloc as "(%γ & Hlocked)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.
  Lemma mutex_create_spec P :
    {{{
      P
    }}}
      mutex_create ()
    {{{ t,
      RET t;
      mutex_inv t P
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    iApply wp_fupd.
    wp_apply (mutex_create_spec_init with "[//]") as (t) "Hinit".
    iMod (mutex_init_to_inv with "Hinit HP") as "Hinv".
    iApply ("HΦ" with "Hinv").
  Qed.

  Lemma mutex_create_lock_spec_init :
    {{{
      True
    }}}
      mutex_create_lock ()
    {{{ t,
      RET t;
      mutex_init t true ∗
      mutex_locked t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_ref l as "Hmeta" "Hl".

    iMod excl_alloc as "(%γ & Hlocked)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.
  Lemma mutex_create_lock_spec P :
    {{{
      True
    }}}
      mutex_create_lock ()
    {{{ t,
      RET t;
      mutex_inv t P ∗
      mutex_locked t
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    iApply wp_fupd.
    wp_apply (mutex_create_lock_spec_init with "[//]") as (t) "(Hinit & Hlocked)".
    iMod (mutex_init_to_inv P with "Hinit [//]") as "Hinv".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma mutex_lock_spec t P :
    {{{
      mutex_inv t P
    }}}
      mutex_lock t
    {{{
      RET ();
      mutex_locked t ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%b & Hl & Hb)".
    destruct b; last iSteps.
    wp_cas as _ | [=].
    iSplitR "HΦ"; first iSteps.
    iModIntro.

    wp_pures.
    iApply ("HLöb" with "HΦ").
  Qed.
  Lemma mutex_lock_spec_init t :
    {{{
      mutex_init t false
    }}}
      mutex_lock t
    {{{
      RET ();
      mutex_init t true ∗
      mutex_locked t
    }}}.
  Proof.
    rewrite /mutex_lock. iSteps.
  Qed.

  Lemma mutex_unlock_spec t P :
    {{{
      mutex_inv t P ∗
      mutex_locked t ∗
      P
    }}}
      mutex_unlock t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %Heq & #_Hmeta & Hlocked) & HP) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    iSteps.
  Qed.
  Lemma mutex_unlock_spec_init t :
    {{{
      mutex_init t true ∗
      mutex_locked t
    }}}
      mutex_unlock t
    {{{
      RET ();
      mutex_init t false
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma mutex_synchronize_spec t P :
    {{{
      mutex_inv t P
    }}}
      mutex_synchronize t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_apply (mutex_lock_spec with "Hinv") as "(Hlocked & HP)".
    wp_smart_apply (mutex_unlock_spec with "[$Hinv $Hlocked $HP] HΦ").
  Qed.
  #[global] Instance mutex_synchronize_diaspec t P :
    DIASPEC
    {{
      mutex_inv t P
    }}
      mutex_synchronize t
    {{
      RET ();
      True
    }}.
  Proof.
    iStep.
    iApply mutex_synchronize_spec.
  Qed.

  Lemma mutex_protect_spec Ψ t P fn :
    {{{
      mutex_inv t P ∗
      ( mutex_locked t -∗
        P -∗
        WP fn () {{ v,
          mutex_locked t ∗
          P ∗
          Ψ v
        }}
      )
    }}}
      mutex_protect t fn
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hfn) HΦ".

    wp_rec.
    wp_smart_apply (mutex_lock_spec with "Hinv") as "(Hlocked & HP)".
    wp_smart_apply (wp_wand with "(Hfn Hlocked HP)") as "%v (Hlocked & HP & HΨ)".
    wp_smart_apply (mutex_unlock_spec with "[$Hinv $Hlocked $HP]").
    iSteps.
  Qed.
End mutex_G.

From zoo_std Require
  mutex__opaque.

#[global] Opaque mutex_init.
#[global] Opaque mutex_inv.
#[global] Opaque mutex_locked.
